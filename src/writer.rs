use std::{fmt, io, mem, ptr, str};

use encoding_rs::Encoder;

use super::{MalformedError, UnmappableError};

const MIN_BUF_SIZE: usize = 32;

/// A writer wrapper that encodes an input byte stream into the specified encoding.
///
/// This wrapper accepts bytes through [`std::io::Write`] methods, encodes them using the specified
/// encoder, and writes the encoded bytes into the underlying writer. Like [`BufWriter`], this type
/// stores the encoded bytes in its internal buffer and writes them into the underlying writer when
/// dropped or when the buffer becomes full.
///
/// This writer reports [`UnmappableError`] when it encounters a character that is not mappable in
/// the destination encoding and [`MalformedError`] when the input byte sequence contains invalid
/// UTF-8 bytes. These errors are non-fatal, and the writer can continue to encode the subsequent
/// bytes by calling any writer methods. See the documentation of [`UnmappableError`] for how to
/// resume while replacing the unmappable characters with the HTML numeric character references.
///
/// To meet the requirements of [`std::io::Write`], this writer often _defers_ an error from one
/// write call to the next. A call to `write` consumes an unmappable character and returns `Ok(n)`,
/// where `n` includes the length of the unmappable character bytes, and the immediately subsequent
/// call to a writer method returns `Err` reporting that unmappable character at the beginning of
/// the procedure. As a result, the writer methods of this writer may return counter-intuitive
/// errors deferred from the previous calls. For example, [`write_str`] can report `MalformedError`
/// even though it only accepts valid `&str`, and the writer type returned by [`passthrough`] can
/// report `UnmappableError` even though it does not transform the input bytes at all.
///
/// This wrapper returns `Ok(0)` when the input passed is empty, but this wrapper does not
/// terminate the internal encoder automatically. Call [`finish`](EncodingWriter::finish)
/// explicitly to let the encoder know the end of the stream, and it will return an error, if any,
/// found at the end of the stream.
///
/// [`BufWriter`]: std::io::BufWriter
/// [`write_str`]: EncodingWriter::write_str
/// [`passthrough`]: EncodingWriter::passthrough
///
/// # Examples
///
/// ```rust
/// use std::io::Write as _;
///
/// use encoding_rs::GB18030;
/// use encoding_rs_rw::EncodingWriter;
///
/// let mut writer = EncodingWriter::new(Vec::new(), GB18030.new_encoder());
///
/// write!(writer, "天坛")?;
/// writer.write_all("公园".as_bytes())?;
/// writer.flush()?;
/// assert_eq!(
///     writer.writer_ref(),
///     &[204, 236, 204, 179, 185, 171, 212, 176]
/// );
/// # Ok::<(), std::io::Error>(())
/// ```
#[derive(Debug)]
pub struct EncodingWriter<W: io::Write> {
    writer: W,
    encoder: super::util::DebuggableEncoder,
    encoded_buf: Vec<u8>,
    /// Storage to carry an error from one write call to the next, used to tentatively return `Ok`
    /// (as per the contract) after consuming erroneous input and report the error at the beginning
    /// of the subsequent call.
    deferred_error: Option<DefErr>,
    writer_panicked: bool,
}

impl<W: io::Write> EncodingWriter<W> {
    /// Creates a new encoding writer from a writer and an encoder.
    pub fn new(writer: W, encoder: Encoder) -> Self {
        // As of Rust 1.73.0: https://github.com/rust-lang/rust/blob/1.73.0/library/std/src/sys_common/io.rs#L3
        const DEFAULT_BUF_SIZE: usize = if cfg!(target_os = "espidf") {
            512
        } else {
            8 * 1024
        };
        Self::with_capacity(DEFAULT_BUF_SIZE, writer, encoder)
    }

    /// Creates a new encoding writer with an internal buffer of at least the specified capacity.
    pub fn with_capacity(capacity: usize, writer: W, encoder: Encoder) -> Self {
        Self {
            writer,
            encoder: encoder.into(),
            encoded_buf: Vec::with_capacity(capacity.max(MIN_BUF_SIZE)),
            deferred_error: None,
            writer_panicked: false,
        }
    }

    /// Returns a reference to the underlying writer.
    pub fn writer_ref(&self) -> &W {
        &self.writer
    }

    /// Returns a reference to the underlying encoder.
    pub fn encoder_ref(&self) -> &Encoder {
        &self.encoder
    }

    /// Notifies the underlying encoder of the end of input stream, dropping it and returning the
    /// underlying writer, the internal buffer content not yet written to the underlying writer,
    /// and any error reported at the end of input byte sequence.
    ///
    /// It is recommended to call `flush` first because this method does not flush the internal
    /// buffer.
    pub fn finish(mut self) -> (W, Vec<u8>, io::Result<()>) {
        self.encoded_buf.reserve(
            self.encoder
                .max_buffer_length_from_utf8_without_replacement(0)
                .unwrap(),
        );
        let (result, _) = self.encoder.encode_from_utf8_to_vec_without_replacement(
            "",
            &mut self.encoded_buf,
            true,
        );

        let deferred_error = match result {
            encoding_rs::EncoderResult::InputEmpty => self.return_any_deferred_error(),
            _ => {
                debug_assert!(false, "unreachable");
                Err(io::Error::new(
                    io::ErrorKind::Other,
                    "failed to finish encoder unexpectedly",
                ))
            }
        };

        // destruct `self`, moving out some fields and dropping the rest
        let (writer, encoded_buf) = unsafe {
            let mut m = mem::ManuallyDrop::new(self);
            ptr::drop_in_place(&mut m.encoder);
            ptr::drop_in_place(&mut m.deferred_error);
            ptr::drop_in_place(&mut m.writer_panicked);
            (ptr::read(&m.writer), ptr::read(&m.encoded_buf))
        };

        (writer, encoded_buf, deferred_error)
    }

    /// Writes a string slice into this writer, returning how many input bytes were consumed.
    ///
    /// This is an equivalent of [`write`](std::io::Write::write) but takes a string slice as the
    /// argument instead of a byte slice, eliminating the UTF-8 validation of the input.
    ///
    /// See the type-level documentation for the error semantics.
    ///
    /// This method is a low-level call primarily meant for a loop handling [`UnmappableError`] in
    /// a desired manner. See the `UnmappableError` documentation for usage examples. Where
    /// `UnmappableError` is unlikely or is not to be recovered, [`std::write!`] macro is the
    /// primary option because `write_fmt` under the hood also skips the UTF-8 validation.
    pub fn write_str(&mut self, buf: &str) -> io::Result<usize> {
        if buf.is_empty() {
            // `io::Write` may return `Ok(0)` if input buffer is 0 bytes in length
            return Ok(0);
        }
        self.return_any_deferred_error()?;
        self.reserve_buffer_capacity(MIN_BUF_SIZE)?;
        Ok(self.write_str_inner(buf))
    }

    /// Returns a new writer that writes encoded bytes into this encoding writer, bypassing the
    /// underlying encoder.
    ///
    /// The caller must ensure that the bytes written are a valid byte sequence in the destination
    /// encoding, as this writer does not validate or transform the input byte sequence.
    ///
    /// See the type-level documentation for the error semantics of the writer methods provided by
    /// the returned writer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::io::Write as _;
    ///
    /// use encoding_rs::ISO_8859_2;
    /// use encoding_rs_rw::EncodingWriter;
    ///
    /// let mut writer = EncodingWriter::new(Vec::new(), ISO_8859_2.new_encoder());
    /// // ASCII bytes are valid as ISO/IEC 8859-2 (a.k.a. Latin-2), too.
    /// write!(writer.passthrough(), r"\U{:08X}", u32::from('😂'))?;
    /// writer.flush()?;
    /// assert_eq!(writer.writer_ref(), br"\U0001F602");
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn passthrough(&mut self) -> impl io::Write + '_ {
        PassthroughWriter(self)
    }

    /// Returns a new writer that handles [`UnmappableError`] with the specified handler.
    #[cfg(feature = "unstable")]
    #[cfg_attr(docsrs, doc(cfg(feature = "unstable")))]
    pub fn with_unmappable_handler<'a>(
        &'a mut self,
        handler: impl FnMut(char, &mut PassthroughWriter<W>) -> io::Result<()> + 'a,
    ) -> impl io::Write + 'a {
        struct WithUnmappableHandlerWriter<'a, W: io::Write, H>(&'a mut EncodingWriter<W>, H);

        impl<W: io::Write, H> WithUnmappableHandlerWriter<'_, W, H>
        where
            H: FnMut(char, &mut PassthroughWriter<W>) -> io::Result<()>,
        {
            fn handle_any_unmappable_error(&mut self) -> io::Result<()> {
                if matches!(self.0.deferred_error, Some(DefErr::Unmappable(..))) {
                    let value = match self.0.deferred_error.take() {
                        Some(DefErr::Unmappable(e)) => e.value(),
                        _ => unreachable!(),
                    };
                    (self.1)(value, &mut PassthroughWriter(self.0))?;
                }
                Ok(())
            }
        }

        impl<W: io::Write, H> WriteFmtAdapter for WithUnmappableHandlerWriter<'_, W, H>
        where
            H: FnMut(char, &mut PassthroughWriter<W>) -> io::Result<()>,
        {
            fn write_str_io(&mut self, buf: &str) -> io::Result<usize> {
                if buf.is_empty() {
                    return Ok(0);
                }
                self.handle_any_unmappable_error()?;
                self.0.return_any_deferred_error()?;
                self.0.reserve_buffer_capacity(MIN_BUF_SIZE)?;
                Ok(self.0.write_str_inner(buf))
            }
        }

        impl<W: io::Write, H> io::Write for WithUnmappableHandlerWriter<'_, W, H>
        where
            H: FnMut(char, &mut PassthroughWriter<W>) -> io::Result<()>,
        {
            fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
                if buf.is_empty() {
                    return Ok(0);
                }
                self.handle_any_unmappable_error()?;
                self.0.write(buf)
            }

            fn flush(&mut self) -> io::Result<()> {
                self.0.flush()
            }

            fn write_fmt(&mut self, f: fmt::Arguments<'_>) -> io::Result<()> {
                write_fmt_impl(self, f)
            }
        }

        WithUnmappableHandlerWriter(self, handler)
    }

    fn write_str_inner(&mut self, buf: &str) -> usize {
        debug_assert!(!buf.is_empty());
        debug_assert!(self.deferred_error.is_none());
        debug_assert!(self.encoded_buf.capacity() - self.encoded_buf.len() >= MIN_BUF_SIZE);

        let (result, consumed) = self.encoder.encode_from_utf8_to_vec_without_replacement(
            buf,
            &mut self.encoded_buf,
            false,
        );
        debug_assert_ne!(consumed, 0);
        debug_assert!(buf.is_char_boundary(consumed), "encoder broke contract");

        if let encoding_rs::EncoderResult::Unmappable(c) = result {
            // defer error until subsequent call because some bytes were consumed successfully
            self.deferred_error = Some(DefErr::Unmappable(UnmappableError::new(c)));
        }

        consumed
    }

    /// Consumes `self.deferred_error` and reports the corresponding `io::Error` (if applicable).
    fn return_any_deferred_error(&mut self) -> io::Result<()> {
        match self.deferred_error.take() {
            None => Ok(()),
            Some(DefErr::Unmappable(e)) => Err(e.wrap()),
            Some(DefErr::MalformedUtf8(e)) => Err(e.wrap()),
            // IncompleteUtf8 represents MalformedError before writing another &str or at EOF,
            // whereas this state can be recovered when writing &[u8] containing the subsequent
            // UTF-8 character fragment.
            Some(DefErr::IncompleteUtf8(..)) => Err(MalformedError::new().wrap()),
        }
    }

    fn reserve_buffer_capacity(&mut self, additional: usize) -> io::Result<()> {
        if self.encoded_buf.capacity() - self.encoded_buf.len() < additional {
            self.flush_buffer()?;
        }
        debug_assert!(
            self.encoded_buf.capacity() - self.encoded_buf.len() >= additional
                || self.encoded_buf.is_empty()
        );
        Ok(())
    }

    /// Writes the buffered data into the underlying writer.
    fn flush_buffer(&mut self) -> io::Result<()> {
        // A guard struct to make sure to remove consumed bytes from the buffer when dropped.
        struct PanicGuard<'a> {
            consumed: usize,
            buffer: &'a mut Vec<u8>,
        }

        impl Drop for PanicGuard<'_> {
            fn drop(&mut self) {
                if self.consumed < self.buffer.len() {
                    self.buffer.drain(..self.consumed);
                } else {
                    self.buffer.clear();
                }
            }
        }

        let mut g = PanicGuard {
            consumed: 0,
            buffer: &mut self.encoded_buf,
        };

        while g.consumed < g.buffer.len() {
            self.writer_panicked = true;
            let ret = self.writer.write(&g.buffer[g.consumed..]);
            self.writer_panicked = false;

            match ret {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write buffered data to underlying writer",
                    ));
                }
                Ok(n) => g.consumed += n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

impl<W: io::Write> WriteFmtAdapter for EncodingWriter<W> {
    fn write_str_io(&mut self, buf: &str) -> io::Result<usize> {
        self.write_str(buf)
    }
}

impl<W: io::Write> io::Write for EncodingWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            // `io::Write` may return `Ok(0)` if input buffer is 0 bytes in length
            return Ok(0);
        } else if !matches!(self.deferred_error, Some(DefErr::IncompleteUtf8(..))) {
            // recover from IncompleteUtf8 later; otherwise, report any deferred error
            self.return_any_deferred_error()?;
        }
        self.reserve_buffer_capacity(MIN_BUF_SIZE)?;

        Ok(match self.deferred_error.take() {
            None => match str_from_utf8_up_to_error(buf) {
                // encode `buf` if it starts with valid UTF-8 of at least one byte in length
                //
                // This path doesn't consume any invalid bytes following the valid sequence because
                // it's not sure if `write_str_inner` encodes the entire argument. Accordingly, the
                // other match arms consume invalid UTF-8 bytes only and defer error state until a
                // subsequent call.
                Ok(s) => self.write_str_inner(s),
                // consume invalid bytes and defer MalformedError until subsequent call
                Err(Some(error_len)) => {
                    self.deferred_error = Some(DefErr::MalformedUtf8(MalformedError::new()));
                    error_len
                }
                // consume and save incomplete character fragment, waiting for the following bytes
                Err(None) => {
                    let mut bs = super::util::MiniBuffer::default();
                    let len = bs.fill_from_slice(buf);
                    debug_assert!(len == bs.len());
                    assert!(len < 4 && len == buf.len());
                    self.deferred_error = Some(DefErr::IncompleteUtf8(bs));
                    len
                }
            },
            Some(DefErr::Unmappable(..)) => unreachable!(),
            Some(DefErr::MalformedUtf8(..)) => unreachable!(),
            Some(DefErr::IncompleteUtf8(mut bs)) => {
                let old_len = bs.len();
                let new_len = old_len + bs.fill_from_slice(buf);
                debug_assert!(old_len < new_len && new_len == bs.len());
                let consumed = match str_from_utf8_up_to_error(bs.as_ref()) {
                    Ok(s) => self.write_str_inner(s),
                    Err(Some(error_len)) => {
                        self.deferred_error = Some(DefErr::MalformedUtf8(MalformedError::new()));
                        error_len
                    }
                    Err(None) => {
                        assert!(new_len < 4 && new_len == old_len + buf.len());
                        self.deferred_error = Some(DefErr::IncompleteUtf8(bs));
                        new_len
                    }
                };
                assert!(old_len < consumed);
                consumed - old_len
            }
        })
    }

    fn flush(&mut self) -> io::Result<()> {
        self.return_any_deferred_error()?;
        self.flush_buffer()?;
        self.writer.flush()
    }

    fn write_fmt(&mut self, f: fmt::Arguments<'_>) -> io::Result<()> {
        write_fmt_impl(self, f)
    }
}

impl<W: io::Write> Drop for EncodingWriter<W> {
    fn drop(&mut self) {
        // don't double-flush the buffer when the inner writer panicked in a call to write
        if !self.writer_panicked {
            let _ = self.flush_buffer();
        }
    }
}

#[derive(Debug)]
enum DefErr {
    Unmappable(UnmappableError),
    MalformedUtf8(MalformedError),
    IncompleteUtf8(super::util::MiniBuffer),
}

fn str_from_utf8_up_to_error(v: &[u8]) -> Result<&str, Option<usize>> {
    match str::from_utf8(v) {
        Ok(s) => Ok(s),
        Err(e) if e.valid_up_to() > 0 => {
            Ok(unsafe { str::from_utf8_unchecked(&v[..e.valid_up_to()]) })
        }
        Err(e) => Err(e.error_len()),
    }
}

/// The writer type returned by [`EncodingWriter::passthrough`].
#[derive(Debug)]
pub struct PassthroughWriter<'a, W: io::Write>(&'a mut EncodingWriter<W>);

impl<W: io::Write> io::Write for PassthroughWriter<'_, W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            // `io::Write` may return `Ok(0)` if input buffer is 0 bytes in length
            return Ok(0);
        }
        self.0.return_any_deferred_error()?;
        self.0.reserve_buffer_capacity(buf.len())?;

        if buf.len() > self.0.encoded_buf.capacity() {
            // bypass internal buffer if input buffer is large
            assert!(self.0.encoded_buf.is_empty());
            self.0.writer_panicked = true;
            let ret = self.0.writer.write(buf);
            self.0.writer_panicked = false;
            ret
        } else {
            let old_len = self.0.encoded_buf.len();
            let new_len = old_len + buf.len();
            assert!(new_len <= self.0.encoded_buf.capacity());
            // SAFETY: ok because copy_from_slice overwrites uninitialized area
            unsafe {
                self.0.encoded_buf.set_len(new_len);
                self.0.encoded_buf[old_len..].copy_from_slice(buf);
            }
            Ok(buf.len())
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

trait WriteFmtAdapter {
    /// Writes a string slice just like [`std::fmt::Write::write_str`] but returns a result just
    /// like [`std::io::Write::write`].
    fn write_str_io(&mut self, buf: &str) -> io::Result<usize>;
}

/// Implements [`std::io::Write::write_fmt`].
///
/// This function essentially combines the default `write_all` and `write_fmt` implementations of
/// `std::io::Write`, while using `write_str` to eliminate the UTF-8 validation.
fn write_fmt_impl(writer: &mut impl WriteFmtAdapter, f: fmt::Arguments<'_>) -> io::Result<()> {
    struct FmtWriter<'a, T> {
        inner: &'a mut T,
        io_error: io::Result<()>,
    }

    impl<T: WriteFmtAdapter> fmt::Write for FmtWriter<'_, T> {
        fn write_str(&mut self, mut s: &str) -> fmt::Result {
            while !s.is_empty() {
                match self.inner.write_str_io(s) {
                    Ok(0) => {
                        self.io_error = Err(io::Error::new(
                            io::ErrorKind::WriteZero,
                            "failed to write whole buffer",
                        ));
                        return Err(fmt::Error);
                    }
                    Ok(n) => {
                        s = match s.get(n..) {
                            Some(t) => t,
                            None => {
                                debug_assert!(false, "unreachable");
                                self.io_error = Err(io::Error::new(
                                    io::ErrorKind::Other,
                                    "encoder returned invalid string index",
                                ));
                                return Err(fmt::Error);
                            }
                        }
                    }
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                    Err(e) => {
                        self.io_error = Err(e);
                        return Err(fmt::Error);
                    }
                }
            }
            Ok(())
        }
    }

    let mut output = FmtWriter {
        inner: writer,
        io_error: Ok(()),
    };
    match fmt::write(&mut output, f) {
        Ok(_) => Ok(()),
        Err(_) => {
            if output.io_error.is_err() {
                output.io_error
            } else {
                Err(io::Error::new(io::ErrorKind::Other, "formatter error"))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Write;

    use super::{EncodingWriter, MalformedError, UnmappableError};

    /// Tests rare cases where `finish` reports `Err` after `write` returned `Ok(0)`.
    #[test]
    fn trailing_unmappable_char() {
        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::SHIFT_JIS.new_encoder());
        assert!(matches!(writer.write_all("Oh🥺".as_bytes()), Ok(())));
        match writer.finish() {
            (writer, buffer, Err(e)) => {
                assert_eq!(writer, &[]);
                assert_eq!(buffer, &[b'O', b'h']);
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
            }
            ret => panic!("assertion failed: {:?}", ret),
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::EUC_JP.new_encoder());
        assert!(matches!(writer.write_all("Oh🥺".as_bytes()), Ok(())));
        assert!(matches!(writer.write_all(&[]), Ok(())));
        assert!(matches!(writer.write_all(&[]), Ok(())));
        assert!(matches!(writer.write(&[]), Ok(0)));
        assert!(matches!(writer.write(&[]), Ok(0)));
        match writer.flush() {
            Err(e) => {
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
            }
            ret => panic!("assertion failed: {:?}", ret),
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::EUC_KR.new_encoder());
        assert!(matches!(write!(writer, "Oh🥺"), Ok(())));
        match writer.finish() {
            (writer, buffer, Err(e)) => {
                assert_eq!(writer, &[]);
                assert_eq!(buffer, &[b'O', b'h']);
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
            }
            ret => panic!("assertion failed: {:?}", ret),
        };
    }

    /// Tests invalid and incomplete UTF-8 bytes supplied to the writer.
    #[test]
    fn malformed_utf8() {
        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_2.new_encoder());
        let src = [b'A', b'B', 0x80, 0x9f, b'C', b'D'];
        assert!(matches!(writer.write(&src[0..]), Ok(2)));
        assert!(matches!(writer.write(&src[2..]), Ok(1)));
        assert!(match writer.write(&src[3..]) {
            Err(e) => MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });
        assert!(matches!(writer.write(&src[3..]), Ok(1)));
        assert!(match writer.write(&src[4..]) {
            Err(e) => MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });
        assert!(matches!(writer.write(&src[4..]), Ok(2)));

        assert!(matches!(writer.write(&[0xc3]), Ok(1)));
        assert!(matches!(writer.write(&[0x97]), Ok(1)));

        assert!(matches!(writer.write(&[0xc3]), Ok(1)));
        assert!(matches!(writer.write(&[]), Ok(0)));
        assert!(matches!(writer.write_str(""), Ok(0)));
        assert!(matches!(writer.passthrough().write(&[]), Ok(0)));

        match writer.finish() {
            (writer, buffer, Err(e)) => {
                assert_eq!(writer, &[]);
                assert_eq!(buffer, &[b'A', b'B', b'C', b'D', 0xd7]);
                assert!(MalformedError::wrapped_in(&e).is_some());
            }
            ret => panic!("assertion failed: {:?}", ret),
        }

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_3.new_encoder());
        assert!(matches!(writer.write(&[0xc3]), Ok(1)));
        assert!(match writer.write_str("A") {
            Err(e) => MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_4.new_encoder());
        assert!(matches!(writer.write(&[0xc3]), Ok(1)));
        assert!(match writer.passthrough().write(&[0xd7]) {
            Err(e) => MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_7.new_encoder());
        assert!(matches!(writer.write(&[0xc3]), Ok(1)));
        assert!(match writer.flush() {
            Err(e) => MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });

        #[cfg(feature = "unstable")]
        {
            let mut writer =
                EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_15.new_encoder());
            assert!(matches!(
                writer
                    .with_unmappable_handler(|_, _| unreachable!())
                    .write(&[0xc3]),
                Ok(1)
            ));
            assert!(match writer.flush() {
                Err(e) => MalformedError::wrapped_in(&e).is_some(),
                _ => false,
            });
        }
    }
}
