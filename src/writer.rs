use std::{fmt, io, mem, str};

use encoding_rs::Encoder;

use super::{buffer::DefaultBuffer, util, MalformedError, UnmappableError};

const MIN_BUF_SIZE: usize = 32;

/// A writer wrapper that encodes an input byte stream into the specified encoding.
///
/// This encoding writer accepts bytes through [`std::io::Write`] methods, encodes them using the
/// specified encoder, and writes the encoded bytes into the underlying buffer that implements
/// [`BufferedWrite`]. This wrapper also supports writing into `std::io::Write` writers by fully
/// integrating the [`BufWriter`]-like [`DefaultBuffer`] type. Like `BufWriter`, `DefaultBuffer`
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
/// This deferred error behavior could be particularly tricky if this writer encounters an error at
/// the end of the input stream because it does not return the error at the very moment when the
/// input buffer is _fully consumed_ (i.e., when [`write_all`] or [`write!`] returns `Ok(())` or
/// when the cumulative sum of `Ok(n)` returned by [`write`] indicates the completion). It is
/// recommended to call [`flush`] and [`finish`] at the end of the input to handle such a trailing
/// error explicitly.
///
/// [`BufWriter`]: io::BufWriter
/// [`write_str`]: Self::write_str
/// [`passthrough`]: Self::passthrough
/// [`write_all`]: io::Write::write_all
/// [`write!`]: std::write
/// [`write`]: io::Write::write
/// [`finish`]: Self::finish
/// [`flush`]: io::Write::flush
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
pub struct EncodingWriter<B> {
    buffer: B,
    encoder: util::DebuggableEncoder,
    /// Storage to carry an error from one write call to the next, used to tentatively return `Ok`
    /// (as per the contract) after consuming erroneous input and report the error at the beginning
    /// of the subsequent call.
    deferred_error: Option<DefErr>,
}

impl<W: io::Write> EncodingWriter<DefaultBuffer<W>> {
    /// Creates a new encoding writer from a writer and an encoder.
    ///
    /// This constructor wraps the specified writer with [`DefaultBuffer`], and accordingly, the
    /// encoded bytes are not written to the underlying writer until the buffer becomes full.
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
    ///
    /// This constructor wraps the specified writer with [`DefaultBuffer`], and accordingly, the
    /// encoded bytes are not written to the underlying writer until the buffer becomes full.
    pub fn with_capacity(capacity: usize, writer: W, encoder: Encoder) -> Self {
        let c = capacity.max(MIN_BUF_SIZE);
        Self::with_buffer(DefaultBuffer::with_capacity(c, writer), encoder)
    }

    /// Returns a reference to the underlying writer.
    pub fn writer_ref(&self) -> &W {
        self.buffer.get_ref()
    }

    /// Finishes the encoding writer and takes the underlying writer out of the structure.
    ///
    /// When this method encounters an error while [`finish`](Self::finish)ing this encoding writer
    /// and destructing [`DefaultBuffer`], it returns an iterator that produces, in order of
    /// occurrence, the unwritten bytes salvaged and the errors reported during operation, in
    /// addition to returning the underlying writer. Since the error iterator is hard to handle, it
    /// is recommended to [`flush`](io::Write::flush) first, which minimizes the chance of error.
    pub fn unwrap_writer(
        self,
    ) -> Result<W, (W, impl Iterator<Item = io::Result<Vec<u8>>> + fmt::Debug)> {
        let (mut buffer, iter) = match self.finish() {
            Ok(buffer) => (buffer, None),
            Err((buffer, iter)) => (buffer, Some(iter)),
        };

        let mut seq = Vec::new();

        if let Err(e) = buffer.flush_buffer() {
            seq.push(Err(e));
        }

        let (writer, unwritten) = buffer.into_parts();
        match unwritten {
            Ok(v) if v.is_empty() => {}
            Ok(v) => seq.push(Ok(v)),
            Err(e) => seq.push(Err(io::Error::new(io::ErrorKind::Other, e))),
        }

        if let Some(e) = iter {
            seq.extend(e);
        }

        if seq.is_empty() {
            Ok(writer)
        } else {
            Err((writer, seq.into_iter()))
        }
    }
}

impl<B: BufferedWrite> EncodingWriter<B> {
    /// Creates a new encoding writer from a buffer and an encoder.
    pub fn with_buffer(buffer: B, encoder: Encoder) -> Self {
        Self {
            buffer,
            encoder: encoder.into(),
            deferred_error: None,
        }
    }

    /// Returns a reference to the underlying buffer.
    pub fn buffer_ref(&self) -> &B {
        &self.buffer
    }

    /// Returns a reference to the underlying encoder.
    pub fn encoder_ref(&self) -> &Encoder {
        &self.encoder
    }

    /// Notifies the underlying encoder of the end of input stream, dropping it and returning the
    /// underlying buffer.
    ///
    /// When this method detects an error finishing the underlying encoder, it returns an iterator
    /// that produces, in order of occurrence, the remaining bytes extracted from the encoder and
    /// the errors reported during operation, in addition to returning the underlying buffer.
    pub fn finish(
        mut self,
    ) -> Result<B, (B, impl Iterator<Item = io::Result<Vec<u8>>> + fmt::Debug)> {
        let mut seq = Vec::new();

        let max_remainder_len = self
            .encoder
            .max_buffer_length_from_utf8_without_replacement(0)
            .unwrap();
        if let Err(e) = self.realize_any_deferred_error() {
            seq.push(Err(e));
        } else if let Err(e) = self.buffer.try_reserve(max_remainder_len, None) {
            seq.push(Err(e));
        }

        let mut dst = Vec::with_capacity(max_remainder_len);
        let (result, _consumed) = self
            .encoder
            .encode_from_utf8_to_vec_without_replacement("", &mut dst, true);
        if !dst.is_empty() {
            if seq.is_empty() {
                // SAFETY: `&[T]` and `&[MaybeUninit<T>]` have the same layout
                self.buffer
                    .unfilled()
                    .get_mut(..dst.len())
                    .expect("illegal `BufferedWrite` implementation")
                    .copy_from_slice(unsafe { mem::transmute(dst.as_slice()) });
                // SAFETY: `dst.len()` elements have just been initialized by `copy_from_slice`
                unsafe { self.buffer.advance(dst.len()) };
            } else {
                seq.push(Ok(dst));
            }
        }

        if let encoding_rs::EncoderResult::Unmappable(c) = result {
            seq.push(Err(UnmappableError::new(c).wrap()));
        } else {
            debug_assert!(matches!(result, encoding_rs::EncoderResult::InputEmpty));
        }

        if seq.is_empty() {
            Ok(self.buffer)
        } else {
            Err((self.buffer, seq.into_iter()))
        }
    }

    /// Writes a string slice into this writer, returning how many input bytes were consumed.
    ///
    /// This is an equivalent of [`write`](std::io::Write::write) but takes a string slice as the
    /// argument instead of a byte slice, eliminating the UTF-8 validation of the input.
    ///
    /// See [the type-level documentation](Self) for the error semantics.
    ///
    /// This method is a low-level call primarily meant for a loop handling [`UnmappableError`] in
    /// a desired manner. See the `UnmappableError` documentation for usage examples. Where
    /// `UnmappableError` is unlikely or is not to be recovered, [`std::write!`] macro is the
    /// primary option because `write_fmt` under the hood also skips the UTF-8 validation.
    pub fn write_str(&mut self, buf: &str) -> io::Result<usize> {
        if buf.is_empty() {
            // report confirmed error if any or return `Ok(0)` otherwise because `io::Write`
            // implementer may do so if input buffer is 0 bytes in length
            self.realize_deferred_error_except_incomplete_utf8()?;
            return Ok(0);
        } else {
            // report any error including `IncompleteUtf8` that represents `MalformedError` before
            // writing another valid `&str`
            self.realize_any_deferred_error()?;
        }
        // pass `None` as the size hint instead of `Some(buf.len())` to rely on Rust's standard
        // adaptive reallocation strategy
        self.buffer.try_reserve(MIN_BUF_SIZE, None)?;
        Ok(self.write_str_inner(buf))
    }

    /// Returns a new writer that writes encoded bytes into this encoding writer, bypassing the
    /// underlying encoder.
    ///
    /// The caller must ensure that the bytes written are a valid byte sequence in the destination
    /// encoding, as this writer does not validate or transform the input byte sequence.
    ///
    /// See [the type-level documentation](Self) for the error semantics of the writer methods
    /// provided by the returned writer.
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
    pub fn passthrough(&mut self) -> PassthroughWriter<B> {
        PassthroughWriter(self)
    }

    /// Returns a new writer that handles [`UnmappableError`] with the specified handler.
    ///
    /// For each unmappable character encountered, the handler is called with two arguments: an
    /// [`UnmappableError`] and a writer created by [`passthrough`] so that the handler can
    /// translate an unmappable character into a desired byte sequence in the destination encoding.
    /// The `Err` returned by the handler is rethrown to the caller of a writer method.
    ///
    /// It is recommended to call [`flush`] after writing the entire data to make sure the
    /// unmappable character found at the end of the input is processed by the handler. See [the
    /// type-level documentation](Self) for the deferred error behavior and `flush`.
    ///
    /// The handler must ensure that the bytes written into the supplied writer are a valid byte
    /// sequence in the destination encoding, as the `passthrough` writer does not validate or
    /// transform the input byte sequence.
    ///
    /// [`passthrough`]: Self::passthrough
    /// [`flush`]: io::Write::flush
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::io::Write as _;
    ///
    /// use encoding_rs::ISO_8859_7; // a.k.a. Latin/Greek
    /// use encoding_rs_rw::EncodingWriter;
    ///
    /// let mut writer = EncodingWriter::new(Vec::new(), ISO_8859_7.new_encoder());
    /// {
    ///     let mut writer =
    ///         writer.with_unmappable_handler(|e, w| write!(w, "&#{};", u32::from(e.value())));
    ///     write!(writer, "Boo!👻")?;
    ///     writer.flush()?; // important
    /// }
    /// assert_eq!(writer.writer_ref(), b"Boo!&#128123;");
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn with_unmappable_handler<'a>(
        &'a mut self,
        handler: impl FnMut(UnmappableError, &mut PassthroughWriter<B>) -> io::Result<()> + 'a,
    ) -> impl io::Write + '_ {
        struct WithUnmappableHandlerWriter<'a, B, H>(&'a mut EncodingWriter<B>, H);

        impl<B: BufferedWrite, H> WithUnmappableHandlerWriter<'_, B, H>
        where
            H: FnMut(UnmappableError, &mut PassthroughWriter<B>) -> io::Result<()>,
        {
            fn handle_deferred_unmappable_error(&mut self) -> io::Result<()> {
                match self.0.deferred_error {
                    Some(DefErr::Unmappable(..)) => match self.0.deferred_error.take() {
                        Some(DefErr::Unmappable(e)) => (self.1)(e, &mut self.0.passthrough()),
                        _ => unreachable!(),
                    },
                    _ => Ok(()),
                }
            }
        }

        impl<B: BufferedWrite, H> WriteFmtAdapter for WithUnmappableHandlerWriter<'_, B, H>
        where
            H: FnMut(UnmappableError, &mut PassthroughWriter<B>) -> io::Result<()>,
        {
            fn write_str_io(&mut self, buf: &str) -> io::Result<usize> {
                self.handle_deferred_unmappable_error()?;
                self.0.write_str_io(buf)
            }
        }

        impl<B: BufferedWrite, H> io::Write for WithUnmappableHandlerWriter<'_, B, H>
        where
            H: FnMut(UnmappableError, &mut PassthroughWriter<B>) -> io::Result<()>,
        {
            fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
                self.handle_deferred_unmappable_error()?;
                self.0.write(buf)
            }

            fn flush(&mut self) -> io::Result<()> {
                self.handle_deferred_unmappable_error()?;
                self.0.flush()
            }

            fn write_fmt(&mut self, f: fmt::Arguments<'_>) -> io::Result<()> {
                self.handle_deferred_unmappable_error()?;
                write_fmt_impl(self, f)
            }
        }

        WithUnmappableHandlerWriter(self, handler)
    }

    fn write_str_inner(&mut self, buf: &str) -> usize {
        debug_assert!(!buf.is_empty());
        debug_assert!(self.deferred_error.is_none());

        let unfilled = self.buffer.unfilled();
        assert!(
            unfilled.len() >= MIN_BUF_SIZE,
            "illegal `BufferedWrite` implementation"
        );
        // SAFETY: `&[T]` and `&[MaybeUninit<T>]` have the same layout. The following code should
        // be okay because it mimics the approach taken by `encoding_rs` to implement the
        // `encode_from_utf8_to_vec_*` methods; however, it is technically UB to create a mutable
        // reference to an uninitialized buffer and pass it to a supposedly write-only function.
        let dst: &mut [u8] = unsafe { mem::transmute(unfilled) };
        let (result, consumed, written) = self
            .encoder
            .encode_from_utf8_without_replacement(buf, dst, false);
        unsafe { self.buffer.advance(written) };
        debug_assert_ne!(consumed, 0);
        debug_assert!(buf.is_char_boundary(consumed), "encoder broke contract");

        if let encoding_rs::EncoderResult::Unmappable(c) = result {
            // defer error until subsequent call because some bytes were consumed successfully
            self.deferred_error = Some(DefErr::Unmappable(UnmappableError::new(c)));
        }

        consumed
    }

    /// Consumes `self.deferred_error` and reports the corresponding `io::Error` (if applicable).
    fn realize_any_deferred_error(&mut self) -> io::Result<()> {
        match self.deferred_error.take() {
            None => Ok(()),
            Some(DefErr::Unmappable(e)) => Err(e.wrap()),
            Some(DefErr::MalformedUtf8(e)) => Err(e.wrap()),
            // `IncompleteUtf8` represents `MalformedError` before writing another `&str` or at EOF,
            // whereas this state can be recovered when writing `&[u8]` containing the subsequent
            // UTF-8 character fragment.
            Some(DefErr::IncompleteUtf8(..)) => Err(MalformedError::new().wrap()),
        }
    }

    /// Invokes `realize_any_deferred_error` if `self.deferred_error` represents an error other
    /// than `IncompleteUtf8`.
    ///
    /// `IncompleteUtf8` is treated differently because it only can be fixed by a later `write`
    /// call.
    fn realize_deferred_error_except_incomplete_utf8(&mut self) -> io::Result<()> {
        match self.deferred_error {
            None | Some(DefErr::IncompleteUtf8(..)) => Ok(()),
            _ => self.realize_any_deferred_error(),
        }
    }
}

impl<B: BufferedWrite> WriteFmtAdapter for EncodingWriter<B> {
    fn write_str_io(&mut self, buf: &str) -> io::Result<usize> {
        self.write_str(buf)
    }
}

impl<B: BufferedWrite> io::Write for EncodingWriter<B> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // recover from IncompleteUtf8 later; otherwise, report any deferred error
        self.realize_deferred_error_except_incomplete_utf8()?;
        if buf.is_empty() {
            return Ok(0);
        }
        self.buffer.try_reserve(MIN_BUF_SIZE, None)?;

        Ok(match self.deferred_error.take() {
            None => match str_from_utf8_up_to_error(buf) {
                // encode `buf` if it starts with valid UTF-8 of at least one byte in length
                //
                // This path doesn't consume any invalid bytes following the valid sequence because
                // it's not sure if `write_str_inner` encodes the entire argument. Accordingly, the
                // other match arms consume invalid UTF-8 bytes only and defer error state until a
                // subsequent call.
                Ok(s) => self.write_str_inner(s),
                // consume invalid bytes and defer `MalformedError` until subsequent call
                Err(Some(error_len)) => {
                    self.deferred_error = Some(DefErr::MalformedUtf8(MalformedError::new()));
                    error_len
                }
                // consume and save incomplete character fragment, waiting for the following bytes
                Err(None) => {
                    let mut bs = util::MiniBuffer::default();
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
                    // incomplete fragment turned out to be invalid UTF-8
                    Err(Some(error_len)) => {
                        self.deferred_error = Some(DefErr::MalformedUtf8(MalformedError::new()));
                        error_len
                    }
                    // still incomplete
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
        self.realize_deferred_error_except_incomplete_utf8()?;
        self.buffer.flush()
    }

    fn write_fmt(&mut self, f: fmt::Arguments<'_>) -> io::Result<()> {
        self.realize_deferred_error_except_incomplete_utf8()?;
        write_fmt_impl(self, f)
    }
}

#[derive(Debug)]
enum DefErr {
    Unmappable(UnmappableError),
    MalformedUtf8(MalformedError),
    IncompleteUtf8(util::MiniBuffer),
}

/// The writer type returned by [`EncodingWriter::passthrough`].
#[derive(Debug)]
pub struct PassthroughWriter<'a, B>(&'a mut EncodingWriter<B>);

impl<B> PassthroughWriter<'_, B> {
    /// Returns a reference to the underlying encoding writer.
    pub fn encoding_writer_ref(&self) -> &EncodingWriter<B> {
        self.0
    }
}

impl<B: BufferedWrite> io::Write for PassthroughWriter<'_, B> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if buf.is_empty() {
            self.0.realize_deferred_error_except_incomplete_utf8()?;
            return Ok(0);
        } else {
            self.0.realize_any_deferred_error()?;
        }
        self.0.buffer.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
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

/// A trait abstracting the byte buffer that exposes its unfilled capacity as a slice.
pub trait BufferedWrite: io::Write {
    /// Returns the unfilled buffer capacity as a slice.
    ///
    /// The caller must [`advance`](Self::advance) the cursor after writing initialized data into
    /// the returned buffer.
    fn unfilled(&mut self) -> &mut [mem::MaybeUninit<u8>];

    /// Marks the first `n` bytes of the unfilled buffer as filled.
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    ///
    /// -  `n` is less than or equal to the length of the unfilled buffer.
    /// -  The first `n` bytes of the unfilled buffer is properly initialized.
    unsafe fn advance(&mut self, n: usize);

    /// Tries to reserve capacity for at least `minimum` more bytes.
    ///
    /// When this method returns `Ok(())`, the implementation must ensure the length of the slice
    /// returned by [`unfilled`](Self::unfilled) is `minimum` or greater. The implementation may
    /// speculatively reserve more space than `minimum` and is encouraged to reserve more than the
    /// `size_hint` provided by the caller, though it may end up reserving less space than
    /// `size_hint` (but not less than `minimum`). The implementation must return `Err` if it
    /// cannot reserve space of `minimum` bytes and may also report `Err` if it encounters an error
    /// in reserving additional memory, flushing the existing content, or any other operations.
    fn try_reserve(&mut self, minimum: usize, size_hint: Option<usize>) -> io::Result<()>;
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
            Err((buffer, mut iter)) => {
                assert_eq!(buffer.get_ref(), b"");
                assert_eq!(buffer.buffer(), b"Oh");
                let e = iter.next().unwrap().unwrap_err();
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
                assert!(iter.next().is_none());
            }
            ret => panic!("assertion failed: {:?}", ret),
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::EUC_JP.new_encoder());
        assert!(matches!(writer.write_all("Oh🥺".as_bytes()), Ok(())));
        match writer.flush() {
            Err(e) => {
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
            }
            ret => panic!("assertion failed: {:?}", ret),
        };
        match writer.finish() {
            Ok(buffer) => {
                assert_eq!(buffer.get_ref(), b"");
                assert_eq!(buffer.buffer(), b"Oh");
            }
            ret => panic!("assertion failed: {:?}", ret),
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_2022_JP.new_encoder());
        assert!(matches!(writer.write_all("Oh🥺".as_bytes()), Ok(())));
        match writer.write(b"") {
            Err(e) => {
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
            }
            ret => panic!("assertion failed: {:?}", ret),
        };
        match writer.finish() {
            Ok(buffer) => {
                assert_eq!(buffer.get_ref(), b"");
                assert_eq!(buffer.buffer(), b"Oh");
            }
            ret => panic!("assertion failed: {:?}", ret),
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::EUC_KR.new_encoder());
        assert!(matches!(write!(writer, "Oh🥺"), Ok(())));
        match writer.finish() {
            Err((buffer, mut iter)) => {
                assert_eq!(buffer.get_ref(), b"");
                assert_eq!(buffer.buffer(), b"Oh");
                let e = iter.next().unwrap().unwrap_err();
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
                assert!(iter.next().is_none());
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
            Err((buffer, mut iter)) => {
                assert_eq!(buffer.get_ref(), &[]);
                assert_eq!(buffer.buffer(), &[b'A', b'B', b'C', b'D', 0xd7]);
                let e = iter.next().unwrap().unwrap_err();
                assert!(MalformedError::wrapped_in(&e).is_some());
                assert!(iter.next().is_none());
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
        assert!(writer.flush().is_ok());

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_15.new_encoder());
        assert!(matches!(
            writer
                .with_unmappable_handler(|_, _| unreachable!())
                .write(&[0xc3]),
            Ok(1),
        ));
        assert!(writer.flush().is_ok());
    }

    #[test]
    fn propagate_error_from_handler() {
        use std::{error, fmt, io};

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::BIG5.new_encoder());
        {
            let mut writer = writer.with_unmappable_handler(|e, _| Err(e.wrap()));
            let ret = write!(writer, "Boo!👻 Boo!👻");
            writer.flush().unwrap();
            assert!(ret
                .unwrap_err()
                .get_ref()
                .unwrap()
                .downcast_ref::<UnmappableError>()
                .is_some());
        }
        assert_eq!(writer.writer_ref(), b"Boo!");

        #[derive(Debug)]
        struct AdHocError;
        impl fmt::Display for AdHocError {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Debug::fmt(self, f)
            }
        }
        impl error::Error for AdHocError {}

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::BIG5.new_encoder());
        {
            let mut writer = writer.with_unmappable_handler(|_, _| {
                Err(io::Error::new(io::ErrorKind::Other, AdHocError))
            });
            let ret = write!(writer, "Boo!👻 Boo!👻");
            writer.flush().unwrap();
            assert!(ret
                .unwrap_err()
                .get_ref()
                .unwrap()
                .downcast_ref::<AdHocError>()
                .is_some());
        }
        assert_eq!(writer.writer_ref(), b"Boo!");
    }

    /// Tests `encoding_rs`'s undocumented guarantee that the ISO-2022-JP encoder is reset to the
    /// ASCII state when an unmappable character is encountered.
    #[test]
    fn iso_2022_jp_at_unmappable() {
        let text = "🐀Lorem ip🐁sum恥の多い🐂生涯をdolor sit 🐃amet送って🐄来ました🐅";
        let expected = {
            let mut dst = Vec::with_capacity(text.len() * 2);
            let mut encoder = encoding_rs::ISO_2022_JP.new_encoder();
            let (result, ..) = encoder.encode_from_utf8_to_vec(text, &mut dst, false);
            assert!(matches!(result, encoding_rs::CoderResult::InputEmpty));
            dst
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_2022_JP.new_encoder());
        {
            let mut writer = writer.with_unmappable_handler(|e, w| {
                assert!(!w.encoding_writer_ref().encoder_ref().has_pending_state());
                write!(w, "&#{};", u32::from(e.value()))
            });
            write!(writer, "{}", text).unwrap();
            writer.flush().unwrap();
        }
        assert_eq!(writer.writer_ref(), &expected);
    }
}
