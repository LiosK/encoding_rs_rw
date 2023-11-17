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
pub struct EncodingWriter<W: io::Write> {
    writer: BufferedWriter<W>,
    encoder: super::util::DebuggableEncoder,
    /// Storage to carry an error from one write call to the next, used to tentatively return `Ok`
    /// (as per the contract) after consuming erroneous input and report the error at the beginning
    /// of the subsequent call.
    deferred_error: Option<DefErr>,
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
            writer: BufferedWriter::with_capacity(capacity.max(MIN_BUF_SIZE), writer),
            encoder: encoder.into(),
            deferred_error: None,
        }
    }

    /// Returns a reference to the underlying writer.
    pub fn writer_ref(&self) -> &W {
        self.writer.get_ref()
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
        let mut temp_buf = Vec::with_capacity(
            self.encoder
                .max_buffer_length_from_utf8_without_replacement(0)
                .unwrap(),
        );
        let (result, _) =
            self.encoder
                .encode_from_utf8_to_vec_without_replacement("", &mut temp_buf, true);

        let deferred_error = match result {
            encoding_rs::EncoderResult::InputEmpty => self.realize_any_deferred_error(),
            _ => {
                debug_assert!(false, "unreachable");
                Err(io::Error::new(
                    io::ErrorKind::Other,
                    "failed to finish encoder unexpectedly",
                ))
            }
        };

        let (writer, mut buffer) = self.writer.into_parts();
        buffer.extend(temp_buf);

        (writer, buffer, deferred_error)
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
            // report confirmed error if any or return `Ok(0)` otherwise because `io::Write`
            // implementer may do so if input buffer is 0 bytes in length
            self.realize_deferred_error_except_incomplete_utf8()?;
            return Ok(0);
        } else {
            // report any error including `IncompleteUtf8` that represents `MalformedError` before
            // writing another valid `&str`
            self.realize_any_deferred_error()?;
        }
        self.writer.try_reserve(MIN_BUF_SIZE, None)?;
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
    pub fn passthrough(&mut self) -> PassthroughWriter<W> {
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
    ///     writer.flush()?;
    /// }
    /// assert_eq!(writer.writer_ref(), b"Boo!&#128123;");
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn with_unmappable_handler<'a>(
        &'a mut self,
        handler: impl FnMut(UnmappableError, &mut PassthroughWriter<W>) -> io::Result<()> + 'a,
    ) -> impl io::Write + '_ {
        struct WithUnmappableHandlerWriter<'a, W: io::Write, H>(&'a mut EncodingWriter<W>, H);

        impl<W: io::Write, H> WithUnmappableHandlerWriter<'_, W, H>
        where
            H: FnMut(UnmappableError, &mut PassthroughWriter<W>) -> io::Result<()>,
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

        impl<W: io::Write, H> WriteFmtAdapter for WithUnmappableHandlerWriter<'_, W, H>
        where
            H: FnMut(UnmappableError, &mut PassthroughWriter<W>) -> io::Result<()>,
        {
            fn write_str_io(&mut self, buf: &str) -> io::Result<usize> {
                self.handle_deferred_unmappable_error()?;
                self.0.write_str_io(buf)
            }
        }

        impl<W: io::Write, H> io::Write for WithUnmappableHandlerWriter<'_, W, H>
        where
            H: FnMut(UnmappableError, &mut PassthroughWriter<W>) -> io::Result<()>,
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
        debug_assert!(self.writer.unfilled().len() >= MIN_BUF_SIZE);

        // SAFETY: `mem::transmute` is generally okay because `&[T]` and `&[MaybeUninit<T>]` have
        // the same layout and `u8` is a trivial type. It is technically UB to create a mutable
        // reference to an uninitialized byte buffer and pass it to a supposedly write-only
        // function, though the following code mimics the approach taken by `encoding_rs` to
        // implement the `encode_from_utf8_to_vec_*` methods.
        let (result, consumed, written) = self.encoder.encode_from_utf8_without_replacement(
            buf,
            unsafe { mem::transmute(self.writer.unfilled()) },
            false,
        );
        unsafe { self.writer.advance(written) };
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

impl<W: io::Write> WriteFmtAdapter for EncodingWriter<W> {
    fn write_str_io(&mut self, buf: &str) -> io::Result<usize> {
        self.write_str(buf)
    }
}

impl<W: io::Write> io::Write for EncodingWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // recover from IncompleteUtf8 later; otherwise, report any deferred error
        self.realize_deferred_error_except_incomplete_utf8()?;
        if buf.is_empty() {
            return Ok(0);
        }
        self.writer.try_reserve(MIN_BUF_SIZE, None)?;

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
        self.realize_any_deferred_error()?;
        self.writer.flush()
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
            self.0.realize_deferred_error_except_incomplete_utf8()?;
            return Ok(0);
        } else {
            self.0.realize_any_deferred_error()?;
        }
        self.0.writer.write(buf)
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

/// A trait abstracting the buffered byte writer that exposes its unfilled capacity as a slice.
trait BufferedWrite: io::Write {
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
    /// returned by `unfilled` is `minimum` or greater. The implementation may speculatively
    /// reserve more space than `minimum` and is encouraged to reserve more than the `size_hint`
    /// provided by the caller, though it may end up reserving less space than `size_hint` (but not
    /// less than `minimum`). The implementation must return `Err` if it cannot reserve space of
    /// `minimum` bytes and may also report `Err` if it encounters an error in flushing the
    /// existing content or any other operations.
    fn try_reserve(&mut self, minimum: usize, size_hint: Option<usize>) -> io::Result<()>;
}

/// A [`BufWriter`](io::BufWriter)-like type that exposes its unfilled capacity as a slice through
/// [`BufferedWrite`] trait.
#[derive(Debug)]
struct BufferedWriter<W: io::Write> {
    buffer: Vec<u8>,
    panicked: bool,
    inner: W,
}

impl<W: io::Write> BufferedWriter<W> {
    fn with_capacity(capacity: usize, inner: W) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            panicked: false,
            inner,
        }
    }

    fn get_ref(&self) -> &W {
        &self.inner
    }

    fn into_parts(self) -> (W, Vec<u8>) {
        // destruct `self`, moving out some fields and dropping the rest
        unsafe {
            let mut m = mem::ManuallyDrop::new(self);
            ptr::drop_in_place(&mut m.panicked);
            (ptr::read(&m.inner), ptr::read(&m.buffer))
        }
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
            buffer: &mut self.buffer,
        };

        while g.consumed < g.buffer.len() {
            self.panicked = true;
            let ret = self.inner.write(&g.buffer[g.consumed..]);
            self.panicked = false;

            match ret {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write buffered data to writer",
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

impl<W: io::Write> Drop for BufferedWriter<W> {
    fn drop(&mut self) {
        // don't double-flush the buffer when the inner writer panicked in a call to write
        if !self.panicked {
            let _ = self.flush_buffer();
        }
    }
}

impl<W: io::Write> io::Write for BufferedWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.try_reserve(1, Some(buf.len()))?;
        let capacity = self.unfilled().len();
        if buf.len() > capacity && self.buffer.is_empty() {
            // bypass the internal buffer if the input buffer is large
            self.panicked = true;
            let ret = self.inner.write(buf);
            self.panicked = false;
            ret
        } else {
            let n = buf.len().min(capacity);
            // SAFETY: `&[T]` and `&[MaybeUninit<T>]` have the same layout
            self.unfilled()[..n].copy_from_slice(unsafe { mem::transmute(&buf[..n]) });
            // SAFETY: `n` elements have just been initialized by `copy_from_slice`
            unsafe { self.advance(n) };
            Ok(n)
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flush_buffer()?;
        self.inner.flush()
    }
}

impl<W: io::Write> BufferedWrite for BufferedWriter<W> {
    fn unfilled(&mut self) -> &mut [mem::MaybeUninit<u8>] {
        self.buffer.spare_capacity_mut()
    }

    unsafe fn advance(&mut self, n: usize) {
        assert!(self.buffer.len() + n <= self.buffer.capacity());
        self.buffer.set_len(self.buffer.len() + n);
    }

    fn try_reserve(&mut self, minimum: usize, size_hint: Option<usize>) -> io::Result<()> {
        if self.buffer.capacity() - self.buffer.len()
            < size_hint.map_or(minimum, |n| n.max(minimum))
        {
            self.flush_buffer()?;
            if self.buffer.capacity() - self.buffer.len() < minimum {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "failed to reserve minimum buffer capacity",
                ));
            }
        }
        Ok(())
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
                assert_eq!(writer, b"");
                assert_eq!(buffer, b"Oh");
                assert_eq!(UnmappableError::wrapped_in(&e).unwrap().value(), '🥺');
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
            (writer, buffer, Ok(())) => {
                assert_eq!(writer, b"");
                assert_eq!(buffer, b"Oh");
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
            (writer, buffer, Ok(())) => {
                assert_eq!(writer, b"");
                assert_eq!(buffer, b"Oh");
            }
            ret => panic!("assertion failed: {:?}", ret),
        };

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::EUC_KR.new_encoder());
        assert!(matches!(write!(writer, "Oh🥺"), Ok(())));
        match writer.finish() {
            (writer, buffer, Err(e)) => {
                assert_eq!(writer, b"");
                assert_eq!(buffer, b"Oh");
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

        let mut writer = EncodingWriter::new(Vec::new(), encoding_rs::ISO_8859_15.new_encoder());
        assert!(matches!(
            writer
                .with_unmappable_handler(|_, _| unreachable!())
                .write(&[0xc3]),
            Ok(1),
        ));
        assert!(match writer.flush() {
            Err(e) => MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });
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
}
