use std::{io, str};

use encoding_rs::Decoder;

use super::MalformedError;

/// A reader wrapper that decodes an input byte stream into UTF-8.
///
/// This wrapper reads bytes from the underlying reader, decodes them using the specified decoder,
/// and allows callers to access the decoded string through [`std::io::Read`] methods.
///
/// The byte sequence read from this reader is generally valid UTF-8, but that is _not_ always so,
/// especially when the output buffer is less than four bytes in length, in order not to return
/// `Ok(0)` by filling the buffer with a character fragment. When this reader reaches EOF or
/// returns `Err`, the byte sequence read so far, as a whole from the beginning, is guaranteed to
/// be valid UTF-8.
///
/// This reader reports [`MalformedError`] when it encounters a malformed byte sequence in the
/// input. This error is non-fatal, and the reader can continue to decode the subsequent bytes by
/// calling any read methods. See the documentation of [`MalformedError`] for how to resume while
/// replacing the malformed bytes with the replacement character (U+FFED).
///
/// This wrapper returns `Ok(0)` when the underlying reader indicates EOF, but this wrapper does
/// not terminate the internal decoder to stay ready for another byte that the underlying reader
/// might produce. Call [`finish`](DecodingReader::finish) explicitly to let the decoder know the
/// end of the stream, and it will return `MalformedError`, if any, found at the end of the stream.
///
/// # Examples
///
/// ```rust
/// use std::io::Read as _;
///
/// use encoding_rs::UTF_16BE;
/// use encoding_rs_rw::DecodingReader;
///
/// let src: &[u8] = &[254, 255, 216, 61, 222, 2, 216, 61, 220, 123];
/// let mut reader = DecodingReader::new(src, UTF_16BE.new_decoder());
///
/// let mut dst = String::new();
/// reader.read_to_string(&mut dst)?;
/// assert_eq!(dst, "😂👻");
/// # Ok::<(), std::io::Error>(())
/// ```
#[derive(Debug)]
pub struct DecodingReader<R> {
    reader: super::util::BufReadWithFallbackBuffer<R>,
    decoder: super::util::DebuggableDecoder,
    /// A tiny backup buffer used when the buffer supplied by the caller is so small that the
    /// decoder might be unable to write a single UTF-8 character.
    fallback_buf: super::util::MiniBuffer,
    /// Storage to carry an error from one read call to the next, used to tentatively return `Ok`
    /// (as per the contract) after writing some bytes up to an error and report the error at the
    /// beginning of the subsequent call.
    deferred_error: Option<MalformedError>,
}

impl<R: io::BufRead> DecodingReader<R> {
    /// Creates a new decoding reader from a buffered reader and a decoder.
    pub fn new(reader: R, decoder: Decoder) -> Self {
        Self {
            reader: reader.into(),
            decoder: decoder.into(),
            fallback_buf: Default::default(),
            deferred_error: None,
        }
    }

    /// Returns a reference to the underlying reader.
    pub fn reader_ref(&self) -> &R {
        self.reader.as_inner()
    }

    /// Returns a reference to the underlying decoder.
    pub fn decoder_ref(&self) -> &Decoder {
        &self.decoder
    }

    /// Notifies the underlying decoder of the end of input stream, dropping it and returning the
    /// underlying reader, any unread bytes left in `self`, and any error reported at the end of
    /// input byte sequence.
    pub fn finish(mut self) -> (R, Vec<u8>, io::Result<()>) {
        let src_rem = self.reader.fallback_buffer();
        let dst_rem = self.fallback_buf.as_ref();
        let mut remainder = vec![
            0;
            dst_rem.len()
                + self
                    .decoder
                    .max_utf8_buffer_length_without_replacement(src_rem.len())
                    .unwrap()
        ];

        let (a, b) = remainder.split_at_mut(dst_rem.len());
        a.copy_from_slice(dst_rem);
        let (result, _, written) = self
            .decoder
            .decode_to_utf8_without_replacement(src_rem, b, true);
        remainder.truncate(dst_rem.len() + written);

        use encoding_rs::DecoderResult::{InputEmpty, Malformed};
        (
            self.reader.destroy(),
            remainder,
            match result {
                InputEmpty => self.deferred_error.map_or(Ok(()), |e| Err(e.wrap())),
                Malformed(..) if self.deferred_error.is_none() => Err(MalformedError::new().wrap()),
                _ => {
                    debug_assert!(false, "unreachable");
                    Err(io::Error::new(
                        io::ErrorKind::Other,
                        "failed to finish decoder unexpectedly",
                    ))
                }
            },
        )
    }

    fn read_inner(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        debug_assert!(!buf.is_empty());
        debug_assert!(self.fallback_buf.is_empty());
        debug_assert!(self.deferred_error.is_none());

        let src = self.reader.fill_buf()?;
        if src.is_empty() {
            return Ok(0);
        }
        let (result, consumed, written) = if buf.len() > self.fallback_buf.spare_capacity_len() {
            self.decoder
                .decode_to_utf8_without_replacement(src, buf, false)
        } else {
            // use fallback buffer if `buf` may be too small to call decoder method
            let fallback_buf = self.fallback_buf.spare_capacity_mut();
            let (result, consumed, mut written) =
                self.decoder
                    .decode_to_utf8_without_replacement(src, fallback_buf, false);
            if written > 0 {
                self.fallback_buf.add_len(written);
                written = self.fallback_buf.read_at_least_one_byte(buf);
            }
            (result, consumed, written)
        };
        self.reader.consume(consumed);

        if let encoding_rs::DecoderResult::Malformed(..) = result {
            self.deferred_error = Some(MalformedError::new());
        }

        debug_assert!(self.check_utf8_guarantee(&buf[..written]).is_ok());
        Ok(written)
    }

    /// Asserts the UTF-8 guarantee of this reader: the byte sequence read, followed by any
    /// fallback buffer content left in this reader, is a valid UTF-8 sequence.
    fn check_utf8_guarantee(&self, buf_written: &[u8]) -> Result<(), str::Utf8Error> {
        if self.fallback_buf.is_empty() {
            str::from_utf8(buf_written).and(Ok(()))
        } else {
            let mut v = Vec::with_capacity(buf_written.len() + self.fallback_buf.len());
            v.extend(buf_written);
            v.extend(self.fallback_buf.as_ref());
            str::from_utf8(&v).and(Ok(()))
        }
    }

    /// Returns `true` if the bytes returned by this reader so far, as a whole, is a valid UTF-8
    /// sequence.
    fn has_read_valid_utf8(&self) -> bool {
        // true if fallback buffer is empty or previous call happened to read up to char boundary
        self.fallback_buf.is_empty() || str::from_utf8(self.fallback_buf.as_ref()).is_ok()
    }
}

impl<R: io::BufRead> io::Read for DecodingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        // ensure preconditions
        if buf.is_empty() {
            // `io::Read` may return `Ok(0)` if output buffer is 0 bytes in length
            return Ok(0);
        } else if !self.fallback_buf.is_empty() {
            // flush internal buffer if it contains leftovers from previous call; return early to
            // keep this cold path simple even if `buf` has remaining space to read more bytes
            return Ok(self.fallback_buf.read_at_least_one_byte(buf));
        } else if let Some(e) = self.deferred_error.take() {
            // report the error that has been deferred until all the decoded bytes (including those
            // left in the fallback buffer) are written
            return Err(e.wrap());
        }
        match self.read_inner(buf) {
            Ok(0) => match self.deferred_error.take() {
                None => Ok(0),
                Some(e) => Err(e.wrap()),
            },
            ret => ret,
        }
    }

    fn read_to_string(&mut self, buf: &mut String) -> io::Result<usize> {
        // This method skips the UTF-8 validation of the output based on `Decoder`'s guarantee. It
        // delegates to the default `read_to_end` while using `PanicGuard` to make sure that
        // `Vec`'s `len` is reset to a place up to which UTF-8 validity is confirmed.
        //
        // See also https://github.com/rust-lang/rust/blob/1.73.0/library/std/src/io/mod.rs#L432
        struct PanicGuard<'a> {
            len: usize,
            inner: &'a mut Vec<u8>,
        }

        impl Drop for PanicGuard<'_> {
            fn drop(&mut self) {
                unsafe {
                    self.inner.set_len(self.len);
                }
            }
        }

        let mut g = PanicGuard {
            len: buf.len(),
            inner: unsafe { buf.as_mut_vec() },
        };

        let ret = self.read_to_end(g.inner);
        if self.has_read_valid_utf8() {
            g.len = g.inner.len();
            ret
        } else {
            ret?;
            debug_assert!(false, "unreachable");
            Err(io::Error::new(
                io::ErrorKind::Other,
                "failed to read to string unexpectedly",
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;

    use super::{DecodingReader, MalformedError};

    /// Tests rare cases where `finish` reports `Err` after `read` returned `Ok(0)`.
    #[test]
    fn trailing_malformed_bytes() {
        let mut reader = DecodingReader::new(
            &[b'h', b'e', b'l', b'l', b'o', 0xe0][..],
            encoding_rs::SHIFT_JIS.new_decoder(),
        );
        let mut dst = String::new();
        assert!(matches!(reader.read_to_string(&mut dst), Ok(5)));
        assert_eq!(dst, "hello");
        assert!(match reader.finish() {
            (_, v, Err(e)) => v.is_empty() && MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });

        let mut reader = DecodingReader::new(
            &[b'h', b'e', b'l', b'l', b'o', 0xe0][..],
            encoding_rs::SHIFT_JIS.new_decoder(),
        );
        let mut dst = String::new();
        assert!(matches!(reader.read_to_string(&mut dst), Ok(5)));
        assert!(matches!(reader.read_to_string(&mut dst), Ok(0)));
        assert!(matches!(reader.read_to_string(&mut dst), Ok(0)));
        assert!(matches!(reader.read(&mut [0; 64]), Ok(0)));
        assert!(matches!(reader.read(&mut [0; 64]), Ok(0)));
        assert_eq!(dst, "hello");
        assert!(match reader.finish() {
            (_, v, Err(e)) => v.is_empty() && MalformedError::wrapped_in(&e).is_some(),
            _ => false,
        });
    }
}
