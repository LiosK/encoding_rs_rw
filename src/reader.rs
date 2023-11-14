use std::{io, str};

use encoding_rs::Decoder;

use super::MalformedError;

/// A reader wrapper that decodes an input byte stream into UTF-8.
///
/// This wrapper reads bytes from the underlying reader, decodes them using the specified decoder,
/// and allows callers to access the decoded string through [`std::io::Read`] methods.
///
/// The byte sequence read from this reader is generally valid UTF-8, but that is _not_ always so,
/// especially when the output buffer is less than four bytes in length. In such a case, this
/// reader fills the given buffer with a character fragment in order not to return `Ok(0)`. When
/// this reader reaches EOF or returns `Err`, the byte sequence read so far, as a whole from the
/// beginning, is guaranteed to be valid UTF-8.
///
/// This reader reports [`MalformedError`] when it encounters a malformed byte sequence in the
/// input. This error is non-fatal, and the reader can continue to decode the subsequent bytes by
/// calling any read methods. See the documentation of [`MalformedError`] for how to resume while
/// replacing the malformed bytes with the replacement character (U+FFED).
///
/// This wrapper terminates the decoder and stops reading subsequent bytes from the underlying
/// reader when the underlying reader reports an EOF.
///
/// See [`DecodingReader::lossy`] for a variant of this reader that handles `MalformedError`s
/// automatically.
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
    decoder: Option<super::util::DebuggableDecoder>,
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
            decoder: Some(decoder.into()),
            fallback_buf: Default::default(),
            deferred_error: None,
        }
    }

    /// Returns a reference to the underlying reader.
    pub fn reader_ref(&self) -> &R {
        self.reader.as_inner()
    }

    /// Returns a reference to the underlying decoder if it is still active or `None` otherwise.
    pub fn decoder_ref(&self) -> Option<&Decoder> {
        self.decoder.as_deref()
    }

    /// Takes the underlying reader out of the structure.
    ///
    /// In addition to the underlying reader, this method returns a _leftover_ reader that delivers
    /// the bytes already consumed from the underlying reader but not yet read by the caller.
    pub fn take_reader(self) -> (R, DecodingReader<impl io::BufRead>) {
        let (reader, remainder) = self.reader.into_parts();
        (
            reader,
            DecodingReader {
                reader: io::Cursor::new(remainder).into(),
                decoder: self.decoder,
                fallback_buf: self.fallback_buf,
                deferred_error: self.deferred_error,
            },
        )
    }

    /// Returns a variant of this decoding reader that replaces a detected malformed byte sequence
    /// with a replacement character (U+FFFD) instead of reporting a `MalformedError`.
    ///
    /// The returned reader has the same UTF-8 validity guarantee and error semantics as those of
    /// [`DecodingReader`], except that it does not report `MalformedError`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::io::Read as _;
    ///
    /// use encoding_rs::EUC_JP;
    /// use encoding_rs_rw::DecodingReader;
    ///
    /// let src: &[u8] = &[182, 229, 187, 0xff, 176, 236, 192, 184];
    /// let mut reader = DecodingReader::new(src, EUC_JP.new_decoder());
    ///
    /// let mut dst = String::new();
    /// reader.lossy().read_to_string(&mut dst)?;
    ///
    /// assert_eq!(dst, "九�一生");
    /// # Ok::<(), std::io::Error>(())
    /// ```
    pub fn lossy(&mut self) -> impl io::Read + '_ {
        struct LossyReader<'a, R>(&'a mut DecodingReader<R>);

        impl<R: io::BufRead> ReadToStringAdapter for LossyReader<'_, R> {
            fn has_read_valid_utf8(&self) -> bool {
                self.0.has_read_valid_utf8()
            }
        }

        impl<R: io::BufRead> io::Read for LossyReader<'_, R> {
            fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
                self.0.read_impl::<true, true>(buf)
            }

            fn read_to_string(&mut self, buf: &mut String) -> io::Result<usize> {
                read_to_string_impl(self, buf)
            }
        }

        LossyReader(self)
    }

    /// Implements [`std::io::Read::read`].
    ///
    /// -   `LOSSY` controls whether a malformed byte sequence is replaced with a replacement
    ///     character (`true`) or reported as an error (`false`).
    /// -   `FUSED` controls whether the underlying decoder is closed (`true`) or not (`false`)
    ///     when the underlying reader reports an EOF.
    fn read_impl<const LOSSY: bool, const FUSED: bool>(
        &mut self,
        buf: &mut [u8],
    ) -> io::Result<usize> {
        if !self.fallback_buf.is_empty() {
            // flush internal buffer if it contains leftovers from previous call; return early to
            // keep this cold path simple even if `buf` has remaining space to read more bytes
            return Ok(self.fallback_buf.read_buf(buf));
        } else if let Some(e) = self.deferred_error.take() {
            return if !LOSSY {
                // report the error that has been deferred until all the decoded bytes (including
                // those left in the fallback buffer) are written
                Err(e.wrap())
            } else {
                // write REPLACEMENT CHARACTER and return early because `self.reader.fill_buf()?`
                // called later may return `Err`
                const REPL: &[u8] = "\u{FFFD}".as_bytes();
                if buf.len() >= REPL.len() {
                    buf[..REPL.len()].copy_from_slice(REPL);
                    Ok(REPL.len())
                } else {
                    self.fallback_buf.fill_from_slice(REPL);
                    Ok(self.fallback_buf.read_buf(buf))
                }
            };
        } else if self.decoder.is_none() || buf.is_empty() {
            // stop if decoder is already closed or if input buffer is empty
            return Ok(0);
        }

        debug_assert!(self.fallback_buf.is_empty());
        debug_assert!(self.deferred_error.is_none());
        debug_assert!(self.decoder.is_some() && !buf.is_empty());

        let src = self.reader.fill_buf()?;
        if src.is_empty() {
            return if FUSED {
                // close decoder when underlying reader reports EOF
                self.close_decoder::<LOSSY>(buf)
            } else {
                Ok(0)
            };
        }

        let decoder = self.decoder.as_deref_mut().unwrap();
        let written = if !LOSSY {
            let (result, consumed, written) =
                decode_with_fallback_buf(buf, &mut self.fallback_buf, |dst| {
                    decoder.decode_to_utf8_without_replacement(src, dst, false)
                });
            self.reader.consume(consumed);

            if let encoding_rs::DecoderResult::Malformed(..) = result {
                if written == 0 {
                    return Err(MalformedError::new().wrap());
                }
                // defer error until subsequent call because some bytes were written successfully
                self.deferred_error = Some(MalformedError::new());
            }

            written
        } else {
            let (_, consumed, written) =
                decode_with_fallback_buf(buf, &mut self.fallback_buf, |dst| {
                    let ret = decoder.decode_to_utf8(src, dst, false);
                    (ret.0, ret.1, ret.2)
                });
            self.reader.consume(consumed);

            written
        };

        debug_assert!(self.check_utf8_guarantee(&buf[..written]).is_ok());
        if FUSED && written == 0 {
            // This path is supposed (though not proved) to be unreachable.
            self.close_decoder::<LOSSY>(buf)
        } else {
            Ok(written)
        }
    }

    /// Closes and discards the underlying decoder.
    ///
    /// This method must be called from within `read_impl` to ensure preconditions.
    fn close_decoder<const LOSSY: bool>(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        debug_assert!(self.fallback_buf.is_empty());
        debug_assert!(self.deferred_error.is_none());
        debug_assert!(self.decoder.is_some() && !buf.is_empty());
        let mut decoder = self.decoder.take().unwrap();
        let written = if !LOSSY {
            let (result, _, written) =
                decode_with_fallback_buf(buf, &mut self.fallback_buf, |dst| {
                    decoder.decode_to_utf8_without_replacement(&[], dst, true)
                });

            if let encoding_rs::DecoderResult::Malformed(..) = result {
                if written == 0 {
                    return Err(MalformedError::new().wrap());
                }
                self.deferred_error = Some(MalformedError::new());
            }

            written
        } else {
            let (_, _, written) = decode_with_fallback_buf(buf, &mut self.fallback_buf, |dst| {
                let ret = decoder.decode_to_utf8(&[], dst, true);
                (ret.0, ret.1, ret.2)
            });

            written
        };

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
}

impl<R: io::BufRead> ReadToStringAdapter for DecodingReader<R> {
    fn has_read_valid_utf8(&self) -> bool {
        // true if fallback buffer is empty or previous call happened to read up to char boundary
        self.fallback_buf.is_empty() || str::from_utf8(self.fallback_buf.as_ref()).is_ok()
    }
}

impl<R: io::BufRead> io::Read for DecodingReader<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.read_impl::<false, true>(buf)
    }

    fn read_to_string(&mut self, buf: &mut String) -> io::Result<usize> {
        read_to_string_impl(self, buf)
    }
}

trait ReadToStringAdapter: io::Read {
    /// Returns `true` if the bytes returned by this reader so far, as a whole, is a valid UTF-8
    /// sequence.
    fn has_read_valid_utf8(&self) -> bool;
}

/// Implements [`std::io::Read::read_to_string`].
///
/// This function skips the UTF-8 validation of the output based on `Decoder`'s guarantee. It
/// delegates to the default `read_to_end` while using `PanicGuard` to make sure that the inner
/// `Vec`'s `len` is reset to the place up to which UTF-8 validity is confirmed.
///
/// See also https://github.com/rust-lang/rust/blob/1.73.0/library/std/src/io/mod.rs#L432
fn read_to_string_impl(
    reader: &mut impl ReadToStringAdapter,
    buf: &mut String,
) -> io::Result<usize> {
    // A panic guard structure to ensure that the inner `Vec`'s `len` is reset to the place up to
    // which UTF-8 validity is confirmed.
    struct PanicGuard<'a> {
        len: usize,
        inner: &'a mut Vec<u8>,
    }

    impl Drop for PanicGuard<'_> {
        fn drop(&mut self) {
            unsafe { self.inner.set_len(self.len) };
        }
    }

    let mut g = PanicGuard {
        len: buf.len(),
        inner: unsafe { buf.as_mut_vec() },
    };
    let ret = reader.read_to_end(g.inner);
    if reader.has_read_valid_utf8() {
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

/// Executes the specified decoder method but uses the fallback buffer is the destination buffer
/// may be too small to call the decoder method.
///
/// This function assumes that the fallback buffer is empty.
fn decode_with_fallback_buf<T>(
    dst_buf: &mut [u8],
    fallback_buf: &mut super::util::MiniBuffer,
    mut decode: impl FnMut(&mut [u8]) -> (T, usize, usize),
) -> (T, usize, usize) {
    debug_assert!(fallback_buf.is_empty());
    if dst_buf.len() > fallback_buf.spare_capacity_len() {
        decode(dst_buf)
    } else {
        let (result, consumed, mut written) = decode(fallback_buf.spare_capacity_mut());
        if written > 0 {
            fallback_buf.add_len(written);
            written = fallback_buf.read_buf(dst_buf);
        }
        (result, consumed, written)
    }
}

#[cfg(test)]
mod tests {
    use std::io::Read;

    use super::DecodingReader;

    /// Tests the handling of malformed byte sequence at the end of the input stream.
    #[test]
    fn trailing_malformed_bytes() {
        use encoding_rs::SHIFT_JIS as Enc;
        let src: &[u8] = &[b'h', b'e', b'l', b'l', b'o', 0xe0];

        let mut reader = DecodingReader::new(src, Enc.new_decoder());
        let mut dst = String::new();
        assert!(reader.read_to_string(&mut dst).is_err());
        assert_eq!(dst, "hello");
        assert!(matches!(reader.read_to_string(&mut dst), Ok(0)));
        assert!(matches!(reader.read_to_string(&mut dst), Ok(0)));
        assert!(matches!(reader.read(&mut [0; 64]), Ok(0)));
        assert!(matches!(reader.read(&mut [0; 64]), Ok(0)));
        assert_eq!(dst, "hello");

        let mut reader = DecodingReader::new(src, Enc.new_decoder());
        let mut dst = [0; 64];
        assert!(matches!(reader.read(&mut dst), Ok(5)));
        assert_eq!(&dst[..5], b"hello");
        assert!(reader.read(&mut dst[5..]).is_err());
        assert!(matches!(reader.read(&mut dst[5..]), Ok(0)));
        assert!(matches!(reader.read(&mut dst[5..]), Ok(0)));
        assert_eq!(&dst[..5], b"hello");

        let mut reader = DecodingReader::new(src, Enc.new_decoder());
        let mut dst = String::new();
        assert!(matches!(reader.lossy().read_to_string(&mut dst), Ok(8)));
        assert_eq!(dst, "hello\u{FFFD}");
    }
}
