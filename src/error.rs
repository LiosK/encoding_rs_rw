use std::{error, fmt, io};

/// The error type reported by [`DecodingReader`] and [`EncodingWriter`] when they encounter a
/// malformed byte sequence.
///
/// `DecodingReader` reports this error when its decoder encounters a malformed byte sequence.
/// `EncodingWriter` reports this error when an invalid UTF-8 sequence is supplied as input.
///
/// The [`Read`] and [`Write`] implementations of `DecodingReader` and `EncodingWriter`,
/// respectively, report this error in the form of [`std::io::Error`] wrapping an instance of this
/// type. Callers need to unwrap and downcast the inner error of a reported error, which can be
/// shortcut by [`MalformedError::wrapped_in`].
///
/// [`DecodingReader`]: crate::DecodingReader
/// [`EncodingWriter`]: crate::EncodingWriter
/// [`Read`]: std::io::Read
/// [`Write`]: std::io::Write
///
/// # Examples
///
/// ```rust
/// use encoding_rs::SHIFT_JIS;
/// use encoding_rs_rw::{DecodingReader, MalformedError};
/// use std::io::Read as _;
///
/// let src: &[u8] = &[227, 89, 151, 0xff, 144, 175];
/// let mut reader = DecodingReader::new(src, SHIFT_JIS.new_decoder());
///
/// let mut dst = String::new();
/// while let Err(io_error) = reader.read_to_string(&mut dst) {
///     if MalformedError::wrapped_in(&io_error).is_some() {
///         // insert replacement character (U+FFED) and continue
///         dst.push('�');
///     } else {
///         panic!("found other error than MalformedError: {}", io_error);
///     }
/// }
///
/// assert_eq!(dst, "綺�星");
/// ```
#[derive(Debug)]
pub struct MalformedError(());

impl fmt::Display for MalformedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "encountered a malformed byte sequence")
    }
}

impl error::Error for MalformedError {}

impl MalformedError {
    /// Creates a new error value.
    pub(crate) fn new() -> Self {
        Self(())
    }

    /// Wraps `self` in a [`std::io::Error`].
    pub(crate) fn wrap(self) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, self)
    }

    /// Returns a reference to the `MalformedError` value wrapped by a [`std::io::Error`] if it
    /// contains an inner error whose type is `MalformedError`, or returns `None` otherwise.
    #[inline]
    pub fn wrapped_in(io_error: &io::Error) -> Option<&Self> {
        match io_error.get_ref() {
            Some(e) => e.downcast_ref::<Self>(),
            None => None,
        }
    }
}

/// The error type reported by [`EncodingWriter`] when it encounters an unmappable character.
///
/// The [`Write`] implementation of `EncodingWriter` reports this error in the form of
/// [`std::io::Error`] wrapping an instance of this type. Callers need to unwrap and downcast the
/// inner error of a reported error, which can be shortcut by [`UnmappableError::wrapped_in`].
///
/// [`EncodingWriter`]: crate::EncodingWriter
/// [`Write`]: std::io::Write
///
/// # Examples
///
/// ```rust
/// use encoding_rs::EUC_JP;
/// use encoding_rs_rw::{EncodingWriter, UnmappableError};
/// use std::io::{ErrorKind, Write as _};
///
/// let mut writer = EncodingWriter::new(Vec::new(), EUC_JP.new_encoder());
///
/// let mut src = "矛💥盾";
/// while !src.is_empty() {
///     match writer.write_str(src) {
///         Ok(0) => break,
///         Ok(consumed) => src = &src[consumed..],
///         Err(io_error) if io_error.kind() == ErrorKind::Interrupted => {}
///         Err(io_error) => match UnmappableError::wrapped_in(&io_error) {
///             Some(e) => {
///                 // insert HTML numeric character reference instead of unmappable character
///                 write!(writer.passthrough(), "&#{};", u32::from(e.value()))?;
///             }
///             _ => return Err(io_error),
///         },
///     }
/// }
/// writer.flush()?;
///
/// assert_eq!(
///     writer.writer_ref(),
///     &[204, 183, b'&', b'#', b'1', b'2', b'8', b'1', b'6', b'5', b';', 189, 226]
/// );
/// # Ok::<(), std::io::Error>(())
/// ```
#[derive(Debug)]
pub struct UnmappableError(char);

impl fmt::Display for UnmappableError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "encountered an unmappable character: {:?}", self.0)
    }
}

impl error::Error for UnmappableError {}

impl UnmappableError {
    /// Creates a new error value.
    pub(crate) fn new(unmappable_character: char) -> Self {
        Self(unmappable_character)
    }

    /// Wraps `self` in a [`std::io::Error`].
    pub(crate) fn wrap(self) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, self)
    }

    /// Returns the unmappable character value.
    #[inline]
    pub fn value(&self) -> char {
        self.0
    }

    /// Returns a reference to the `UnmappableError` value wrapped by a [`std::io::Error`] if it
    /// contains an inner error whose type is `UnmappableError`, or returns `None` otherwise.
    #[inline]
    pub fn wrapped_in(io_error: &io::Error) -> Option<&Self> {
        match io_error.get_ref() {
            Some(e) => e.downcast_ref::<Self>(),
            None => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{io, MalformedError, UnmappableError};

    #[test]
    fn unwrap_malformed_error() {
        assert!(MalformedError::wrapped_in(&io::Error::new(
            io::ErrorKind::InvalidData,
            MalformedError(())
        ))
        .is_some());
        assert!(MalformedError::wrapped_in(&io::Error::new(
            io::ErrorKind::Other,
            MalformedError(())
        ))
        .is_some());

        assert!(MalformedError::wrapped_in(&io::ErrorKind::InvalidData.into()).is_none());
        assert!(MalformedError::wrapped_in(&io::ErrorKind::Other.into()).is_none());
        assert!(MalformedError::wrapped_in(&io::Error::new(
            io::ErrorKind::InvalidData,
            "encountered a malformed byte sequence"
        ))
        .is_none());
        assert!(MalformedError::wrapped_in(&io::Error::new(
            io::ErrorKind::Other,
            "encountered a malformed byte sequence"
        ))
        .is_none());
    }

    #[test]
    fn unwrap_unmappable_error() {
        assert!(UnmappableError::wrapped_in(&io::Error::new(
            io::ErrorKind::InvalidData,
            UnmappableError('.')
        ))
        .is_some());
        assert!(UnmappableError::wrapped_in(&io::Error::new(
            io::ErrorKind::Other,
            UnmappableError('.')
        ))
        .is_some());

        assert!(UnmappableError::wrapped_in(&io::ErrorKind::InvalidData.into()).is_none());
        assert!(UnmappableError::wrapped_in(&io::ErrorKind::Other.into()).is_none());
        assert!(UnmappableError::wrapped_in(&io::Error::new(
            io::ErrorKind::InvalidData,
            "encountered an unmappable character"
        ))
        .is_none());
        assert!(UnmappableError::wrapped_in(&io::Error::new(
            io::ErrorKind::Other,
            "encountered an unmappable character"
        ))
        .is_none());

        assert_eq!(
            UnmappableError::wrapped_in(&io::Error::new(
                io::ErrorKind::InvalidData,
                UnmappableError('.')
            ))
            .unwrap()
            .value(),
            '.'
        );
        assert_eq!(
            UnmappableError::wrapped_in(&io::Error::new(
                io::ErrorKind::Other,
                UnmappableError('.')
            ))
            .unwrap()
            .value(),
            '.'
        );
    }
}
