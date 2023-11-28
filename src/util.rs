use std::{fmt, io, ops};

use encoding_rs::{Decoder, Encoder};

/// A `Vec`-like struct that handles a tiny stack-allocated byte array.
#[derive(Debug, Default)]
pub(crate) struct MiniBuffer {
    len: u8,
    buf: [u8; 7],
}

impl AsRef<[u8]> for MiniBuffer {
    fn as_ref(&self) -> &[u8] {
        &self.buf[..self.len()]
    }
}

impl MiniBuffer {
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len.into()
    }

    pub fn add_len(&mut self, n: usize) {
        debug_assert!(self.len() + n <= self.buf.len());
        self.len = self.buf.len().min(self.len() + n) as u8;
    }

    pub fn remove_front(&mut self, count: usize) {
        debug_assert!(count <= self.len());
        if count < self.len() {
            self.buf.copy_within(count.., 0);
            self.len -= count as u8;
        } else {
            self.len = 0;
        };
    }

    pub fn spare_capacity_len(&self) -> usize {
        self.buf.len() - self.len()
    }

    pub fn spare_capacity_mut(&mut self) -> &mut [u8] {
        &mut self.buf[self.len.into()..]
    }

    /// Reads bytes from the internal buffer to fill the specified buffer, returning the number of
    /// bytes read.
    pub fn read_to_slice(&mut self, buf: &mut [u8]) -> usize {
        let n = self.len().min(buf.len());
        buf[..n].copy_from_slice(&self.buf[..n]);
        self.remove_front(n);
        n
    }

    /// Writes as many bytes as possible pulled from a reader into the spare capacity.
    pub fn fill_from_reader(&mut self, reader: &mut impl io::Read) -> io::Result<()> {
        while self.spare_capacity_len() > 0 {
            match reader.read(self.spare_capacity_mut()) {
                Ok(0) => break,
                Ok(n) => self.add_len(n),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Writes as many bytes as possible copied from a slice into the spare capacity, returning the
    /// number of bytes consumed.
    pub fn fill_from_slice(&mut self, buf: &[u8]) -> usize {
        let n = self.spare_capacity_len().min(buf.len());
        self.spare_capacity_mut()[..n].copy_from_slice(&buf[..n]);
        self.add_len(n);
        n
    }
}

/// Implements `Debug` for `encoding_rs::Decoder` and `encoding_rs::Encoder`.
macro_rules! define_debuggable_coder {
    ($type_name:ident, $inner_type:ident) => {
        pub struct $type_name($inner_type);

        impl fmt::Debug for $type_name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_struct(stringify!($inner_type))
                    .field("encoding()", self.encoding())
                    .finish()
            }
        }

        impl From<$inner_type> for $type_name {
            fn from(value: $inner_type) -> Self {
                Self(value)
            }
        }

        impl ops::Deref for $type_name {
            type Target = $inner_type;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl ops::DerefMut for $type_name {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }
    };
}

define_debuggable_coder!(DebuggableDecoder, Decoder);
define_debuggable_coder!(DebuggableEncoder, Encoder);
