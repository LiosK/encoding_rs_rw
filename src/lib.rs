//! std::io::{Read, Write} wrappers for encoding_rs
//!
//! This crate provides [`std::io::Read`] and [`std::io::Write`] implementations for
//! [`encoding_rs::Decoder`] and [`encoding_rs::Encoder`], respectively, to support
//! Rust's standard streaming API.
//!
//! ```no_run
//! use std::{fs, io, io::prelude::*};
//!
//! use encoding_rs::{EUC_JP, SHIFT_JIS};
//! use encoding_rs_rw::{DecodingReader, EncodingWriter};
//!
//! let file_r = io::BufReader::new(fs::File::open("foo.txt")?);
//! let mut reader = DecodingReader::new(file_r, EUC_JP.new_decoder());
//! let mut utf8 = String::new();
//! reader.read_to_string(&mut utf8)?;
//!
//! let file_w = fs::File::create("bar.txt")?;
//! let mut writer = EncodingWriter::new(file_w, SHIFT_JIS.new_encoder());
//! write!(writer, "{}", utf8)?;
//! writer.flush()?;
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! This crate is an alternative to [`encoding_rs_io`] but provides a simpler API
//! and more flexible error semantics.
//!
//! This crate also provides a [`lossy`] variant of the decoding reader that replaces
//! malformed byte sequences with replacement characters (U+FFED) and a
//! [`with_unmappable_handler`] variant of writer that handles unmappable characters
//! with the specified handler.
//!
//! ```no_run
//! use std::{fs, io, io::prelude::*};
//!
//! use encoding_rs::{EUC_KR, ISO_8859_7};
//! use encoding_rs_rw::{DecodingReader, EncodingWriter};
//!
//! let file_r = io::BufReader::new(fs::File::open("baz.txt")?);
//! let mut reader = DecodingReader::new(file_r, EUC_KR.new_decoder());
//! let mut utf8 = String::new();
//! reader.lossy().read_to_string(&mut utf8)?;
//!
//! let file_w = fs::File::create("qux.txt")?;
//! let mut writer = EncodingWriter::new(file_w, ISO_8859_7.new_encoder());
//! {
//!     let mut writer =
//!         writer.with_unmappable_handler(|e, w| write!(w, "&#{};", u32::from(e.value())));
//!     write!(writer, "{}", utf8)?;
//!     writer.flush()?;
//! }
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! [`encoding_rs_io`]: https://crates.io/crates/encoding_rs_io
//! [`lossy`]: DecodingReader::lossy
//! [`with_unmappable_handler`]: EncodingWriter::with_unmappable_handler

#![cfg_attr(docsrs, feature(doc_cfg))]

mod error;
mod reader;
mod writer;

mod buffer;
mod util;

pub use error::{MalformedError, UnmappableError};
pub use reader::DecodingReader;
pub use writer::EncodingWriter;

/// Miscellaneous types not intended for direct access by name.
pub mod misc {
    pub use super::buffer::{DefaultBuffer, WriterPanicked};
    pub use super::writer::{BufferedWrite, PassthroughWriter};
}

/// Implements `BufferedWrite` for `Vec<u8>`.
mod vec_integration {
    use std::{io, mem};

    impl super::writer::BufferedWrite for Vec<u8> {
        fn unfilled(&mut self) -> &mut [mem::MaybeUninit<u8>] {
            self.spare_capacity_mut()
        }

        unsafe fn advance(&mut self, n: usize) {
            self.set_len(self.len() + n);
        }

        fn try_reserve(&mut self, minimum: usize, size_hint: Option<usize>) -> io::Result<()> {
            let size_hint = size_hint.unwrap_or(minimum);
            if size_hint > minimum && self.try_reserve(size_hint).is_ok() {
                return Ok(());
            }
            self.try_reserve(minimum)
                .map_err(|e| io::Error::new(io::ErrorKind::OutOfMemory, e))
        }
    }
}

#[cfg(test)]
mod tests;
