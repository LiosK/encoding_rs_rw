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
    pub use super::buffer::{DefaultBuffer, VecBuffer, WriterPanicked};
    pub use super::writer::{BufferedWrite, PassthroughWriter};
}

#[cfg(test)]
mod tests;
