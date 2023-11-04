//! This crate provides [`std::io::Read`] and [`std::io::Write`] implementations for
//! [`encoding_rs::Decoder`] and [`encoding_rs::Encoder`] to support Rust's standard
//! streaming API.
//!
//! ```rust
//! use std::io::prelude::*;
//!
//! use encoding_rs::{BIG5, SHIFT_JIS};
//! use encoding_rs_rw::{DecodingReader, EncodingWriter};
//!
//! let sjis: &[u8] = &[72, 101, 108, 108, 111, 32, 144, 162, 138, 69];
//! let big5: &[u8] = &[72, 101, 108, 108, 111, 32, 165, 64, 172, 201];
//!
//! let mut reader = DecodingReader::new(sjis, SHIFT_JIS.new_decoder());
//! let mut writer = EncodingWriter::new(Vec::new(), BIG5.new_encoder());
//!
//! let mut utf8 = String::new();
//! reader.read_to_string(&mut utf8)?;
//! assert_eq!(utf8, "Hello 世界");
//!
//! write!(writer, "{}", utf8)?;
//! writer.flush()?;
//! assert_eq!(writer.writer_ref(), big5);
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! This crate is an alternative to [`encoding_rs_io`] but provides a simpler API
//! and more flexible error semantics.
//!
//! [`encoding_rs_io`]: https://crates.io/crates/encoding_rs_io

mod error;
mod reader;
mod writer;

mod util;

pub use error::{MalformedError, UnmappableError};
pub use reader::DecodingReader;
pub use writer::EncodingWriter;

#[cfg(test)]
mod tests {
    mod ja;
}