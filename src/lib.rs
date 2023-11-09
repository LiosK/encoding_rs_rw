//! std::io::{Read, Write} wrappers for encoding_rs
//!
//! This crate provides [`std::io::Read`] and [`std::io::Write`] implementations for
//! [`encoding_rs::Decoder`] and [`encoding_rs::Encoder`], respectively, to support
//! Rust's standard streaming API.
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
//!
//! # Crate features
//!
//! `unstable-handler` enables [`EncodingWriter::with_unmappable_handler`] that
//! provides an encoding writer processing unmappable characters with a specified
//! handler. This feature does not require a nightly build, but the API is
//! experimental and yet to be finalized.

#![cfg_attr(docsrs, feature(doc_cfg))]

mod error;
mod reader;
mod writer;

mod util;

pub use error::{MalformedError, UnmappableError};
pub use reader::DecodingReader;
pub use writer::EncodingWriter;

#[cfg(feature = "unstable-handler")]
#[cfg_attr(docsrs, doc(cfg(feature = "unstable-handler")))]
pub use writer::PassthroughWriter;

#[cfg(test)]
mod tests {
    mod ja;
}
