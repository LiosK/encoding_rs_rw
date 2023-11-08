# std::io::{Read, Write} wrappers for encoding_rs

[![Crates.io](https://img.shields.io/crates/v/encoding_rs_rw)](https://crates.io/crates/encoding_rs_rw)
[![License](https://img.shields.io/crates/l/encoding_rs_rw)](https://github.com/LiosK/encoding_rs_rw/blob/main/LICENSE)

This crate provides `std::io::Read` and `std::io::Write` implementations for
`encoding_rs::Decoder` and `encoding_rs::Encoder`, respectively, to support
Rust's standard streaming API.

```rust
use std::io::prelude::*;

use encoding_rs::{BIG5, SHIFT_JIS};
use encoding_rs_rw::{DecodingReader, EncodingWriter};

let sjis: &[u8] = &[72, 101, 108, 108, 111, 32, 144, 162, 138, 69];
let big5: &[u8] = &[72, 101, 108, 108, 111, 32, 165, 64, 172, 201];

let mut reader = DecodingReader::new(sjis, SHIFT_JIS.new_decoder());
let mut writer = EncodingWriter::new(Vec::new(), BIG5.new_encoder());

let mut utf8 = String::new();
reader.read_to_string(&mut utf8)?;
assert_eq!(utf8, "Hello 世界");

write!(writer, "{}", utf8)?;
writer.flush()?;
assert_eq!(writer.writer_ref(), big5);
```

This crate is an alternative to [`encoding_rs_io`] but provides a simpler API
and more flexible error semantics.

[`encoding_rs_io`]: https://crates.io/crates/encoding_rs_io

## Crate features

- `unstable-handler` enables `EncodingWriter::with_unmappable_handler`. This
  feature does not require a nightly build, but the API is experimental and yet
  to be finalized.

## License

Licensed under the Apache License, Version 2.0.

## See also

- [encoding_rs - crates.io](https://crates.io/crates/encoding_rs)
- [encoding_rs_io - crates.io](https://crates.io/crates/encoding_rs_io)
