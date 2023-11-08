use std::io::{self, prelude::*};

use encoding_rs::{BIG5, EUC_JP, EUC_KR, ISO_2022_JP, ISO_8859_15, SHIFT_JIS};

use crate::{DecodingReader, EncodingWriter, MalformedError, UnmappableError};

/// Tests the reader's high level API usage.
#[test]
fn reader_high_level_api() {
    TEST_CASES.with(|cs| {
        for c in cs {
            let mut reader =
                DecodingReader::new(io::BufReader::new(c.encoded()), c.encoding.new_decoder());
            let mut dst = String::new();
            reader.read_to_string(&mut dst).unwrap();
            assert_eq!(dst, c.decoded());
            assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
        }
    });
}

/// Tests the lossy reader's high level API usage.
#[test]
fn lossy_reader_high_level_api() {
    TEST_CASES.with(|cs| {
        for c in cs {
            let mut reader =
                DecodingReader::new(io::BufReader::new(c.encoded()), c.encoding.new_decoder());
            {
                let mut reader = reader.lossy();
                let mut dst = String::new();
                reader.read_to_string(&mut dst).unwrap();
                assert_eq!(dst, c.decoded());
            }
            assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
        }
    });
}

/// Tests the writer's high level API usage.
#[test]
fn writer_high_level_api() {
    TEST_CASES.with(|cs| {
        for c in cs {
            let mut writer = EncodingWriter::new(Vec::new(), c.encoding.new_encoder());
            write!(writer, "{}", c.decoded()).unwrap();
            writer.flush().unwrap();
            assert_eq!(writer.writer_ref(), c.encoded());
            assert!(matches!(writer.finish(), (_, v, Ok(())) if v.is_empty()));
        }
    });
}

/// Tests the reader for byte-by-byte streaming.
#[test]
fn reader_byte_by_byte() {
    TEST_CASES.with(|cs| {
        for c in cs {
            let mut reader = DecodingReader::new(
                io::BufReader::with_capacity(1, c.encoded()),
                c.encoding.new_decoder(),
            );
            let mut dst = Vec::with_capacity(c.decoded().len());
            let mut buf = [0u8; 1];
            loop {
                match reader.read(&mut buf) {
                    Ok(0) => break,
                    Ok(n) => dst.extend(&buf[..n]),
                    ret => panic!("assertion failed: {:?}", ret),
                }
            }
            assert_eq!(String::from_utf8(dst).unwrap(), c.decoded());
            assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
        }
    });
}

/// Tests the lossy reader for byte-by-byte streaming.
#[test]
fn lossy_reader_byte_by_byte() {
    TEST_CASES.with(|cs| {
        for c in cs {
            let mut reader = DecodingReader::new(
                io::BufReader::with_capacity(1, c.encoded()),
                c.encoding.new_decoder(),
            );
            {
                let mut reader = reader.lossy();
                let mut dst = Vec::with_capacity(c.decoded().len());
                let mut buf = [0u8; 1];
                loop {
                    match reader.read(&mut buf) {
                        Ok(0) => break,
                        Ok(n) => dst.extend(&buf[..n]),
                        ret => panic!("assertion failed: {:?}", ret),
                    }
                }
                assert_eq!(String::from_utf8(dst).unwrap(), c.decoded());
            }
            assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
        }
    });
}

/// Tests the writer for byte-by-byte streaming.
#[test]
fn writer_byte_by_byte() {
    TEST_CASES.with(|cs| {
        for c in cs {
            let mut writer = EncodingWriter::new(Vec::new(), c.encoding.new_encoder());
            let mut src = c.decoded().as_bytes();
            while !src.is_empty() {
                match writer.write(&src[..1]) {
                    Ok(1) => src = &src[1..],
                    ret => panic!("assertion failed: {:?}", ret),
                }
            }
            writer.flush().unwrap();
            assert_eq!(writer.writer_ref(), c.encoded());
            assert!(matches!(writer.finish(), (_, v, Ok(())) if v.is_empty()));
        }
    });
}

/// Emulates the replacement behavior of `encoding_rs::Decoder`.
#[test]
fn reader_malformed_bytes() {
    TEST_CASES.with(|cs| {
        for a in cs {
            for b in cs {
                // skip ISO_2022_JP as it is 7-bit encoding and is indistinguishable from ASCII
                if a.encoding != b.encoding && b.encoding != ISO_2022_JP {
                    let expected = {
                        let mut decoder = a.encoding.new_decoder();
                        let mut dst = String::with_capacity(
                            decoder.max_utf8_buffer_length(b.encoded().len()).unwrap(),
                        );
                        let (result, consumed, replaced) =
                            decoder.decode_to_string(b.encoded(), &mut dst, true);
                        assert_eq!(result, encoding_rs::CoderResult::InputEmpty);
                        assert_eq!(consumed, b.encoded().len());
                        assert!(replaced);
                        dst
                    };

                    let actual = {
                        let mut reader = DecodingReader::new(b.encoded(), a.encoding.new_decoder());
                        let mut dst = String::new();
                        while let Err(io_error) = reader.read_to_string(&mut dst) {
                            if MalformedError::wrapped_in(&io_error).is_some() {
                                dst.push('�');
                            } else {
                                unreachable!();
                            }
                        }
                        assert!(matches!(reader.read(&mut [0; 64]), Ok(0)));
                        assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
                        dst
                    };
                    assert_eq!(actual, expected);

                    let actual_byte_by_byte = {
                        let mut reader = DecodingReader::new(
                            io::BufReader::with_capacity(1, b.encoded()),
                            a.encoding.new_decoder(),
                        );
                        let mut dst = Vec::new();
                        let mut buf = [0u8; 1];
                        loop {
                            match reader.read(&mut buf) {
                                Ok(0) => break,
                                Ok(n) => dst.extend(&buf[..n]),
                                Err(e) if MalformedError::wrapped_in(&e).is_some() => {
                                    dst.extend("�".as_bytes())
                                }
                                ret => panic!("assertion failed: {:?}", ret),
                            }
                        }
                        assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
                        String::from_utf8(dst).unwrap()
                    };
                    assert_eq!(actual_byte_by_byte, expected);

                    let actual_lossy = {
                        let mut reader = DecodingReader::new(b.encoded(), a.encoding.new_decoder());
                        let mut dst = String::new();
                        reader.lossy().read_to_string(&mut dst).unwrap();
                        assert!(matches!(reader.lossy().read(&mut [0; 64]), Ok(0)));
                        assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
                        dst
                    };
                    assert_eq!(actual_lossy, expected);

                    let actual_lossy_byte_by_byte = {
                        let mut reader = DecodingReader::new(
                            io::BufReader::with_capacity(1, b.encoded()),
                            a.encoding.new_decoder(),
                        );
                        let mut dst = Vec::new();
                        let mut buf = [0u8; 1];
                        loop {
                            match reader.lossy().read(&mut buf) {
                                Ok(0) => break,
                                Ok(n) => dst.extend(&buf[..n]),
                                ret => panic!("assertion failed: {:?}", ret),
                            }
                        }
                        assert!(matches!(reader.finish(), (_, v, Ok(())) if v.is_empty()));
                        String::from_utf8(dst).unwrap()
                    };
                    assert_eq!(actual_lossy_byte_by_byte, expected);
                }
            }
        }
    });
}

/// Emulates the replacement behavior of `encoding_rs::Encoder`.
#[test]
fn writer_unmappable_char() {
    TEST_CASES_UNMAPPABLE.with(|cs| {
        for c in cs {
            let actual = {
                let mut src = c.decoded();
                let mut writer = EncodingWriter::new(Vec::new(), c.encoding.new_encoder());
                while !src.is_empty() {
                    match writer.write_str(src) {
                        Ok(0) => unreachable!(),
                        Ok(consumed) => src = &src[consumed..],
                        Err(io_error) => {
                            if let Some(e) = UnmappableError::wrapped_in(&io_error) {
                                write!(writer.passthrough(), "&#{};", u32::from(e.value()))
                                    .unwrap();
                            } else {
                                unreachable!();
                            }
                        }
                    }
                }
                writer.flush().unwrap();
                let (dst, _, _) = writer.finish();
                dst
            };
            assert_eq!(actual, c.encoded());

            let actual_byte_by_byte = {
                let mut src = c.decoded().as_bytes();
                let mut writer = EncodingWriter::new(Vec::new(), c.encoding.new_encoder());
                while !src.is_empty() {
                    match writer.write(&src[..1]) {
                        Ok(1) => src = &src[1..],
                        Ok(_) => unreachable!(),
                        Err(io_error) => {
                            if let Some(e) = UnmappableError::wrapped_in(&io_error) {
                                write!(writer.passthrough(), "&#{};", u32::from(e.value()))
                                    .unwrap();
                            } else {
                                unreachable!();
                            }
                        }
                    }
                }
                writer.flush().unwrap();
                let (dst, _, _) = writer.finish();
                dst
            };
            assert_eq!(actual_byte_by_byte, c.encoded());
        }
    });
}
/// Emulates the replacement behavior of `encoding_rs::Encoder`.
#[cfg(feature = "unstable-handler")]
#[test]
fn writer_unmappable_char_with_handler() {
    TEST_CASES_UNMAPPABLE.with(|cs| {
        for c in cs {
            let actual_handler = {
                let src = c.decoded();
                let mut writer = EncodingWriter::new(Vec::new(), c.encoding.new_encoder());
                {
                    let mut writer = writer
                        .with_unmappable_handler(|e, w| write!(w, "&#{};", u32::from(e.value())));
                    write!(writer, "{}", src).unwrap();
                    writer.flush().unwrap();
                }
                let (dst, _, _) = writer.finish();
                dst
            };
            assert_eq!(actual_handler, c.encoded());

            let actual_handler_byte_by_byte = {
                let mut src = c.decoded().as_bytes();
                let mut writer = EncodingWriter::new(Vec::new(), c.encoding.new_encoder());
                {
                    let mut writer = writer
                        .with_unmappable_handler(|e, w| write!(w, "&#{};", u32::from(e.value())));
                    while !src.is_empty() {
                        match writer.write(&src[..1]) {
                            Ok(1) => src = &src[1..],
                            _ => unreachable!(),
                        }
                    }
                    writer.flush().unwrap();
                }
                let (dst, _, _) = writer.finish();
                dst
            };
            assert_eq!(actual_handler_byte_by_byte, c.encoded());
        }
    });
}

static TEXT: &str = include_str!("text_ja.txt");

thread_local! {
    static TEST_CASES: Vec<TestCase<&'static str, Vec<u8>>> = {
        [SHIFT_JIS, EUC_JP, ISO_2022_JP]
            .into_iter()
            .map(|encoding| {
                let mut encoder = encoding.new_encoder();
                let mut dst = Vec::with_capacity(
                    encoder
                        .max_buffer_length_from_utf8_without_replacement(TEXT.len())
                        .unwrap(),
                );
                let (result, consumed) =
                    encoder.encode_from_utf8_to_vec_without_replacement(TEXT, &mut dst, true);
                assert_eq!(result, encoding_rs::EncoderResult::InputEmpty);
                assert_eq!(consumed, TEXT.len());
                dst.shrink_to_fit();

                TestCase {
                    encoding,
                    decoded_bytes: TEXT,
                    encoded_bytes: dst,
                }
            })
            .collect()
    };

    static TEST_CASES_UNMAPPABLE: Vec<TestCase<&'static str, Vec<u8>>> = {
        [BIG5, EUC_KR, ISO_8859_15]
            .into_iter()
            .map(|encoding| {
                let mut encoder = encoding.new_encoder();
                let mut dst = Vec::with_capacity(
                    encoder
                        .max_buffer_length_from_utf8_if_no_unmappables(TEXT.len())
                        .unwrap()
                        * 4,
                );
                let (result, consumed, replaced) =
                    encoder.encode_from_utf8_to_vec(TEXT, &mut dst, true);
                assert_eq!(result, encoding_rs::CoderResult::InputEmpty);
                assert_eq!(consumed, TEXT.len());
                assert!(replaced);
                dst.shrink_to_fit();

                TestCase {
                    encoding,
                    decoded_bytes: TEXT,
                    encoded_bytes: dst,
                }
            })
            .collect()
    };
}

struct TestCase<D, E> {
    encoding: &'static encoding_rs::Encoding,
    decoded_bytes: D,
    encoded_bytes: E,
}

impl<D: AsRef<str>, E: AsRef<[u8]>> TestCase<D, E> {
    fn decoded(&self) -> &str {
        self.decoded_bytes.as_ref()
    }

    fn encoded(&self) -> &[u8] {
        self.encoded_bytes.as_ref()
    }
}
