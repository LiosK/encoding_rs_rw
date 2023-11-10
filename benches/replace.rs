//! Compares the throughput of replacement of malformed bytes and unmappable characters.

#![feature(test)]

extern crate test;

use std::io::{Read, Write};

use encoding_rs::{ISO_8859_15 as Enc, UTF_8};
use encoding_rs_rw::{DecodingReader, EncodingWriter, MalformedError, UnmappableError};

const N_READ: usize = 32 * 1024;

#[bench]
fn reader_lossy(b: &mut test::Bencher) {
    let src = test::black_box(vec![0xffu8; N_READ]);
    let expected = "�".repeat(N_READ);
    b.iter(|| {
        let mut dst = String::new();
        let mut reader = DecodingReader::new(&src[..], UTF_8.new_decoder());
        reader.lossy().read_to_string(&mut dst).unwrap();

        assert_eq!(dst, expected);
    });
}

#[bench]
fn reader_manual(b: &mut test::Bencher) {
    let src = test::black_box(vec![0xffu8; N_READ]);
    let expected = "�".repeat(N_READ);
    b.iter(|| {
        let mut dst = String::new();
        let mut reader = DecodingReader::new(&src[..], UTF_8.new_decoder());
        while let Err(e) = reader.read_to_string(&mut dst) {
            if MalformedError::wrapped_in(&e).is_some() {
                dst.push('�');
            } else {
                unreachable!();
            }
        }

        assert_eq!(dst, expected);
    });
}

#[bench]
fn raw_decoder(b: &mut test::Bencher) {
    let src = test::black_box(vec![0xffu8; N_READ]);
    let expected = "�".repeat(N_READ);
    b.iter(|| {
        let mut dst = String::new();
        let mut decoder = UTF_8.new_decoder();
        dst.reserve(decoder.max_utf8_buffer_length(src.len()).unwrap());
        let (result, _, _) = decoder.decode_to_string(&src, &mut dst, true);
        assert!(matches!(result, encoding_rs::CoderResult::InputEmpty));

        assert_eq!(dst, expected);
    });
}

const TEXT: &str = include_str!("text_ja.txt");

#[cfg(feature = "unstable-handler")]
#[bench]
fn writer_with_handler(b: &mut test::Bencher) {
    let src = test::black_box(TEXT);
    let expected = encoder_expected(TEXT);
    b.iter(|| {
        let mut writer = EncodingWriter::new(Vec::new(), Enc.new_encoder());
        {
            let mut writer =
                writer.with_unmappable_handler(|e, w| write!(w, "&#{};", u32::from(e.value())));
            write!(writer, "{}", src).unwrap();
            writer.flush().unwrap();
        }

        assert_eq!(writer.writer_ref(), &expected);
    });
}

#[bench]
fn writer_manual(b: &mut test::Bencher) {
    let src = test::black_box(TEXT);
    let expected = encoder_expected(TEXT);
    b.iter(|| {
        let mut src = src;
        let mut writer = EncodingWriter::new(Vec::new(), Enc.new_encoder());
        while !src.is_empty() {
            match writer.write_str(src) {
                Ok(0) => unreachable!(),
                Ok(consumed) => src = &src[consumed..],
                Err(e) => {
                    let c = UnmappableError::wrapped_in(&e).unwrap().value();
                    write!(writer.passthrough(), "&#{};", u32::from(c)).unwrap();
                }
            }
        }
        if let Err(e) = writer.flush() {
            let c = UnmappableError::wrapped_in(&e).unwrap().value();
            write!(writer.passthrough(), "&#{};", u32::from(c)).unwrap();
        }

        assert_eq!(writer.writer_ref(), &expected);
    });
}

#[bench]
fn raw_encoder(b: &mut test::Bencher) {
    let src = test::black_box(TEXT);
    let expected = encoder_expected(TEXT);
    b.iter(|| {
        let dst = encoder_expected(src);

        assert_eq!(dst, expected);
    });
}

fn encoder_expected(src: &str) -> Vec<u8> {
    let mut dst = Vec::new();
    let mut encoder = Enc.new_encoder();
    dst.reserve(src.len() * 4);
    let (result, _, _) = encoder.encode_from_utf8_to_vec(src, &mut dst, true);
    assert!(matches!(result, encoding_rs::CoderResult::InputEmpty));
    dst
}
