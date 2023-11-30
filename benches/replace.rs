//! Compares the throughput of replacing malformed bytes and unmappable characters.

#![feature(test)]

extern crate test;

use std::io::{self, Read, Write};

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
fn reader_manual_naive(b: &mut test::Bencher) {
    let src = test::black_box(vec![0xffu8; N_READ]);
    let expected = "�".repeat(N_READ);
    b.iter(|| {
        let mut dst = String::new();
        let mut reader = DecodingReader::new(&src[..], UTF_8.new_decoder());
        loop {
            match reader.read_to_string(&mut dst) {
                Ok(_) => break,
                Err(e) if MalformedError::wrapped_in(&e).is_some() => dst.push('�'),
                Err(_) => unreachable!(),
            }
        }

        assert_eq!(dst, expected);
    });
}

/// Manages the buffer manually because repeatedly calling `read_to_string` seems inefficient.
#[bench]
fn reader_manual_optimized(b: &mut test::Bencher) {
    struct PanicGuard<'a> {
        len: usize,
        buf: &'a mut Vec<u8>,
    }
    impl Drop for PanicGuard<'_> {
        fn drop(&mut self) {
            unsafe { self.buf.set_len(self.len) };
        }
    }

    let src = test::black_box(vec![0xffu8; N_READ]);
    let expected = "�".repeat(N_READ);
    b.iter(|| {
        let mut dst = String::new();
        let mut reader = DecodingReader::new(&src[..], UTF_8.new_decoder());
        {
            let mut g = PanicGuard {
                len: dst.len(),
                buf: unsafe { dst.as_mut_vec() },
            };
            loop {
                if g.buf.capacity() - g.len < 32 {
                    g.buf.reserve(32);
                    unsafe { g.buf.set_len(g.buf.capacity()) };
                }

                let buf = &mut g.buf[g.len..];
                match reader.read(buf) {
                    Ok(0) => break,
                    Ok(n) => g.len += n,
                    Err(e) if MalformedError::wrapped_in(&e).is_some() => {
                        buf[.."�".len()].copy_from_slice("�".as_bytes());
                        g.len += "�".len();
                    }
                    Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                    Err(_) => unreachable!(),
                }
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

#[bench]
fn writer_with_handler(b: &mut test::Bencher) {
    let src = test::black_box(TEXT);
    let expected = encoder_expected(TEXT);
    b.iter(|| {
        let mut writer = EncodingWriter::new(Vec::new(), Enc.new_encoder());
        {
            let mut writer = writer.with_unmappable_handler(|e, w| write_ncr(e.value(), w));
            write!(writer, "{}", src).unwrap();
            writer.flush().unwrap();
        }

        assert_eq!(writer.writer_ref(), &expected);
    });
}

#[bench]
fn writer_with_handler_zero_copy(b: &mut test::Bencher) {
    let src = test::black_box(TEXT);
    let expected = encoder_expected(TEXT);
    b.iter(|| {
        let mut writer = EncodingWriter::with_vec(Vec::new(), Enc.new_encoder());
        {
            let mut writer = writer.with_unmappable_handler(|e, w| write_ncr(e.value(), w));
            write!(writer, "{}", src).unwrap();
            writer.flush().unwrap();
        }

        assert_eq!(writer.buffer_ref().as_ref(), &expected);
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
                    write_ncr(c, &mut writer.passthrough()).unwrap();
                }
            }
        }
        if let Err(e) = writer.flush() {
            let c = UnmappableError::wrapped_in(&e).unwrap().value();
            write_ncr(c, &mut writer.passthrough()).unwrap();
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

/// Writes a character into a writer as a HTML numeric character reference without creating the
/// formatter structure.
fn write_ncr(c: char, w: &mut impl io::Write) -> io::Result<()> {
    let mut num = u32::from(c);
    let mut buffer = [0; 10]; // "&#1114111;" (char::MAX)
    let mut pos = buffer.len() - 1;
    buffer[pos] = b';';
    pos -= 1;
    buffer[pos] = (num % 10) as u8 + b'0';
    pos -= 1;
    while num >= 10 {
        num /= 10;
        buffer[pos] = (num % 10) as u8 + b'0';
        pos -= 1;
    }
    buffer[pos] = b'#';
    pos -= 1;
    buffer[pos] = b'&';

    w.write_all(&buffer[pos..])
}
