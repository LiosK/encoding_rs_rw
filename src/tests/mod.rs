mod ja;

#[test]
fn ex_readme_examples() -> std::io::Result<()> {
    use std::io::prelude::*;

    use encoding_rs::{BIG5, SHIFT_JIS};

    use super::{DecodingReader, EncodingWriter};

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

    Ok(())
}
