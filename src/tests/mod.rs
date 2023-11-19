mod ja;

// implement `AsRef<[u8]>` to test `buffer_ref` and `writer_ref` transparently

impl<B> AsRef<[u8]> for super::EncodingWriter<B>
where
    B: AsRef<[u8]> + super::misc::BufferedWrite,
{
    fn as_ref(&self) -> &[u8] {
        self.buffer_ref().as_ref()
    }
}

impl<W> AsRef<[u8]> for super::misc::DefaultBuffer<W>
where
    W: AsRef<[u8]> + std::io::Write,
{
    fn as_ref(&self) -> &[u8] {
        self.get_ref().as_ref()
    }
}
