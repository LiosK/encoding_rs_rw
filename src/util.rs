use std::io;

/// A `Vec`-like struct that handles a tiny stack-allocated byte array.
#[derive(Debug, Default)]
pub(crate) struct MiniBuffer {
    len: u8,
    buf: [u8; 7],
}

impl AsRef<[u8]> for MiniBuffer {
    fn as_ref(&self) -> &[u8] {
        &self.buf[..self.len()]
    }
}

impl MiniBuffer {
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn len(&self) -> usize {
        self.len.into()
    }

    pub fn advance(&mut self, n: usize) {
        debug_assert!(self.len() + n <= self.buf.len());
        self.len = self.buf.len().min(self.len() + n) as u8;
    }

    pub fn remove_front(&mut self, count: usize) {
        debug_assert!(count <= self.len());
        if count < self.len() {
            self.buf.copy_within(count.., 0);
            self.len -= count as u8;
        } else {
            self.len = 0;
        };
    }

    pub fn unfilled(&mut self) -> &mut [u8] {
        &mut self.buf[self.len.into()..]
    }

    /// Reads bytes from the internal buffer to fill the specified buffer, returning the number of
    /// bytes read.
    pub fn read_to_slice(&mut self, buf: &mut [u8]) -> usize {
        let n = self.len().min(buf.len());
        buf[..n].copy_from_slice(&self.buf[..n]);
        self.remove_front(n);
        n
    }

    /// Writes as many bytes as possible pulled from a reader into the spare capacity.
    pub fn fill_from_reader(&mut self, reader: &mut impl io::Read) -> io::Result<()> {
        while !self.unfilled().is_empty() {
            match reader.read(self.unfilled()) {
                Ok(0) => break,
                Ok(n) => self.advance(n),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Writes as many bytes as possible copied from a slice into the spare capacity, returning the
    /// number of bytes consumed.
    pub fn fill_from_slice(&mut self, buf: &[u8]) -> usize {
        let n = self.unfilled().len().min(buf.len());
        self.unfilled()[..n].copy_from_slice(&buf[..n]);
        self.advance(n);
        n
    }
}
