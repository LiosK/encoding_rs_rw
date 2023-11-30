use std::{error, fmt, io, mem, ptr};

use super::writer::BufferedWrite;

/// A [`BufWriter`](io::BufWriter)-like type that exposes its unfilled capacity as a slice through
/// [`BufferedWrite`] trait.
///
/// Like `BufWriter`, this structure stores the written bytes in its internal buffer and writes
/// them into the underlying writer when dropped or when the buffer becomes full.
#[derive(Debug)]
pub struct DefaultBuffer<W: io::Write> {
    buffer: Vec<u8>,
    cursor: usize,
    panicked: bool,
    inner: W,
}

impl<W: io::Write> DefaultBuffer<W> {
    pub(crate) fn with_capacity(capacity: usize, inner: W) -> Self {
        let mut buffer = vec![0; capacity];
        buffer.resize(buffer.capacity(), 0);
        Self {
            buffer,
            cursor: 0,
            panicked: false,
            inner,
        }
    }

    /// Returns a reference to the unwritten buffered data.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer[..self.cursor]
    }

    /// Returns a reference to the underlying writer.
    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    /// Disassembles the structure and returns the underlying writer and unwritten buffered data.
    ///
    /// If the underlying writer experienced panic in a previous call to write, this method wraps
    /// the buffered data with the [`WriterPanicked`] error to signal the fact that the buffered
    /// data might have been partly written to the underlying writer.
    ///
    /// This method does not attempt to flush the buffer.
    pub fn into_parts(self) -> (W, Result<Vec<u8>, WriterPanicked>) {
        // SAFETY: ok because all the fields are taken out of the scope while `ManuallyDrop`
        // guarantees that they are not double-dropped
        let (mut buffer, cursor, panicked, inner) = unsafe {
            let m = mem::ManuallyDrop::new(self);
            (
                ptr::read(&m.buffer),
                ptr::read(&m.cursor),
                ptr::read(&m.panicked),
                ptr::read(&m.inner),
            )
        };
        buffer.truncate(cursor);
        if !panicked {
            (inner, Ok(buffer))
        } else {
            (inner, Err(WriterPanicked { buffer }))
        }
    }

    fn is_empty(&self) -> bool {
        self.cursor == 0
    }

    /// Writes the buffered data into the underlying writer.
    pub(crate) fn flush_buffer(&mut self) -> io::Result<()> {
        // A guard struct to make sure to remove consumed bytes from the buffer when dropped.
        struct PanicGuard<'a> {
            consumed: usize,
            buffer: &'a mut [u8],
            cursor: &'a mut usize,
        }

        impl Drop for PanicGuard<'_> {
            fn drop(&mut self) {
                if self.consumed < self.buffer.len() {
                    self.buffer.copy_within(self.consumed.., 0);
                    *self.cursor -= self.consumed;
                } else {
                    *self.cursor = 0;
                }
            }
        }

        let mut g = PanicGuard {
            consumed: 0,
            buffer: &mut self.buffer[..self.cursor],
            cursor: &mut self.cursor,
        };

        while g.consumed < g.buffer.len() {
            self.panicked = true;
            let ret = self.inner.write(&g.buffer[g.consumed..]);
            self.panicked = false;

            match ret {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write buffered data to writer",
                    ));
                }
                Ok(n) => g.consumed += n,
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        Ok(())
    }
}

impl<W: io::Write> Drop for DefaultBuffer<W> {
    fn drop(&mut self) {
        // don't double-flush the buffer when the inner writer panicked in a call to write
        if !self.panicked {
            let _ = self.flush_buffer();
        }
    }
}

impl<W: io::Write> io::Write for DefaultBuffer<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.try_reserve(1, Some(buf.len()))?;
        let capacity = self.unfilled().len();
        if buf.len() > capacity && self.is_empty() {
            // bypass the internal buffer if the input buffer is large
            self.panicked = true;
            let ret = self.inner.write(buf);
            self.panicked = false;
            ret
        } else {
            let n = buf.len().min(capacity);
            self.unfilled()[..n].copy_from_slice(&buf[..n]);
            self.advance(n);
            Ok(n)
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flush_buffer()?;
        self.inner.flush()
    }
}

impl<W: io::Write> BufferedWrite for DefaultBuffer<W> {
    fn unfilled(&mut self) -> &mut [u8] {
        &mut self.buffer[self.cursor..]
    }

    fn advance(&mut self, n: usize) {
        assert!(self.cursor + n <= self.buffer.len());
        self.cursor += n;
    }

    fn try_reserve(&mut self, minimum: usize, size_hint: Option<usize>) -> io::Result<()> {
        if self.unfilled().len() < size_hint.map_or(minimum, |n| n.max(minimum)) {
            self.flush_buffer()?;
            if self.unfilled().len() < minimum {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    "failed to reserve minimum buffer capacity",
                ));
            }
        }
        Ok(())
    }
}

/// The error returned by [`DefaultBuffer::into_parts`] when the underlying writer experienced
/// panic in a call to write.
#[derive(Debug)]
pub struct WriterPanicked {
    buffer: Vec<u8>,
}

impl WriterPanicked {
    /// Returns the buffered data, which might have been partly written during a previous write
    /// call that panicked.
    pub fn into_inner(self) -> Vec<u8> {
        self.buffer
    }
}

impl fmt::Display for WriterPanicked {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "underlying writer experienced panic")
    }
}

impl error::Error for WriterPanicked {}
