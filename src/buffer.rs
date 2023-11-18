use std::{error, fmt, io, mem, ptr};

use super::writer::BufferedWrite;

/// A [`BufWriter`](io::BufWriter)-like type that exposes its unfilled capacity as a slice through
/// [`BufferedWrite`] trait.
#[derive(Debug)]
pub struct DefaultBuffer<W: io::Write> {
    buffer: Vec<u8>,
    panicked: bool,
    inner: W,
}

impl<W: io::Write> DefaultBuffer<W> {
    pub(crate) fn with_capacity(capacity: usize, inner: W) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            panicked: false,
            inner,
        }
    }

    /// Returns a reference to the unwritten buffered data.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer
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
        let (buffer, panicked, inner) = unsafe {
            let m = mem::ManuallyDrop::new(self);
            (
                ptr::read(&m.buffer),
                ptr::read(&m.panicked),
                ptr::read(&m.inner),
            )
        };
        if !panicked {
            (inner, Ok(buffer))
        } else {
            (inner, Err(WriterPanicked { buffer }))
        }
    }

    /// Writes the buffered data into the underlying writer.
    fn flush_buffer(&mut self) -> io::Result<()> {
        // A guard struct to make sure to remove consumed bytes from the buffer when dropped.
        struct PanicGuard<'a> {
            consumed: usize,
            buffer: &'a mut Vec<u8>,
        }

        impl Drop for PanicGuard<'_> {
            fn drop(&mut self) {
                if self.consumed < self.buffer.len() {
                    self.buffer.drain(..self.consumed);
                } else {
                    self.buffer.clear();
                }
            }
        }

        let mut g = PanicGuard {
            consumed: 0,
            buffer: &mut self.buffer,
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
        if buf.len() > capacity && self.buffer.is_empty() {
            // bypass the internal buffer if the input buffer is large
            self.panicked = true;
            let ret = self.inner.write(buf);
            self.panicked = false;
            ret
        } else {
            let n = buf.len().min(capacity);
            // SAFETY: `&[T]` and `&[MaybeUninit<T>]` have the same layout
            self.unfilled()[..n].copy_from_slice(unsafe { mem::transmute(&buf[..n]) });
            // SAFETY: `n` elements have just been initialized by `copy_from_slice`
            unsafe { self.advance(n) };
            Ok(n)
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        self.flush_buffer()?;
        self.inner.flush()
    }
}

impl<W: io::Write> BufferedWrite for DefaultBuffer<W> {
    fn unfilled(&mut self) -> &mut [mem::MaybeUninit<u8>] {
        self.buffer.spare_capacity_mut()
    }

    unsafe fn advance(&mut self, n: usize) {
        assert!(self.buffer.len() + n <= self.buffer.capacity());
        self.buffer.set_len(self.buffer.len() + n);
    }

    fn try_reserve(&mut self, minimum: usize, size_hint: Option<usize>) -> io::Result<()> {
        if self.buffer.capacity() - self.buffer.len()
            < size_hint.map_or(minimum, |n| n.max(minimum))
        {
            self.flush_buffer()?;
            if self.buffer.capacity() - self.buffer.len() < minimum {
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
