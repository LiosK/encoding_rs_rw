use std::{io, mem, ptr};

use super::writer::BufferedWrite;

/// A [`BufWriter`](io::BufWriter)-like type that exposes its unfilled capacity as a slice through
/// [`BufferedWrite`] trait.
#[derive(Debug)]
pub struct BufferedWriter<W: io::Write> {
    buffer: Vec<u8>,
    panicked: bool,
    inner: W,
}

impl<W: io::Write> BufferedWriter<W> {
    pub(crate) fn with_capacity(capacity: usize, inner: W) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            panicked: false,
            inner,
        }
    }

    /// Returns a reference to the buffered data.
    pub fn buffer(&self) -> &[u8] {
        &self.buffer
    }

    /// Returns a reference to the underlying writer.
    pub fn get_ref(&self) -> &W {
        &self.inner
    }

    fn _into_parts(self) -> (W, Vec<u8>) {
        // destruct `self`, moving out some fields and dropping the rest
        unsafe {
            let mut m = mem::ManuallyDrop::new(self);
            ptr::drop_in_place(&mut m.panicked);
            (ptr::read(&m.inner), ptr::read(&m.buffer))
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

impl<W: io::Write> Drop for BufferedWriter<W> {
    fn drop(&mut self) {
        // don't double-flush the buffer when the inner writer panicked in a call to write
        if !self.panicked {
            let _ = self.flush_buffer();
        }
    }
}

impl<W: io::Write> io::Write for BufferedWriter<W> {
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

impl<W: io::Write> BufferedWrite for BufferedWriter<W> {
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
