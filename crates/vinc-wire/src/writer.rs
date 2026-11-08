//! A bounded, forward-only writer into a caller buffer.
//!
//! Invariants: a write that does not fit fails with [`WireError::BufferTooSmall`] and leaves the written content
//! and position unchanged; the writer never allocates.

use crate::error::WireError;
use crate::varint;

/// A cursor that fills a caller-provided `&mut [u8]`.
#[derive(Debug)]
pub struct Writer<'a> {
    buf: &'a mut [u8],
    pos: usize,
}

impl<'a> Writer<'a> {
    /// A writer at the start of `buf`.
    pub const fn new(buf: &'a mut [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    /// The bytes written so far.
    pub fn written(&self) -> &[u8] {
        self.buf.get(..self.pos).unwrap_or_default()
    }

    /// Room left in the buffer.
    pub const fn remaining(&self) -> usize {
        self.buf.len().saturating_sub(self.pos)
    }

    /// Check that `n` more bytes fit.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] naming the shortfall.
    pub const fn ensure(&self, n: usize) -> Result<(), WireError> {
        if n <= self.remaining() {
            Ok(())
        } else {
            Err(WireError::BufferTooSmall {
                needed: n - self.remaining(),
            })
        }
    }

    /// Append `bytes`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if they do not fit.
    pub fn put_slice(&mut self, bytes: &[u8]) -> Result<(), WireError> {
        self.ensure(bytes.len())?;
        let end = self.pos.saturating_add(bytes.len());
        self.buf
            .get_mut(self.pos..end)
            .ok_or(WireError::BufferTooSmall { needed: bytes.len() })?
            .copy_from_slice(bytes);
        self.pos = end;
        Ok(())
    }

    /// Append one byte.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn put_u8(&mut self, v: u8) -> Result<(), WireError> {
        self.put_slice(&[v])
    }

    /// Append a big-endian `u16`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn put_u16(&mut self, v: u16) -> Result<(), WireError> {
        self.put_slice(&v.to_be_bytes())
    }

    /// Append a big-endian `u32`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn put_u32(&mut self, v: u32) -> Result<(), WireError> {
        self.put_slice(&v.to_be_bytes())
    }

    /// Append a big-endian `u64`.
    ///
    /// # Errors
    /// [`WireError::BufferTooSmall`] if it does not fit.
    pub fn put_u64(&mut self, v: u64) -> Result<(), WireError> {
        self.put_slice(&v.to_be_bytes())
    }

    /// Append a multiformats varint.
    ///
    /// # Errors
    /// [`WireError::VarintOverflow`] for 2^63 or more, [`WireError::BufferTooSmall`] if it does not fit.
    pub fn put_varint(&mut self, v: u64) -> Result<(), WireError> {
        let rest = self.buf.get_mut(self.pos..).unwrap_or_default();
        let n = varint::encode(v, rest)?;
        self.pos = self.pos.saturating_add(n);
        Ok(())
    }
}
