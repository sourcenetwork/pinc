//! A bounded, forward-only cursor over borrowed bytes.
//!
//! Invariants: every read checks bounds first and, on failure, consumes nothing and returns
//! [`WireError::Truncated`]; returned slices borrow the original input, never the reader.

use crate::error::WireError;
use crate::varint;

/// A cursor over `&'a [u8]` that hands out in-place views.
#[derive(Debug, Clone, Copy)]
pub struct Reader<'a> {
    rest: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    /// A reader at the start of `buf`.
    pub const fn new(buf: &'a [u8]) -> Self {
        Self { rest: buf, pos: 0 }
    }

    /// Bytes not yet consumed.
    pub const fn remaining(&self) -> usize {
        self.rest.len()
    }

    /// Bytes consumed so far.
    pub const fn position(&self) -> usize {
        self.pos
    }

    /// Whether every byte has been consumed.
    pub const fn is_empty(&self) -> bool {
        self.rest.is_empty()
    }

    /// The next byte, without consuming it.
    ///
    /// # Errors
    /// [`WireError::Truncated`] at the end of input.
    pub fn peek_u8(&self) -> Result<u8, WireError> {
        self.rest.first().copied().ok_or(WireError::Truncated { needed: 1 })
    }

    /// Consume and return the next `n` bytes.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if fewer than `n` bytes remain.
    pub fn read_bytes(&mut self, n: usize) -> Result<&'a [u8], WireError> {
        let (head, tail) = self.rest.split_at_checked(n).ok_or(WireError::Truncated {
            needed: n.saturating_sub(self.rest.len()),
        })?;
        self.rest = tail;
        self.pos = self.pos.saturating_add(n);
        Ok(head)
    }

    /// Consume and return the next `N` bytes as an array.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if fewer than `N` bytes remain.
    pub fn read_array<const N: usize>(&mut self) -> Result<[u8; N], WireError> {
        let arr = self.rest.first_chunk::<N>().copied().ok_or(WireError::Truncated {
            needed: N.saturating_sub(self.rest.len()),
        })?;
        self.read_bytes(N)?;
        Ok(arr)
    }

    /// Consume one byte.
    ///
    /// # Errors
    /// [`WireError::Truncated`] at the end of input.
    pub fn read_u8(&mut self) -> Result<u8, WireError> {
        let [b] = self.read_array::<1>()?;
        Ok(b)
    }

    /// Consume a big-endian `u16`.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if fewer than 2 bytes remain.
    pub fn read_u16(&mut self) -> Result<u16, WireError> {
        self.read_array().map(u16::from_be_bytes)
    }

    /// Consume a big-endian `u32`.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if fewer than 4 bytes remain.
    pub fn read_u32(&mut self) -> Result<u32, WireError> {
        self.read_array().map(u32::from_be_bytes)
    }

    /// Consume a big-endian `u64`.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if fewer than 8 bytes remain.
    pub fn read_u64(&mut self) -> Result<u64, WireError> {
        self.read_array().map(u64::from_be_bytes)
    }

    /// Consume a multiformats varint.
    ///
    /// # Errors
    /// Any [`varint::decode`] error; nothing is consumed on failure.
    pub fn read_varint(&mut self) -> Result<u64, WireError> {
        let (value, len) = varint::decode(self.rest)?;
        self.read_bytes(len)?;
        Ok(value)
    }
}
