//! The ring: a first-in first-out queue of fixed-size records in a block of `capacity * record` bytes. Invariants:
//! `len <= capacity`; the oldest record is at `head`, the next push goes to `(head + len) % capacity`; records pop
//! in the order they were pushed.

use crate::error::Error;
use crate::storage::{Storage, fit, rec, rec_mut};

/// A bounded FIFO of fixed-size records. See the module comment.
#[derive(Debug)]
pub struct Ring {
    mem: Storage,
    cap: usize,
    size: usize,
    head: usize,
    len: usize,
}

impl Ring {
    /// The bytes of block a ring of `capacity` records of `record` bytes needs. Saturates at `usize::MAX`.
    pub const fn bytes(capacity: usize, record: usize) -> usize {
        capacity.saturating_mul(record)
    }

    /// Makes an empty ring over `mem`. Refuses a block smaller than [`Self::bytes`].
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn new(mem: Storage, capacity: usize, record: usize) -> Result<Self, Error> {
        fit(&mem, Self::bytes(capacity, record))?;
        Ok(Self {
            mem,
            cap: capacity,
            size: record,
            head: 0,
            len: 0,
        })
    }

    /// The records held.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether no record is held.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The most records the ring holds.
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Whether the next push is refused.
    pub fn is_full(&self) -> bool {
        self.len == self.cap
    }

    /// Drops every record.
    pub fn clear(&mut self) {
        self.head = 0;
        self.len = 0;
    }

    fn at(&self, i: usize) -> usize {
        // `head < cap`, so the room before the wrap cannot overflow even for a record of 0 bytes and a huge capacity.
        let room = self.cap - self.head;
        if i < room { self.head + i } else { i - room }
    }

    /// Adds `record` at the back. Refuses when full, and a record of the wrong length.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn push(&mut self, record: &[u8]) -> Result<(), Error> {
        if record.len() != self.size {
            return Err(Error::Length);
        }
        if self.is_full() {
            return Err(Error::Full);
        }
        let at = self.at(self.len);
        rec_mut(self.mem.as_mut_slice(), at, self.size)
            .ok_or(Error::Position)?
            .copy_from_slice(record);
        self.len += 1;
        Ok(())
    }

    /// The oldest record, without removing it.
    pub fn peek(&self) -> Option<&[u8]> {
        self.get(0)
    }

    /// The `i`th record from the front (0 is the oldest).
    pub fn get(&self, i: usize) -> Option<&[u8]> {
        (i < self.len).then(|| rec(self.mem.as_slice(), self.at(i), self.size))
    }

    /// Removes and returns the oldest record. The bytes stay valid until the next push.
    pub fn pop(&mut self) -> Option<&[u8]> {
        if self.len == 0 {
            return None;
        }
        let old = self.head;
        self.head = if old + 1 == self.cap { 0 } else { old + 1 };
        self.len -= 1;
        Some(rec(self.mem.as_slice(), old, self.size))
    }

    /// Every record from the oldest.
    pub fn iter(&self) -> impl Iterator<Item = &[u8]> + '_ {
        (0..self.len).filter_map(move |i| self.get(i))
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn a_ring_of_empty_records_wraps_without_overflowing_its_index() {
        let mut r = Ring::new(Storage::zeroed(0).unwrap(), usize::MAX, 0).unwrap();
        r.head = usize::MAX - 1;
        r.len = 2;
        assert_eq!(r.push(&[]), Ok(()));
        assert_eq!(r.get(2), Some(&[][..]));
        assert_eq!(r.at(2), 1);
        assert_eq!(r.len(), 3);
    }
}
