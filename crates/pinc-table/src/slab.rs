//! The sorted slab: a keyed table that walks in key order, as a `BTreeMap` does, without a node to allocate.
//!
//! Records (key bytes then value bytes, fixed sizes) sit dense in slots `0..len`; an index of slot numbers in key
//! order follows them in the same block. The index entries are 2 bytes wide up to 65,535 records and 4 bytes above,
//! chosen once when the slab is made. A lookup binary-searches the index; an insert appends the record and shifts
//! the index; a remove shifts the index and moves the last record into the hole; `retain` removes many in one pass.
//! Keys compare as byte strings: a caller encodes an unsigned integer key big-endian to get numeric order (a signed
//! one needs its sign bit flipped). A key of varying length is padded to the fixed length with a final length byte
//! appended: that is injective, and bytewise order is then the order of the padded keys (padding alone would merge
//! "a" and "a\0"). Invariants: the index holds each slot in `0..len` exactly once, in strictly ascending key order;
//! no two records share a key; `len <= capacity`.

use core::cmp::Ordering;

use crate::error::Error;
use crate::storage::{Storage, fit, rd_w, rec, rec_mut, wr_w};

/// A keyed table of fixed-size records that walks in key order. See the module comment.
#[derive(Debug)]
pub struct SortedSlab {
    mem: Storage,
    cap: usize,
    klen: usize,
    vlen: usize,
    len: usize,
    /// The bytes of one index entry, from [`Self::width`].
    w: usize,
}

impl SortedSlab {
    /// The bytes of one index entry for a slab of `capacity` records: 2 up to 65,535, 4 above.
    const fn width(capacity: usize) -> usize {
        if capacity <= 65_535 { 2 } else { 4 }
    }

    /// The bytes of block a slab of `capacity` records of `key_len` plus `val_len` bytes needs (the records, then one
    /// index entry of 2 bytes up to 65,535 records and 4 above, per record). Saturates at `usize::MAX`, which no
    /// block satisfies.
    pub const fn bytes(capacity: usize, key_len: usize, val_len: usize) -> usize {
        capacity.saturating_mul(key_len.saturating_add(val_len).saturating_add(Self::width(capacity)))
    }

    /// Makes an empty slab over `mem`. Refuses a block smaller than [`Self::bytes`], a capacity the index
    /// cannot number (above `u32::MAX`), and a key and value whose lengths sum past `usize::MAX`.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn new(mem: Storage, capacity: usize, key_len: usize, val_len: usize) -> Result<Self, Error> {
        if u32::try_from(capacity).is_err() || key_len.checked_add(val_len).is_none() {
            return Err(Error::Capacity);
        }
        fit(&mem, Self::bytes(capacity, key_len, val_len))?;
        Ok(Self {
            mem,
            cap: capacity,
            klen: key_len,
            vlen: val_len,
            len: 0,
            w: Self::width(capacity),
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

    /// The most records the slab holds.
    pub fn capacity(&self) -> usize {
        self.cap
    }

    /// Whether the next insert of a new key is refused.
    pub fn is_full(&self) -> bool {
        self.len == self.cap
    }

    /// Drops every record.
    pub fn clear(&mut self) {
        self.len = 0;
    }

    fn rsize(&self) -> usize {
        self.klen + self.vlen
    }

    fn slot(&self, pos: usize) -> usize {
        let idx = self.mem.as_slice().get(self.cap * self.rsize()..).unwrap_or(&[]);
        rd_w(idx, pos, self.w)
    }

    fn set_slot(&mut self, pos: usize, slot: usize) {
        let (at, w) = (self.cap * self.rsize(), self.w);
        if let Some(idx) = self.mem.as_mut_slice().get_mut(at..) {
            wr_w(idx, pos, w, slot);
        }
    }

    fn key_of(&self, slot: usize) -> &[u8] {
        rec(self.mem.as_slice(), slot, self.rsize())
            .get(..self.klen)
            .unwrap_or(&[])
    }

    /// `Ok(position)` of the key, or `Err(position)` it would be inserted at.
    fn search(&self, key: &[u8]) -> Result<usize, usize> {
        let (mut lo, mut hi) = (0, self.len);
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            match self.key_of(self.slot(mid)).cmp(key) {
                Ordering::Less => lo = mid + 1,
                Ordering::Greater => hi = mid,
                Ordering::Equal => return Ok(mid),
            }
        }
        Err(lo)
    }

    /// The key and value at `pos` in key order.
    pub fn entry(&self, pos: usize) -> Option<(&[u8], &[u8])> {
        if pos >= self.len {
            return None;
        }
        rec(self.mem.as_slice(), self.slot(pos), self.rsize()).split_at_checked(self.klen)
    }

    /// The value stored under `key`.
    pub fn get(&self, key: &[u8]) -> Option<&[u8]> {
        self.search(key).ok().and_then(|p| self.entry(p)).map(|(_, v)| v)
    }

    /// The value stored under `key`, to change in place.
    pub fn get_mut(&mut self, key: &[u8]) -> Option<&mut [u8]> {
        let p = self.search(key).ok()?;
        let (s, klen, size) = (self.slot(p), self.klen, self.rsize());
        rec_mut(self.mem.as_mut_slice(), s, size)?.get_mut(klen..)
    }

    /// Whether `key` is held.
    pub fn contains(&self, key: &[u8]) -> bool {
        self.search(key).is_ok()
    }

    /// The first entry, the one with the least key.
    pub fn first(&self) -> Option<(&[u8], &[u8])> {
        self.entry(0)
    }

    /// The last entry, the one with the greatest key.
    pub fn last(&self) -> Option<(&[u8], &[u8])> {
        self.entry(self.len.checked_sub(1)?)
    }

    /// The first entry whose key is `key` or after it.
    pub fn first_at_or_after(&self, key: &[u8]) -> Option<(&[u8], &[u8])> {
        self.entry(self.search(key).unwrap_or_else(|p| p))
    }

    /// The first entry whose key is after `key`: the cursor step. A caller walks while it removes and
    /// inserts by holding the last key it saw and asking for the next.
    pub fn next_after(&self, key: &[u8]) -> Option<(&[u8], &[u8])> {
        self.entry(match self.search(key) {
            Ok(p) => p + 1,
            Err(p) => p,
        })
    }

    /// Every entry in key order.
    pub fn iter(&self) -> impl Iterator<Item = (&[u8], &[u8])> + '_ {
        (0..self.len).filter_map(move |p| self.entry(p))
    }

    /// Stores `val` under `key`: replaces the value of a key held, otherwise adds the record. Returns
    /// whether a record was replaced. Refuses a new key when full, and a key or value of the wrong length.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn insert(&mut self, key: &[u8], val: &[u8]) -> Result<bool, Error> {
        if key.len() != self.klen || val.len() != self.vlen {
            return Err(Error::Length);
        }
        let (size, klen, w) = (self.rsize(), self.klen, self.w);
        match self.search(key) {
            Ok(p) => {
                let s = self.slot(p);
                if let Some(v) = rec_mut(self.mem.as_mut_slice(), s, size).and_then(|r| r.get_mut(klen..)) {
                    v.copy_from_slice(val);
                }
                Ok(true)
            }
            Err(_) if self.len == self.cap => Err(Error::Full),
            Err(p) => {
                let slot = self.len;
                if let Some(r) = rec_mut(self.mem.as_mut_slice(), slot, size) {
                    let (k, v) = r.split_at_mut(klen);
                    k.copy_from_slice(key);
                    v.copy_from_slice(val);
                }
                let at = self.cap * size;
                if let Some(idx) = self.mem.as_mut_slice().get_mut(at..) {
                    idx.copy_within(p * w..self.len * w, (p + 1) * w);
                }
                self.set_slot(p, slot);
                self.len += 1;
                Ok(false)
            }
        }
    }

    /// Removes `key`; returns whether it was held.
    pub fn remove(&mut self, key: &[u8]) -> bool {
        let Ok(p) = self.search(key) else {
            return false;
        };
        let (slot, size, last, w) = (self.slot(p), self.rsize(), self.len - 1, self.w);
        let at = self.cap * size;
        if let Some(idx) = self.mem.as_mut_slice().get_mut(at..) {
            idx.copy_within((p + 1) * w..self.len * w, p * w);
        }
        self.len = last;
        if slot != last {
            // The last record moves into the hole; the index entry that named it now names the hole.
            if let Ok(q) = self.search(self.key_of(last)) {
                self.set_slot(q, slot);
            }
            self.mem
                .as_mut_slice()
                .copy_within(last * size..(last + 1) * size, slot * size);
        }
        true
    }

    /// Keeps the records `keep` returns true for and removes the rest, in one pass in key order; `keep` may change
    /// the value. Returns the number removed. The index is compacted in place and the records that sat above the new
    /// length move into the holes, so the work is O(len) index bytes and one record copy per record that moves,
    /// against a shift of the index tail per removal for the same removals one by one. Allocates nothing.
    pub fn retain(&mut self, mut keep: impl FnMut(&[u8], &mut [u8]) -> bool) -> usize {
        let (len, w, klen, size) = (self.len, self.w, self.klen, self.rsize());
        let Some((recs, idx)) = self.mem.as_mut_slice().split_at_mut_checked(self.cap * size) else {
            return 0;
        };
        // Pass 1: swap each kept entry down to the front, so the index holds the kept slots in key order and then
        // the removed slots (in no order).
        let mut kept = 0;
        for p in 0..len {
            let s = rd_w(idx, p, w);
            let stays = rec_mut(recs, s, size).is_none_or(|r| {
                let (k, v) = r.split_at_mut(klen);
                keep(k, v)
            });
            if stays {
                let held = rd_w(idx, kept, w);
                wr_w(idx, kept, w, s);
                wr_w(idx, p, w, held);
                kept += 1;
            }
        }
        // Pass 2: a kept record above `kept` takes the next removed slot below it, so the records are dense again.
        let mut j = kept;
        for q in 0..kept {
            let s = rd_w(idx, q, w);
            if s < kept {
                continue;
            }
            while j < len && rd_w(idx, j, w) >= kept {
                j += 1;
            }
            if j == len {
                // Unreachable: below `kept` there are as many removed slots as kept records above it.
                break;
            }
            let hole = rd_w(idx, j, w);
            j += 1;
            wr_w(idx, q, w, hole);
            recs.copy_within(s * size..(s + 1) * size, hole * size);
        }
        self.len = kept;
        len - kept
    }
}

/// The index of the slab, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
impl SortedSlab {
    /// The slot (the record's place in the block) of the record at position `pos` in key order, for `pos` below
    /// [`Self::len`].
    #[must_use]
    pub fn trace_slot(&self, pos: usize) -> Option<usize> {
        (pos < self.len).then(|| self.slot(pos))
    }
}
