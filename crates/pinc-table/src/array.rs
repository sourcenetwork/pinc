//! The array by position: a fixed number of places, each present or absent, read by position. Used for per-hub state
//! kept by boot position. A caller can also give the places an order by a key of its own (set once, at setup), and
//! walk the present places in that order. Invariants: a place is present exactly when it was set and not removed;
//! the order is always a permutation of `0..places`, the identity until set.

use crate::error::{Error, Refused};
use crate::storage::{Storage, fit, rd16, rec, rec_mut, wr16};

/// A fixed array of optional records with a stored walk order. See the module comment.
#[derive(Debug)]
pub struct Array {
    mem: Storage,
    places: usize,
    size: usize,
    count: usize,
}

impl Array {
    /// The bytes of block an array of `places` places of `record` bytes needs: the order (2 bytes a place), a
    /// presence byte a place, then the records. Saturates at `usize::MAX`.
    pub const fn bytes(places: usize, record: usize) -> usize {
        places.saturating_mul(record.saturating_add(3))
    }

    /// Makes an array of absent places over `mem`, in position order. Refuses a block smaller than
    /// [`Self::bytes`] and more places than the order can number.
    ///
    /// # Errors
    ///
    /// The [`Refused`] names what was refused in `error` and hands the block back in `storage`, untouched.
    pub fn new(mem: Storage, places: usize, record: usize) -> Result<Self, Refused> {
        if u16::try_from(places).is_err() {
            return Err(Refused {
                error: Error::Capacity,
                storage: mem,
            });
        }
        let mut mem = fit(mem, Self::bytes(places, record))?;
        let b = mem.as_mut_slice();
        for i in 0..places {
            wr16(b, i, u16::try_from(i).unwrap_or(0));
        }
        if let Some(flags) = b.get_mut(places * 2..places * 3) {
            flags.fill(0);
        }
        Ok(Self {
            mem,
            places,
            size: record,
            count: 0,
        })
    }

    /// The number of places.
    pub fn places(&self) -> usize {
        self.places
    }

    /// The places present.
    pub fn len(&self) -> usize {
        self.count
    }

    /// Whether no place is present.
    pub fn is_empty(&self) -> bool {
        self.count == 0
    }

    fn flag(&self, pos: usize) -> bool {
        self.mem.as_slice().get(self.places * 2 + pos).is_some_and(|&f| f != 0)
    }

    fn data(&self) -> &[u8] {
        self.mem.as_slice().get(self.places * 3..).unwrap_or(&[])
    }

    /// The record at `pos`, or `None` when absent or past the end.
    pub fn get(&self, pos: usize) -> Option<&[u8]> {
        (pos < self.places && self.flag(pos)).then(|| rec(self.data(), pos, self.size))
    }

    /// The record at `pos`, to change in place.
    pub fn get_mut(&mut self, pos: usize) -> Option<&mut [u8]> {
        if pos >= self.places || !self.flag(pos) {
            return None;
        }
        let (at, size) = (self.places * 3, self.size);
        rec_mut(self.mem.as_mut_slice().get_mut(at..)?, pos, size)
    }

    /// Makes `pos` present with `record`; returns whether it was present before.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn set(&mut self, pos: usize, record: &[u8]) -> Result<bool, Error> {
        if pos >= self.places {
            return Err(Error::Position);
        }
        if record.len() != self.size {
            return Err(Error::Length);
        }
        let (at, size, was) = (self.places * 3, self.size, self.flag(pos));
        let b = self.mem.as_mut_slice();
        rec_mut(b.get_mut(at..).ok_or(Error::Position)?, pos, size)
            .ok_or(Error::Position)?
            .copy_from_slice(record);
        if let Some(f) = b.get_mut(self.places * 2 + pos) {
            *f = 1;
        }
        self.count += usize::from(!was);
        Ok(was)
    }

    /// Makes `pos` absent; returns whether it was present.
    pub fn remove(&mut self, pos: usize) -> bool {
        if pos >= self.places || !self.flag(pos) {
            return false;
        }
        if let Some(f) = self.mem.as_mut_slice().get_mut(self.places * 2 + pos) {
            *f = 0;
        }
        self.count -= 1;
        true
    }

    /// Sets the walk order: the positions sorted by `keys[position]`, equal keys in position order. Run once, at
    /// setup. Refuses a `keys` slice that is not one key a place.
    ///
    /// # Errors
    ///
    /// The [`Error`] names what was refused; the table is unchanged.
    pub fn set_order<K: Ord>(&mut self, keys: &[K]) -> Result<(), Error> {
        if keys.len() != self.places {
            return Err(Error::Length);
        }
        // vertexia: insertion sort, O(places^2) moves once at setup; fine for the 64 hubs it serves, heapsort if
        // places grow
        let b = self.mem.as_mut_slice();
        for i in 0..self.places {
            wr16(b, i, u16::try_from(i).unwrap_or(0));
        }
        for i in 1..self.places {
            let x = rd16(b, i);
            let mut j = i;
            while j > 0 {
                let prev = rd16(b, j - 1);
                if keys.get(usize::from(prev)) <= keys.get(usize::from(x)) {
                    break;
                }
                wr16(b, j, prev);
                j -= 1;
            }
            wr16(b, j, x);
        }
        Ok(())
    }

    /// Every position in walk order, present or not.
    pub fn order(&self) -> impl Iterator<Item = usize> + '_ {
        (0..self.places).map(move |i| usize::from(rd16(self.mem.as_slice(), i)))
    }

    /// The present places in walk order, with their records.
    pub fn iter(&self) -> impl Iterator<Item = (usize, &[u8])> + '_ {
        self.order().filter_map(move |p| self.get(p).map(|r| (p, r)))
    }
}
