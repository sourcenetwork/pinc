//! Fixed-capacity tables for the steady path: an open-addressing map from message id to a word, and the dedupe set
//! built on it.
//!
//! Both allocate once, at creation, and never again: inserting, looking up, removing and expiring touch no
//! allocator. The map uses linear probing with backward-shift deletion, so it holds no tombstones and its probe
//! length stays short however long it runs.
//!
//! Invariants: the map never holds more than its capacity (an insert past it is refused); a value stored is never
//! `u64::MAX`; the set's entries are in insertion order, which is time order because time only goes forward, so
//! expiry stops at the first live entry.

use alloc::collections::VecDeque;
use alloc::vec;
use alloc::vec::Vec;
use vinc_membership::Nanos;

use crate::consts::SEEN_TTL;

/// A map from a message id to a `u64`, with a fixed capacity chosen at creation.
#[derive(Debug)]
pub(crate) struct MidMap {
    keys: Vec<u64>,
    // The value plus one; zero marks an empty slot, so a zeroed allocation is an empty map.
    vals: Vec<u64>,
    len: usize,
    cap: usize,
}

impl MidMap {
    /// A map that holds up to `cap` entries.
    pub(crate) fn with_capacity(cap: usize) -> Self {
        let slots = (cap * 2).next_power_of_two().max(8);
        Self {
            keys: vec![0; slots],
            vals: vec![0; slots],
            len: 0,
            cap,
        }
    }

    const fn mask(&self) -> usize {
        self.keys.len() - 1
    }

    fn home(&self, key: u64) -> usize {
        // Message ids are hash output, so their low bits are already uniform.
        usize::try_from(key & self.mask() as u64).unwrap_or(0)
    }

    fn slot(&self, key: u64) -> Option<usize> {
        let mut i = self.home(key);
        for _ in 0..self.keys.len() {
            if self.vals.get(i).copied()? == 0 {
                return None;
            }
            if self.keys.get(i).copied()? == key {
                return Some(i);
            }
            i = (i + 1) & self.mask();
        }
        None
    }

    pub(crate) fn get(&self, key: u64) -> Option<u64> {
        self.slot(key).and_then(|i| self.vals.get(i)).map(|v| v - 1)
    }

    /// Store `val` under `key`; false if the map is full and `key` is new.
    pub(crate) fn insert(&mut self, key: u64, val: u64) -> bool {
        if let Some(i) = self.slot(key) {
            if let Some(v) = self.vals.get_mut(i) {
                *v = val.saturating_add(1);
            }
            return true;
        }
        if self.len >= self.cap {
            return false;
        }
        let mut i = self.home(key);
        while self.vals.get(i).copied().unwrap_or(0) != 0 {
            i = (i + 1) & self.mask();
        }
        if let (Some(k), Some(v)) = (self.keys.get_mut(i), self.vals.get_mut(i)) {
            *k = key;
            *v = val.saturating_add(1);
            self.len += 1;
        }
        true
    }

    pub(crate) fn remove(&mut self, key: u64) -> Option<u64> {
        let found = self.slot(key)?;
        let old = self.vals.get(found).map(|v| v - 1);
        let mask = self.mask();
        let (mut hole, mut j) = (found, found);
        loop {
            j = (j + 1) & mask;
            let Some(vj) = self.vals.get(j).copied().filter(|v| *v != 0) else {
                break;
            };
            let kj = self.keys.get(j).copied().unwrap_or(0);
            let slot0 = self.home(kj);
            // Skip entries whose home lies cyclically in (hole, j]: moving them would break their probe chain.
            let stays = if hole <= j {
                hole < slot0 && slot0 <= j
            } else {
                hole < slot0 || slot0 <= j
            };
            if stays {
                continue;
            }
            if let (Some(k), Some(v)) = (self.keys.get_mut(hole), self.vals.get_mut(hole)) {
                *k = kj;
                *v = vj;
            }
            hole = j;
        }
        if let Some(v) = self.vals.get_mut(hole) {
            *v = 0;
        }
        self.len -= 1;
        old
    }
}

/// The message ids a node has seen, each remembered for [`SEEN_TTL`].
#[derive(Debug)]
pub(crate) struct Seen {
    map: MidMap,
    order: VecDeque<(u64, Nanos)>,
    last: Nanos,
    cap: usize,
}

impl Seen {
    pub(crate) fn with_capacity(cap: usize) -> Self {
        Self {
            map: MidMap::with_capacity(cap),
            order: VecDeque::with_capacity(cap),
            last: 0,
            cap,
        }
    }

    /// Whether `mid` was seen within the time to live.
    pub(crate) fn contains(&self, mid: u64, now: Nanos) -> bool {
        self.map.get(mid).is_some_and(|at| now.saturating_sub(at) <= SEEN_TTL)
    }

    pub(crate) fn len(&self) -> usize {
        self.order.len()
    }

    /// When the newest id was recorded, if any.
    pub(crate) fn newest(&self) -> Option<Nanos> {
        (!self.order.is_empty()).then_some(self.last)
    }

    /// When the oldest id expires (strictly after this instant), if any.
    pub(crate) fn next_expiry(&self) -> Option<Nanos> {
        self.order
            .front()
            .map(|(_, at)| at.saturating_add(SEEN_TTL).saturating_add(1))
    }

    /// Record `mid`. A full set refuses unless `force` is set, which drops the oldest id to make room.
    pub(crate) fn insert(&mut self, mid: u64, now: Nanos, force: bool) -> bool {
        if self.order.len() >= self.cap {
            if !force {
                return false;
            }
            self.pop_front();
        }
        if self.map.insert(mid, now) {
            self.order.push_back((mid, now));
            self.last = now;
            true
        } else {
            false
        }
    }

    fn pop_front(&mut self) {
        if let Some((mid, at)) = self.order.pop_front()
            && self.map.get(mid) == Some(at)
        {
            self.map.remove(mid);
        }
    }

    /// Forget the ids older than the time to live.
    pub(crate) fn expire(&mut self, now: Nanos) {
        while self
            .order
            .front()
            .is_some_and(|(_, at)| now.saturating_sub(*at) > SEEN_TTL)
        {
            self.pop_front();
        }
    }
}
