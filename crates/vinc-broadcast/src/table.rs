//! Fixed-capacity tables for the steady path: an open-addressing map from message id to a word, and the dedupe set
//! built on it.
//!
//! Both allocate once, at creation, and never again: inserting, looking up, removing and expiring touch no
//! allocator. The map uses linear probing with backward-shift deletion, so it holds no tombstones and its probe
//! length stays short however long it runs.
//!
//! A message id is chosen by the origin that sends it, so the map never places an id by its own bits: the home slot
//! is a keyed hash of the id under the node's [`IdKey`], the endpoint's own map keys, which a sender cannot read.
//! The hash has two steps, the keyed multiply and the hasher's finishing multiply, because the keyed multiply alone
//! puts ids that form an arithmetic progression on slots that form one. It is a seeded hash that is not
//! cryptographic. Nothing is refused for a long walk: the tables hold at most half their slots, so a walk reads at
//! most one slot more than the table holds entries (8,193 for the dedupe set, 2,049 for a log index), whatever the
//! placement. A walk of [`PROBE_LONG`] slots or more is counted, so a sender that did learn the key shows.
//!
//! Invariants: the map never holds more than its capacity (an insert past it is refused); a value stored is never
//! `u64::MAX`; the set's entries are in insertion order, which is time order because time only goes forward, so
//! expiry stops at the first live entry; a print kept beside an entry moves with its slot and leaves with it.

use alloc::collections::VecDeque;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::Cell;
use core::hash::BuildHasher;
use rapidhash::quality::SeedableState;
use vinc_membership::Nanos;

use crate::consts::SEEN_TTL;
use crate::node::StartError;

/// The secrets of the unit tests, full width as the key store draws them.
#[cfg(test)]
pub(crate) static TEST_SECRETS: [u64; 7] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xff51_afd7_ed55_8ccd,
    0xc4ce_b9fe_1a85_ec53,
];

/// A walk of this many slots or more is counted ([`Seen::long_walks`]): for ids spread by a secret key it is far out
/// in the tail of the walks of a table at most half full.
pub(crate) const PROBE_LONG: usize = 128;

/// The key that places message ids in the dedupe sets and the hub logs of a node: a 64-bit seed and seven 64-bit
/// secrets, the endpoint's map keys, which its key store draws. The hash has two steps, the keyed multiply and the
/// hasher's finishing multiply; it is seeded and not cryptographic.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct IdKey(SeedableState<'static>);

impl IdKey {
    /// The key of `seed` and `secrets`. A weak key costs only speed: every bound of the tables holds under any
    /// placement. The keys refused are a first secret of zero or of all ones: the keyed multiply then gives every id
    /// but one the same product, so they would start their walks at one slot (the hasher reads only that secret of the
    /// seven for an id). Other patterned values cost speed for a share of the ids and are not refused: draw the key at
    /// random.
    ///
    /// # Errors
    /// [`StartError::InvalidKey`] when the first secret is zero or all ones.
    pub fn new(seed: u64, secrets: &'static [u64; 7]) -> Result<Self, StartError> {
        if secrets[0] == 0 || secrets[0] == u64::MAX {
            return Err(StartError::InvalidKey);
        }
        Ok(Self(SeedableState::custom(seed, secrets)))
    }

    fn hash(&self, id: u64) -> u64 {
        self.0.hash_one(id)
    }
}

impl core::fmt::Debug for IdKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IdKey").finish_non_exhaustive()
    }
}

/// Where a walk for an id ended.
enum Walk {
    /// The slot holding the id.
    Found(usize),
    /// The first empty slot after the id's home.
    Absent(usize),
    /// No empty slot (a table kept at most half full never gives this).
    Full,
}

/// A map from a message id to a `u64`, with a fixed capacity chosen at creation.
#[derive(Debug)]
pub(crate) struct MidMap {
    keys: Vec<u64>,
    // The value plus one; zero marks an empty slot, so a zeroed allocation is an empty map.
    vals: Vec<u64>,
    // A word kept beside each slot (zero: none), empty until `with_prints`.
    prints: Vec<u64>,
    len: usize,
    cap: usize,
    key: IdKey,
    long: Cell<u64>,
}

impl MidMap {
    /// A map that holds up to `cap` entries, placing ids under `key`.
    pub(crate) fn with_capacity(cap: usize, key: IdKey) -> Self {
        let slots = (cap * 2).next_power_of_two().max(8);
        Self {
            keys: vec![0; slots],
            vals: vec![0; slots],
            prints: Vec::new(),
            len: 0,
            cap,
            key,
            long: Cell::new(0),
        }
    }

    /// Keep a word beside each entry from now on (allocates once; a no-op when it is kept already).
    pub(crate) fn with_prints(&mut self) {
        if self.prints.is_empty() {
            self.prints = vec![0; self.keys.len()];
        }
    }

    const fn mask(&self) -> usize {
        self.keys.len() - 1
    }

    /// The slot a walk for `key` starts at.
    pub(crate) fn home(&self, key: u64) -> usize {
        usize::try_from(self.key.hash(key) & self.mask() as u64).unwrap_or(0)
    }

    /// Walk from the home of `key` to its slot or to the first empty one. A walk of [`PROBE_LONG`] slots or more is
    /// counted.
    fn walk(&self, key: u64) -> Walk {
        let mut i = self.home(key);
        let mut found = Walk::Full;
        let mut n = 0;
        for step in 1..=self.keys.len() {
            n = step;
            match (self.vals.get(i).copied(), self.keys.get(i).copied()) {
                (Some(0), _) => {
                    found = Walk::Absent(i);
                    break;
                }
                (Some(_), Some(k)) if k == key => {
                    found = Walk::Found(i);
                    break;
                }
                _ => i = (i + 1) & self.mask(),
            }
        }
        if n >= PROBE_LONG {
            self.long.set(self.long.get().saturating_add(1));
        }
        found
    }

    fn slot(&self, key: u64) -> Option<usize> {
        match self.walk(key) {
            Walk::Found(i) => Some(i),
            Walk::Absent(_) | Walk::Full => None,
        }
    }

    /// How many walks read [`PROBE_LONG`] slots or more.
    pub(crate) fn long_walks(&self) -> u64 {
        self.long.get()
    }

    pub(crate) fn get(&self, key: u64) -> Option<u64> {
        self.slot(key).and_then(|i| self.vals.get(i)).map(|v| v - 1)
    }

    /// Store `val` under `key`; false if the map is full and `key` is new.
    pub(crate) fn insert(&mut self, key: u64, val: u64) -> bool {
        let at = match self.walk(key) {
            Walk::Found(i) => {
                if let Some(v) = self.vals.get_mut(i) {
                    *v = val.saturating_add(1);
                }
                return true;
            }
            Walk::Absent(i) => i,
            Walk::Full => return false,
        };
        if self.len >= self.cap {
            return false;
        }
        if let (Some(k), Some(v)) = (self.keys.get_mut(at), self.vals.get_mut(at)) {
            *k = key;
            *v = val.saturating_add(1);
            self.len += 1;
        }
        true
    }

    /// Keep `print` beside the entry of `key`, if the map holds it and keeps prints.
    pub(crate) fn set_print(&mut self, key: u64, print: u64) {
        if let Some(p) = self.slot(key).and_then(|i| self.prints.get_mut(i)) {
            *p = print;
        }
    }

    /// The word kept beside the entry of `key`; zero if the map does not hold it or none was set.
    pub(crate) fn print(&self, key: u64) -> u64 {
        self.slot(key).and_then(|i| self.prints.get(i)).copied().unwrap_or(0)
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
            if let Some(pj) = self.prints.get(j).copied()
                && let Some(p) = self.prints.get_mut(hole)
            {
                *p = pj;
            }
            hole = j;
        }
        if let Some(v) = self.vals.get_mut(hole) {
            *v = 0;
        }
        if let Some(p) = self.prints.get_mut(hole) {
            *p = 0;
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
    pub(crate) fn with_capacity(cap: usize, key: IdKey) -> Self {
        Self {
            map: MidMap::with_capacity(cap, key),
            order: VecDeque::with_capacity(cap),
            last: 0,
            cap,
        }
    }

    /// Keep the print of a message beside its id from now on (a hub does, from the first message it logs). Allocates
    /// once, 8 bytes a slot.
    pub(crate) fn keep_prints(&mut self) {
        self.map.with_prints();
    }

    /// Whether `mid` was seen within the time to live.
    pub(crate) fn contains(&self, mid: u64, now: Nanos) -> bool {
        self.map.get(mid).is_some_and(|at| now.saturating_sub(at) <= SEEN_TTL)
    }

    /// The print kept for `mid`, if it was seen within the time to live and one was kept.
    pub(crate) fn print(&self, mid: u64, now: Nanos) -> Option<u64> {
        Some(self.map.print(mid)).filter(|p| *p != 0 && self.contains(mid, now))
    }

    /// How many walks of the set read [`PROBE_LONG`] slots or more.
    pub(crate) fn long_walks(&self) -> u64 {
        self.map.long_walks()
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

    /// Record a message that left the log, with the print of its signature: the id is recorded (forced) unless it is
    /// already, and the print is kept beside it, so a retry of that message is told from another under the same id.
    pub(crate) fn keep(&mut self, mid: u64, print: u64, now: Nanos) {
        if !self.contains(mid, now) {
            self.insert(mid, now, true);
        }
        self.map.set_print(mid, print);
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

#[cfg(test)]
mod tests;
