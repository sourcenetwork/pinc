//! Fixed-capacity tables for the steady path: an open-addressing map from message id to a word, and the dedupe set
//! built on it.
//!
//! Both allocate once, at creation, and never again: inserting, looking up, removing and expiring touch no
//! allocator. The map uses linear probing with backward-shift deletion, so it holds no tombstones and its probe
//! length stays short however long it runs.
//!
//! A message id is chosen by the origin that sends it, so the map never places an id by its own bits: the home slot
//! is a keyed hash of the id under the node's [`IdKey`], drawn from the node's key store, which a sender cannot
//! read. The guarantee is the hasher's own: a seeded hash that is not cryptographic, as for the facade's tables.
//!
//! Invariants: the map never holds more than its capacity (an insert past it is refused); a value stored is never
//! `u64::MAX`; no entry sits more than [`PROBE_MAX`] slots from its home, and a lookup or an insert never walks
//! further (it is refused and the caller counts it); the set's entries are in insertion order, which is time order
//! because time only goes forward, so expiry stops at the first live entry.

use alloc::collections::VecDeque;
use alloc::vec;
use alloc::vec::Vec;
use rapidhash::v3::{RapidSecrets, rapidhash_v3_seeded};
use vinc_membership::Nanos;

use crate::consts::SEEN_TTL;

/// The most slots a lookup or an insert walks from an id's home. The tables hold at most half their slots, so for
/// ids spread by the keyed hash a walk this long is far out in the tail (the chance falls off exponentially with the
/// length, roughly `exp(-0.19 * n)` at half load: about 1e-11 at 128), while a sender who could choose where its ids
/// land would make every lookup of the topic scan the whole table. Past it the id is refused, never walked.
pub(crate) const PROBE_MAX: usize = 128;

/// The key that places ids in the tables of one node: a 64-bit seed drawn from the node's key store, expanded by the
/// hasher into its secrets once.
#[derive(Clone, Copy)]
pub(crate) struct IdKey(RapidSecrets);

impl IdKey {
    pub(crate) const fn from_seed(seed: u64) -> Self {
        Self(RapidSecrets::seed(seed))
    }

    fn hash(&self, id: u64) -> u64 {
        rapidhash_v3_seeded(&id.to_le_bytes(), &self.0)
    }
}

impl core::fmt::Debug for IdKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("IdKey").finish_non_exhaustive()
    }
}

/// Why an id was not recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refused {
    /// The table holds its capacity.
    Full,
    /// The id's probe would pass [`PROBE_MAX`].
    Probe,
}

/// A lookup that would pass [`PROBE_MAX`] slots: nothing was found within the bound, and the id cannot be recorded.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ProbeLimit;

/// Where a probe for an id ended.
enum Probe {
    Found(usize),
    Absent(usize),
    Over,
}

/// A map from a message id to a `u64`, with a fixed capacity chosen at creation.
#[derive(Debug)]
pub(crate) struct MidMap {
    keys: Vec<u64>,
    // The value plus one; zero marks an empty slot, so a zeroed allocation is an empty map.
    vals: Vec<u64>,
    len: usize,
    cap: usize,
    key: IdKey,
}

impl MidMap {
    /// A map that holds up to `cap` entries, placing ids under `key`.
    pub(crate) fn with_capacity(cap: usize, key: IdKey) -> Self {
        let slots = (cap * 2).next_power_of_two().max(8);
        Self {
            keys: vec![0; slots],
            vals: vec![0; slots],
            len: 0,
            cap,
            key,
        }
    }

    const fn mask(&self) -> usize {
        self.keys.len() - 1
    }

    /// The slot a probe for `key` starts at.
    pub(crate) fn home(&self, key: u64) -> usize {
        usize::try_from(self.key.hash(key) & self.mask() as u64).unwrap_or(0)
    }

    fn probe(&self, key: u64) -> Probe {
        let mut i = self.home(key);
        for _ in 0..PROBE_MAX.min(self.keys.len()) {
            match (self.vals.get(i).copied(), self.keys.get(i).copied()) {
                (Some(0), _) => return Probe::Absent(i),
                (Some(_), Some(k)) if k == key => return Probe::Found(i),
                (Some(_), Some(_)) => i = (i + 1) & self.mask(),
                _ => return Probe::Over,
            }
        }
        Probe::Over
    }

    fn slot(&self, key: u64) -> Option<usize> {
        match self.probe(key) {
            Probe::Found(i) => Some(i),
            Probe::Absent(_) | Probe::Over => None,
        }
    }

    pub(crate) fn get(&self, key: u64) -> Option<u64> {
        self.slot(key).and_then(|i| self.vals.get(i)).map(|v| v - 1)
    }

    /// The value under `key`, or [`ProbeLimit`] when the walk passed [`PROBE_MAX`] slots without an answer.
    pub(crate) fn lookup(&self, key: u64) -> Result<Option<u64>, ProbeLimit> {
        match self.probe(key) {
            Probe::Found(i) => Ok(self.vals.get(i).map(|v| v - 1)),
            Probe::Absent(_) => Ok(None),
            Probe::Over => Err(ProbeLimit),
        }
    }

    /// Whether an insert of `key` stays within [`PROBE_MAX`] (the capacity is not looked at).
    pub(crate) fn fits_probe(&self, key: u64) -> bool {
        !matches!(self.probe(key), Probe::Over)
    }

    /// Store `val` under `key`.
    ///
    /// # Errors
    /// [`Refused::Full`] if the map is full and `key` is new, [`Refused::Probe`] if `key` is new and its home run is
    /// [`PROBE_MAX`] slots long: the caller counts the refusal and does not rely on the id being remembered.
    pub(crate) fn insert(&mut self, key: u64, val: u64) -> Result<(), Refused> {
        let at = match self.probe(key) {
            Probe::Found(i) => {
                if let Some(v) = self.vals.get_mut(i) {
                    *v = val.saturating_add(1);
                }
                return Ok(());
            }
            Probe::Absent(i) => i,
            Probe::Over => return Err(Refused::Probe),
        };
        if self.len >= self.cap {
            return Err(Refused::Full);
        }
        if let (Some(k), Some(v)) = (self.keys.get_mut(at), self.vals.get_mut(at)) {
            *k = key;
            *v = val.saturating_add(1);
            self.len += 1;
        }
        Ok(())
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
    pub(crate) fn with_capacity(cap: usize, key: IdKey) -> Self {
        Self {
            map: MidMap::with_capacity(cap, key),
            order: VecDeque::with_capacity(cap),
            last: 0,
            cap,
        }
    }

    /// Whether `mid` was seen within the time to live.
    pub(crate) fn contains(&self, mid: u64, now: Nanos) -> bool {
        self.map.get(mid).is_some_and(|at| now.saturating_sub(at) <= SEEN_TTL)
    }

    /// Whether `mid` was seen within the time to live, or [`ProbeLimit`] when the lookup passed [`PROBE_MAX`] slots.
    pub(crate) fn lookup(&self, mid: u64, now: Nanos) -> Result<bool, ProbeLimit> {
        Ok(self
            .map
            .lookup(mid)?
            .is_some_and(|at| now.saturating_sub(at) <= SEEN_TTL))
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
    ///
    /// # Errors
    /// [`Refused::Full`] for a full set, [`Refused::Probe`] for an id whose probe would pass [`PROBE_MAX`]: the id is
    /// then not remembered, and the caller counts it.
    pub(crate) fn insert(&mut self, mid: u64, now: Nanos, force: bool) -> Result<(), Refused> {
        if self.order.len() >= self.cap {
            if !force {
                return Err(Refused::Full);
            }
            self.pop_front();
        }
        self.map.insert(mid, now)?;
        self.order.push_back((mid, now));
        self.last = now;
        Ok(())
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
