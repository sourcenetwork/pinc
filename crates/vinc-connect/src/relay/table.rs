//! Bounded tables keyed by node id.
//!
//! [`Table`] is an open-addressing hash table with linear probing and backward-shift deletion, so lookups never see a
//! tombstone and a probe sequence is as long as the cluster it lands in. [`Cache`] is direct-mapped: one slot per hash
//! bucket, a colliding insert replaces the occupant.
//!
//! Invariants: the capacity `N` is fixed at compile time and never exceeded; the slots are exactly `N` entries, on the
//! heap under `alloc` (built entry by entry, never as one value of the table's size) and inline without it; the hash is
//! keyed by a seed the host chooses, so a peer that grinds node ids cannot aim them at one bucket without knowing it;
//! every operation is deterministic and terminates after at most `N` probes; nothing panics, and nothing allocates but
//! the slots of a table built with the `alloc` feature, once, when it is made.

use vinc_crypto::NodeId;

fn hash(seed: u64, k: &NodeId) -> u64 {
    let mut h = seed ^ 0xcbf2_9ce4_8422_2325 ^ u64::from(k.alg.tag());
    for b in k.bytes {
        h = (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
    }
    h ^ (h >> 29)
}

#[allow(
    clippy::cast_possible_truncation,
    reason = "the bucket index is reduced modulo N, a usize"
)]
fn bucket<const N: usize>(seed: u64, k: &NodeId) -> usize {
    (hash(seed, k) % N as u64) as usize
}

/// The slots of a table: exactly `N` entries. With the `alloc` feature they are a boxed slice collected one entry at a
/// time, so no value of the table's size is ever built on the stack, at any optimisation level, and a table of
/// thousands of entries is a few words on the stack; without it they are an inline array, wherever the owner puts it.
#[cfg(feature = "alloc")]
type Slots<V, const N: usize> = alloc::boxed::Box<[Option<(NodeId, V)>]>;
#[cfg(not(feature = "alloc"))]
type Slots<V, const N: usize> = [Option<(NodeId, V)>; N];

#[cfg(feature = "alloc")]
fn slots<V, const N: usize>() -> Slots<V, N> {
    (0..N).map(|_| None).collect()
}

#[cfg(not(feature = "alloc"))]
fn slots<V, const N: usize>() -> Slots<V, N> {
    core::array::from_fn(|_| None)
}

/// A bounded hash table from node id to `V`.
#[derive(Debug)]
pub struct Table<V, const N: usize> {
    slots: Slots<V, N>,
    len: usize,
    seed: u64,
}

impl<V, const N: usize> Table<V, N> {
    /// An empty table hashing with `seed`.
    pub fn new(seed: u64) -> Self {
        const { assert!(N > 0, "a table needs room for one entry") };
        Self {
            slots: slots::<V, N>(),
            len: 0,
            seed,
        }
    }

    /// The bucket `k` hashes to: where a probe for `k` starts.
    pub fn bucket_of(&self, k: &NodeId) -> usize {
        bucket::<N>(self.seed, k)
    }

    /// The number of entries.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether the table holds nothing.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether no entry can be added.
    pub const fn is_full(&self) -> bool {
        self.len >= N
    }

    fn find(&self, k: &NodeId) -> Option<usize> {
        let mut i = bucket::<N>(self.seed, k);
        for _ in 0..N {
            match self.slots.get(i)? {
                None => return None,
                Some((key, _)) if key == k => return Some(i),
                Some(_) => {}
            }
            i = (i + 1) % N;
        }
        None
    }

    /// The value for `k`.
    pub fn get(&self, k: &NodeId) -> Option<&V> {
        self.find(k)
            .and_then(|i| self.slots.get(i))
            .and_then(|s| s.as_ref())
            .map(|(_, v)| v)
    }

    /// The value for `k`, mutably.
    pub fn get_mut(&mut self, k: &NodeId) -> Option<&mut V> {
        let i = self.find(k)?;
        self.slots.get_mut(i).and_then(|s| s.as_mut()).map(|(_, v)| v)
    }

    /// Whether `k` is present.
    pub fn contains(&self, k: &NodeId) -> bool {
        self.find(k).is_some()
    }

    /// Insert or replace. Returns the previous value, or gives `v` back as `Err` if `k` is new and the table is full.
    ///
    /// # Errors
    /// `Err(v)` when the table is full and `k` is not in it.
    pub fn insert(&mut self, k: NodeId, v: V) -> Result<Option<V>, V> {
        if let Some(i) = self.find(&k) {
            let old = self.slots.get_mut(i).and_then(Option::take).map(|(_, old)| old);
            if let Some(slot) = self.slots.get_mut(i) {
                *slot = Some((k, v));
            }
            return Ok(old);
        }
        if self.len >= N {
            return Err(v);
        }
        let mut i = bucket::<N>(self.seed, &k);
        for _ in 0..N {
            if matches!(self.slots.get(i), Some(None))
                && let Some(slot) = self.slots.get_mut(i)
            {
                *slot = Some((k, v));
                self.len += 1;
                return Ok(None);
            }
            i = (i + 1) % N;
        }
        Err(v)
    }

    /// Remove `k` and return its value.
    pub fn remove(&mut self, k: &NodeId) -> Option<V> {
        let i = self.find(k)?;
        self.remove_at(i)
    }

    fn remove_at(&mut self, hole: usize) -> Option<V> {
        let (_, removed) = self.slots.get_mut(hole).and_then(Option::take)?;
        self.len -= 1;
        let mut hole = hole;
        let mut j = hole;
        for _ in 0..N {
            j = (j + 1) % N;
            let Some(Some((key, _))) = self.slots.get(j) else {
                break;
            };
            let ideal = bucket::<N>(self.seed, key);
            // The entry at j may move into the hole unless its ideal slot lies cyclically in (hole, j].
            let stays = if hole <= j {
                hole < ideal && ideal <= j
            } else {
                hole < ideal || ideal <= j
            };
            if !stays {
                let moved = self.slots.get_mut(j).and_then(Option::take);
                if let Some(slot) = self.slots.get_mut(hole) {
                    *slot = moved;
                }
                hole = j;
            }
        }
        Some(removed)
    }

    /// Keep the entries `keep` accepts. `keep` may be called more than once on an entry.
    pub fn retain(&mut self, mut keep: impl FnMut(&NodeId, &mut V) -> bool) {
        let mut i = 0;
        while i < N {
            let drop_it = match self.slots.get_mut(i) {
                Some(Some((k, v))) => !keep(k, v),
                _ => false,
            };
            if drop_it {
                self.remove_at(i);
            } else {
                i += 1;
            }
        }
    }

    /// The entries in table order (deterministic for a given insertion history).
    pub fn iter(&self) -> impl Iterator<Item = (&NodeId, &V)> {
        self.slots.iter().flatten().map(|(k, v)| (k, v))
    }
}

/// A direct-mapped cache from node id to `V`: one slot per bucket, a collision replaces the occupant.
#[derive(Debug)]
pub struct Cache<V, const N: usize> {
    slots: Slots<V, N>,
    seed: u64,
}

impl<V, const N: usize> Cache<V, N> {
    /// An empty cache hashing with `seed`.
    pub fn new(seed: u64) -> Self {
        const { assert!(N > 0, "a cache needs room for one entry") };
        Self {
            slots: slots::<V, N>(),
            seed,
        }
    }

    /// The bucket `k` hashes to: where a probe for `k` starts.
    pub fn bucket_of(&self, k: &NodeId) -> usize {
        bucket::<N>(self.seed, k)
    }

    /// The value for `k`.
    pub fn get(&self, k: &NodeId) -> Option<&V> {
        match self.slots.get(bucket::<N>(self.seed, k)) {
            Some(Some((key, v))) if key == k => Some(v),
            _ => None,
        }
    }

    /// Store `v` for `k`, replacing whatever held the bucket.
    pub fn put(&mut self, k: NodeId, v: V) {
        if let Some(slot) = self.slots.get_mut(bucket::<N>(self.seed, &k)) {
            *slot = Some((k, v));
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn a_tables_slots_hold_exactly_n_entries() {
        assert_eq!(Table::<u8, 1>::new(1).slots.len(), 1);
        assert_eq!(Table::<u8, 7>::new(1).slots.len(), 7);
        assert_eq!(Table::<u8, 1024>::new(1).slots.len(), 1024);
        assert_eq!(Cache::<u8, 1>::new(1).slots.len(), 1);
        assert_eq!(Cache::<u8, 7>::new(1).slots.len(), 7);
        assert_eq!(Cache::<u8, 1024>::new(1).slots.len(), 1024);
    }
}
