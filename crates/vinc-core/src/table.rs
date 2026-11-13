//! A bounded hash table with chaining and an insertion-order list, the one lookup structure of the endpoint.
//!
//! Entries live in a fixed array. Each bucket heads a chain through the entries; a second list links the entries in
//! insertion order, so the oldest is found and unlinked in constant time. Keys hash with a keyed multiply-mix, so a
//! peer who picks identifiers cannot aim them at one bucket without the key the host seeded.
//!
//! Invariants: the table never holds more than `CAP` entries and never allocates; a key may appear more than once
//! only through [`Table::insert_dup`]; [`Table::insert`] replaces the value of an existing key and never moves it in
//! the order; when the table is full [`Table::insert`] evicts the oldest entry and [`Table::insert_dup`] and
//! [`Table::insert_room`] refuse. Every operation costs the length of one chain, which stays short while `CAP`
//! entries spread over `CAP` buckets.

use core::hash::{Hash, Hasher};

use crate::store::{Store, filled, store_fn};

const NIL: u32 = u32::MAX;

/// A keyed 64-bit hasher: each 8-byte word is mixed in with a multiply and a rotation, and the result is finalised.
struct Mix(u64);

impl Mix {
    const K: u64 = 0x9E37_79B9_7F4A_7C15;

    fn step(&mut self, w: u64) {
        self.0 = (self.0 ^ w).wrapping_mul(Self::K).rotate_left(29);
    }
}

impl Hasher for Mix {
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut w = [0u8; 8];
            if let Some(d) = w.get_mut(..chunk.len()) {
                d.copy_from_slice(chunk);
            }
            self.step(u64::from_le_bytes(w) ^ ((chunk.len() as u64) << 56));
        }
    }

    fn write_u8(&mut self, i: u8) {
        self.step(u64::from(i));
    }

    fn write_u16(&mut self, i: u16) {
        self.step(u64::from(i));
    }

    fn write_u32(&mut self, i: u32) {
        self.step(u64::from(i));
    }

    fn write_u64(&mut self, i: u64) {
        self.step(i);
    }

    fn write_usize(&mut self, i: usize) {
        self.step(i as u64);
    }

    fn finish(&self) -> u64 {
        let mut z = self.0;
        z = (z ^ (z >> 32)).wrapping_mul(0xD6E8_FEB8_6659_FD93);
        z = (z ^ (z >> 32)).wrapping_mul(0xD6E8_FEB8_6659_FD93);
        z ^ (z >> 32)
    }
}

#[derive(Clone, Copy)]
struct Entry<K, V> {
    kv: Option<(K, V)>,
    chain: u32,
    older: u32,
    newer: u32,
}

impl<K, V> Entry<K, V> {
    const EMPTY: Self = Self {
        kv: None,
        chain: NIL,
        older: NIL,
        newer: NIL,
    };
}

/// A bounded hash table of up to `CAP` entries; see the module docs.
pub struct Table<K, V, const CAP: usize> {
    seed: u64,
    heads: Store<u32, CAP>,
    entries: Store<Entry<K, V>, CAP>,
    free: u32,
    oldest: u32,
    newest: u32,
    len: usize,
}

impl<K, V, const CAP: usize> core::fmt::Debug for Table<K, V, CAP> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Table")
            .field("len", &self.len)
            .field("capacity", &CAP)
            .finish_non_exhaustive()
    }
}

impl<K: Hash + Eq + Copy, V: Copy, const CAP: usize> Table<K, V, CAP> {
    store_fn! {
    /// An empty table whose hash is keyed by `seed`.
    #[allow(
        clippy::indexing_slicing,
        reason = "an initialiser; the loop bound keeps the index in range"
    )]
    pub fn new(seed: u64) -> Self {
        const { assert!(CAP >= 1 && CAP < NIL as usize) };
        let mut entries: Store<Entry<K, V>, CAP> = filled(Entry::EMPTY);
        // Thread the free list through the `chain` links.
        let mut i = 0;
        while i + 1 < CAP {
            entries[i].chain = (i + 1) as u32;
            i += 1;
        }
        Self {
            seed,
            heads: filled(NIL),
            entries,
            free: 0,
            oldest: NIL,
            newest: NIL,
            len: 0,
        }
    }
    }

    /// How many entries the table holds.
    pub const fn len(&self) -> usize {
        self.len
    }

    /// Whether the table is empty.
    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn bucket(&self, k: &K) -> usize {
        let mut h = Mix(self.seed);
        k.hash(&mut h);
        (h.finish() % CAP as u64) as usize
    }

    /// The bucket `k` hashes to: the bucket function the models take as a parameter, read for the trace check.
    #[cfg(feature = "trace")]
    pub fn trace_bucket(&self, k: &K) -> usize {
        self.bucket(k)
    }

    fn at(&self, i: u32) -> Option<&Entry<K, V>> {
        self.entries.get(i as usize)
    }

    fn find_from(&self, mut i: u32, k: &K) -> Option<u32> {
        while let Some(e) = self.at(i) {
            if e.kv.as_ref().is_some_and(|(ek, _)| ek == k) {
                return Some(i);
            }
            i = e.chain;
        }
        None
    }

    fn find(&self, k: &K) -> Option<u32> {
        self.find_from(*self.heads.get(self.bucket(k))?, k)
    }

    /// The value stored under `k`.
    pub fn get(&self, k: &K) -> Option<&V> {
        let i = self.find(k)?;
        self.at(i)?.kv.as_ref().map(|(_, v)| v)
    }

    /// The value stored under `k`, to change in place. The insertion order is untouched.
    pub fn get_mut(&mut self, k: &K) -> Option<&mut V> {
        let i = self.find(k)?;
        self.entries.get_mut(i as usize)?.kv.as_mut().map(|(_, v)| v)
    }

    /// Whether `k` is present.
    pub fn contains(&self, k: &K) -> bool {
        self.find(k).is_some()
    }

    fn link_newest(&mut self, i: u32) {
        let tail = self.newest;
        if let Some(e) = self.entries.get_mut(i as usize) {
            e.older = tail;
            e.newer = NIL;
        }
        match self.entries.get_mut(tail as usize) {
            Some(t) => t.newer = i,
            None => self.oldest = i,
        }
        self.newest = i;
    }

    fn unlink_order(&mut self, i: u32) {
        let (older, newer) = self.at(i).map_or((NIL, NIL), |e| (e.older, e.newer));
        match self.entries.get_mut(older as usize) {
            Some(o) => o.newer = newer,
            None => self.oldest = newer,
        }
        match self.entries.get_mut(newer as usize) {
            Some(n) => n.older = older,
            None => self.newest = older,
        }
    }

    /// Add a new entry without looking for the key. Returns false when the table is full.
    fn push(&mut self, k: K, v: V) -> bool {
        let i = self.free;
        let Some(next_free) = self.at(i).map(|e| e.chain) else {
            return false;
        };
        let b = self.bucket(&k);
        let head = self.heads.get(b).copied().unwrap_or(NIL);
        if let Some(e) = self.entries.get_mut(i as usize) {
            *e = Entry {
                kv: Some((k, v)),
                chain: head,
                older: NIL,
                newer: NIL,
            };
        }
        if let Some(h) = self.heads.get_mut(b) {
            *h = i;
        }
        self.free = next_free;
        self.link_newest(i);
        self.len += 1;
        true
    }

    /// Remove entry `i` (which must be live) and return its pair.
    fn pop(&mut self, i: u32) -> Option<(K, V)> {
        let (k, v) = self.at(i)?.kv?;
        let b = self.bucket(&k);
        let next = self.at(i)?.chain;
        let mut cur = *self.heads.get(b)?;
        if cur == i {
            *self.heads.get_mut(b)? = next;
        } else {
            while let Some(e) = self.at(cur) {
                if e.chain == i {
                    self.entries.get_mut(cur as usize)?.chain = next;
                    break;
                }
                cur = e.chain;
            }
        }
        self.unlink_order(i);
        let free = self.free;
        *self.entries.get_mut(i as usize)? = Entry {
            chain: free,
            ..Entry::EMPTY
        };
        self.free = i;
        self.len -= 1;
        Some((k, v))
    }

    /// Store `v` under `k`: an existing key keeps its place in the order and takes the value; a new key is added
    /// and, when the table is full, the oldest entry is evicted and returned.
    pub fn insert(&mut self, k: K, v: V) -> Option<(K, V)> {
        if let Some(slot) = self.get_mut(&k) {
            *slot = v;
            return None;
        }
        let evicted = if self.len == CAP { self.pop(self.oldest) } else { None };
        self.push(k, v);
        evicted
    }

    /// Store `v` under `k` like [`insert`](Self::insert), but a new key is refused (false) when the table is full.
    pub fn insert_room(&mut self, k: K, v: V) -> bool {
        if let Some(slot) = self.get_mut(&k) {
            *slot = v;
            return true;
        }
        self.push(k, v)
    }

    /// Add an entry even if the key is present. Returns false when the table is full.
    pub fn insert_dup(&mut self, k: K, v: V) -> bool {
        self.push(k, v)
    }

    /// Remove the entry under `k` (the newest if several) and return its value.
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let i = self.find(k)?;
        self.pop(i).map(|(_, v)| v)
    }

    /// Remove the entry holding exactly `k` and `v`, among duplicates. Returns whether one was removed.
    pub fn remove_pair(&mut self, k: &K, v: &V) -> bool
    where
        V: PartialEq,
    {
        let mut cur = self.heads.get(self.bucket(k)).copied().unwrap_or(NIL);
        while let Some(e) = self.at(cur) {
            if e.kv.as_ref().is_some_and(|(ek, ev)| ek == k && ev == v) {
                return self.pop(cur).is_some();
            }
            cur = e.chain;
        }
        false
    }

    /// Every value stored under `k`, newest first, up to `M` of them, and how many were found.
    pub fn matches<const M: usize>(&self, k: &K) -> ([Option<V>; M], usize) {
        let mut out = [None; M];
        let mut n = 0;
        let mut cur = self.heads.get(self.bucket(k)).copied().unwrap_or(NIL);
        while let Some(e) = self.at(cur) {
            if let Some((ek, ev)) = e.kv.as_ref()
                && ek == k
                && let Some(s) = out.get_mut(n)
            {
                *s = Some(*ev);
                n += 1;
            }
            cur = e.chain;
        }
        (out, n)
    }

    /// Move the entry under `k` to the newest position, so it is evicted last.
    pub fn touch(&mut self, k: &K) {
        if let Some(i) = self.find(k)
            && self.newest != i
        {
            self.unlink_order(i);
            self.link_newest(i);
        }
    }

    /// The entry at array position `i`, if live: the position is stable while the entry lives.
    pub fn at_index(&self, i: usize) -> Option<(&K, &V)> {
        self.entries.get(i)?.kv.as_ref().map(|(k, v)| (k, v))
    }

    /// The array position of the entry under `k`.
    pub fn index_of(&self, k: &K) -> Option<usize> {
        self.find(k).map(|i| i as usize)
    }

    /// The entries from the oldest to the newest, as pairs.
    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        let mut cur = self.oldest;
        core::iter::from_fn(move || {
            let e = self.at(cur)?;
            cur = e.newer;
            e.kv.as_ref().map(|(k, v)| (k, v))
        })
    }

    /// Remove every entry.
    pub fn clear(&mut self) {
        *self = Self::new(self.seed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fifo_eviction_and_replacement() {
        let mut t: Table<u32, u32, 4> = Table::new(7);
        for i in 0..4 {
            assert!(t.insert(i, i * 10).is_none());
        }
        assert!(t.insert(1, 99).is_none());
        assert_eq!(t.get(&1), Some(&99));
        assert_eq!(t.insert(9, 90), Some((0, 0)));
        assert_eq!(t.len(), 4);
        assert!(!t.contains(&0));
        t.touch(&1);
        assert_eq!(t.insert(10, 100), Some((2, 20)));
        assert_eq!(t.iter().map(|(k, _)| *k).collect::<std::vec::Vec<_>>(), [3, 9, 1, 10]);
    }

    #[test]
    fn duplicates_and_room() {
        let mut t: Table<u8, u8, 3> = Table::new(1);
        assert!(t.insert_dup(5, 1));
        assert!(t.insert_dup(5, 2));
        let (m, n) = t.matches::<4>(&5);
        assert_eq!((n, m[0], m[1]), (2, Some(2), Some(1)));
        assert!(t.insert_room(6, 3));
        assert!(!t.insert_room(7, 4));
        assert!(!t.insert_dup(5, 9));
        assert!(t.remove_pair(&5, &1));
        assert!(!t.remove_pair(&5, &1));
        assert!(t.insert_room(7, 4));
        assert_eq!(t.remove(&7), Some(4));
    }

    #[test]
    fn heavy_churn_keeps_the_invariants() {
        let mut t: Table<u32, u32, 16> = Table::new(3);
        let mut x = 1u32;
        for _ in 0..2000 {
            x = x.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
            let k = x % 40;
            match x >> 28 {
                0..=7 => {
                    t.insert(k, x);
                }
                8..=11 => {
                    t.remove(&k);
                }
                _ => t.touch(&k),
            }
            assert!(t.len() <= 16);
            assert_eq!(t.iter().count(), t.len());
        }
    }
}
