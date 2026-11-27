//! The responder's bounded LRU of initiator prekeys, keyed by the 32-byte prekey hash.
//!
//! Invariants: it never holds more than `N` entries; a lookup ([`PrekeyCache::get`]) refreshes the entry's recency, a
//! peek ([`PrekeyCache::peek`]) does not; inserting into a full cache evicts the least recently used entry; `N = 0` is
//! valid and caches nothing, so every short Initial misses.
//! Lookup and eviction scan the `N` slots, which is the bound on the work per call.
// vertexia: linear scan over N slots, a hash index if N grows past a few thousand.

use pinc_crypto::provider::KEM_ENCAPS_KEY_LEN;

/// The default capacity.
pub const DEFAULT_KEY_CACHE: usize = 256;

struct Entry {
    hash: [u8; 32],
    encaps_key: [u8; KEM_ENCAPS_KEY_LEN],
    stamp: u64,
}

/// A bounded LRU of initiator prekeys. Each slot is about 1.2 KiB; for large `N` place it in a static or a box.
pub struct PrekeyCache<const N: usize = DEFAULT_KEY_CACHE> {
    entries: [Option<Entry>; N],
    clock: u64,
}

impl<const N: usize> core::fmt::Debug for PrekeyCache<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("PrekeyCache")
            .field("len", &self.len())
            .field("capacity", &N)
            .finish()
    }
}

impl<const N: usize> Default for PrekeyCache<N> {
    fn default() -> Self {
        Self::new()
    }
}

impl<const N: usize> PrekeyCache<N> {
    /// An empty cache.
    pub const fn new() -> Self {
        Self {
            entries: [const { None }; N],
            clock: 0,
        }
    }

    /// How many prekeys are cached.
    pub fn len(&self) -> usize {
        self.entries.iter().flatten().count()
    }

    /// Whether nothing is cached.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The capacity `N`.
    pub const fn capacity(&self) -> usize {
        N
    }

    fn tick(&mut self) -> u64 {
        self.clock = self.clock.wrapping_add(1);
        self.clock
    }

    /// The encapsulation key cached under `hash`, marking it most recently used.
    pub fn get(&mut self, hash: &[u8; 32]) -> Option<&[u8; KEM_ENCAPS_KEY_LEN]> {
        let stamp = self.tick();
        let entry = self.entries.iter_mut().flatten().find(|e| &e.hash == hash)?;
        entry.stamp = stamp;
        Some(&entry.encaps_key)
    }

    /// The encapsulation key cached under `hash`, leaving its recency and the clock untouched: a lookup that proved
    /// nothing (a screened datagram) must not decide which entry is evicted next.
    pub fn peek(&self, hash: &[u8; 32]) -> Option<&[u8; KEM_ENCAPS_KEY_LEN]> {
        self.entries
            .iter()
            .flatten()
            .find(|e| &e.hash == hash)
            .map(|e| &e.encaps_key)
    }

    /// Cache `encaps_key` under `hash`, evicting the least recently used entry if the cache is full.
    pub fn insert(&mut self, hash: [u8; 32], encaps_key: &[u8; KEM_ENCAPS_KEY_LEN]) {
        let stamp = self.tick();
        if let Some(e) = self.entries.iter_mut().flatten().find(|e| e.hash == hash) {
            e.stamp = stamp;
            return;
        }
        let slot = self.entries.iter().position(Option::is_none).or_else(|| {
            self.entries
                .iter()
                .enumerate()
                .filter_map(|(i, e)| e.as_ref().map(|e| (e.stamp, i)))
                .min()
                .map(|(_, i)| i)
        });
        if let Some(s) = slot.and_then(|i| self.entries.get_mut(i)) {
            *s = Some(Entry {
                hash,
                encaps_key: *encaps_key,
                stamp,
            });
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_peek_leaves_which_entry_is_evicted_and_a_get_changes_it() {
        let k = [1; KEM_ENCAPS_KEY_LEN];
        let mut c: PrekeyCache<2> = PrekeyCache::new();
        c.insert([1; 32], &k);
        c.insert([2; 32], &k);
        assert!(c.peek(&[1; 32]).is_some());
        assert!(c.peek(&[9; 32]).is_none());
        c.insert([3; 32], &k);
        assert!(c.peek(&[1; 32]).is_none(), "the peek kept the oldest entry fresh");
        assert!(c.peek(&[2; 32]).is_some());
        assert!(c.get(&[2; 32]).is_some());
        c.insert([4; 32], &k);
        assert!(c.peek(&[3; 32]).is_none());
        assert!(c.peek(&[2; 32]).is_some());
    }
}
