//! The hash maps and sets of the facade, all made one way: hashbrown tables under rapidhash's fast hasher, which
//! works without the standard library, seeded once per endpoint.
//!
//! Invariants: the seed is 64 bits the endpoint's key store drew when the endpoint was built (the store's randomness,
//! not a counter or an address, which on a part without an address-space layout would be guessable), so a peer that
//! cannot read it cannot pick node ids or keys that collide in a table. The seed is kept in each table's build
//! hasher; the secrets rapidhash mixes it with are its own, shared by the process. No code relies on the order
//! a table iterates in: every place that walks one sorts, dedups or takes an arbitrary entry.

use hashbrown::{HashMap, HashSet};
use rapidhash::fast::SeedableState;

/// The build hasher of every map and set of the facade.
pub(crate) type Hasher = SeedableState<'static>;
/// A map under the facade's hasher.
pub(crate) type Map<K, V> = HashMap<K, V, Hasher>;
/// A set under the facade's hasher.
pub(crate) type Set<K> = HashSet<K, Hasher>;

/// The build hasher for `seed`.
pub(crate) fn hasher(seed: u64) -> Hasher {
    SeedableState::new(seed)
}

/// An empty map for `seed`.
pub(crate) fn map<K, V>(seed: u64) -> Map<K, V> {
    HashMap::with_hasher(hasher(seed))
}

/// An empty set for `seed`.
pub(crate) fn set<K>(seed: u64) -> Set<K> {
    HashSet::with_hasher(hasher(seed))
}

#[cfg(test)]
mod tests {
    use core::hash::BuildHasher;

    use super::*;

    #[test]
    fn a_seed_fixes_the_hash_and_another_seed_changes_it() {
        let key = [7u8; 32];
        assert_eq!(hasher(1).hash_one(key), hasher(1).hash_one(key));
        assert_ne!(hasher(1).hash_one(key), hasher(2).hash_one(key));
    }

    #[test]
    fn a_map_and_a_set_find_what_they_hold() {
        let mut m = map(9);
        let mut s = set(9);
        for i in 0..1000u32 {
            m.insert(i, i + 1);
            s.insert(i);
        }
        assert!((0..1000u32).all(|i| m.get(&i) == Some(&(i + 1)) && s.contains(&i)));
        assert!(m.get(&1000).is_none() && !s.contains(&1000));
    }
}
