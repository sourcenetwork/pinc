//! The hash maps and sets of the facade, all made one way: hashbrown tables under rapidhash's fast hasher, which
//! works without the standard library, keyed by values the endpoint's key store drew.
//!
//! Where the keys come from: a hasher takes a 64-bit seed and seven 64-bit secrets, all drawn from the key store's
//! randomness in one call when an endpoint is built ([`Keys::draw`]). The secrets are drawn once per process, by the
//! first endpoint built, and kept for the life of the process; every later endpoint reuses them and keeps only its own
//! seed. rapidhash's own secrets are not used: without the standard library they come from a stack address or are
//! public constants, which a peer can know. A draw with a zero secret or two equal secrets is refused, since it means
//! the source is broken.
//!
//! The guarantee is the hasher's own: a seeded, secret-keyed hash that is not cryptographic. A peer that cannot read
//! the seed and the secrets cannot prepare keys that collide, and if it could, every table is bounded (the largest is
//! the session table, at most the `connections` limit, 65,536 entries), so the worst case of a collision attack is a
//! bounded scan. No code relies on the order a table iterates in: every place that walks one sorts, dedups or takes an
//! arbitrary entry.

use alloc::boxed::Box;
use hashbrown::{HashMap, HashSet};
use once_cell::race::OnceBox;
use rapidhash::fast::SeedableState;

use crate::error::{Error, Result};

/// The build hasher of every map and set of the facade.
pub(crate) type Hasher = SeedableState<'static>;
/// A map under the facade's hasher.
pub(crate) type Map<K, V> = HashMap<K, V, Hasher>;
/// A set under the facade's hasher.
pub(crate) type Set<K> = HashSet<K, Hasher>;

/// The secrets of the process: drawn by the first endpoint, shared by every later one.
static SECRETS: OnceBox<[u64; 7]> = OnceBox::new();

/// The seed of one endpoint and the secrets of the process: what a table needs to be made.
#[derive(Clone, Copy)]
pub(crate) struct Keys {
    seed: u64,
    secrets: &'static [u64; 7],
}

impl core::fmt::Debug for Keys {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Keys").finish_non_exhaustive()
    }
}

impl Keys {
    /// Draw an endpoint's keys: `random` fills 64 bytes, the first 8 are the seed and the other 56 the secrets.
    ///
    /// # Errors
    /// `random`'s error; [`ErrorKind::Config`](crate::ErrorKind::Config) when a secret is zero or two are equal.
    pub(crate) fn draw(random: impl FnOnce(&mut [u8]) -> Result<()>) -> Result<Self> {
        let mut bytes = [0u8; 64];
        random(&mut bytes)?;
        let word = |i: usize| {
            let mut w = [0u8; 8];
            w.copy_from_slice(bytes.get(i * 8..i * 8 + 8).unwrap_or(&[0; 8]));
            u64::from_le_bytes(w)
        };
        let mut secrets = [0u64; 7];
        for (i, s) in secrets.iter_mut().enumerate() {
            *s = word(i + 1);
        }
        let usable = secrets
            .iter()
            .enumerate()
            .all(|(i, s)| *s != 0 && !secrets.iter().take(i).any(|t| t == s));
        if !usable {
            return Err(Error::config("the key store's randomness is not usable"));
        }
        let secrets = SECRETS.get_or_init(|| Box::new(secrets));
        Ok(Self { seed: word(0), secrets })
    }

    /// The keys a discovery is handed to build its own tables, as [`parts`](Self::parts) gave them.
    pub(crate) const fn from_parts(seed: u64, secrets: &'static [u64; 7]) -> Self {
        Self { seed, secrets }
    }

    /// The seed and the secrets.
    pub(crate) const fn parts(self) -> (u64, &'static [u64; 7]) {
        (self.seed, self.secrets)
    }

    /// The build hasher of these keys.
    pub(crate) fn hasher(self) -> Hasher {
        SeedableState::custom(self.seed, self.secrets)
    }

    /// Keys of fixed, non-zero, distinct secrets, for tests that have no key store.
    #[cfg(test)]
    pub(crate) fn for_tests(seed: u64) -> Self {
        Self::with_secrets(seed, [11, 22, 33, 44, 55, 66, 77])
    }

    /// Keys of the given secrets, for tests.
    #[cfg(test)]
    pub(crate) fn with_secrets(seed: u64, secrets: [u64; 7]) -> Self {
        Self {
            seed,
            secrets: Box::leak(Box::new(secrets)),
        }
    }
}

/// An empty map under `keys`.
pub(crate) fn map<K, V>(keys: Keys) -> Map<K, V> {
    HashMap::with_hasher(keys.hasher())
}

/// An empty set under `keys`.
pub(crate) fn set<K>(keys: Keys) -> Set<K> {
    HashSet::with_hasher(keys.hasher())
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use alloc::vec::Vec;
    use core::hash::BuildHasher;

    use super::*;
    use crate::error::ErrorKind;

    fn bytes(seed: u64, secrets: [u64; 7]) -> [u8; 64] {
        let mut b = [0u8; 64];
        b[..8].copy_from_slice(&seed.to_le_bytes());
        for (i, s) in secrets.iter().enumerate() {
            b[8 + i * 8..16 + i * 8].copy_from_slice(&s.to_le_bytes());
        }
        b
    }

    fn draw(b: [u8; 64]) -> Result<Keys> {
        Keys::draw(|out| {
            out.copy_from_slice(&b);
            Ok(())
        })
    }

    #[test]
    fn the_same_keys_hash_a_key_the_same_and_other_keys_differently() {
        let key = [7u8; 32];
        let a = Keys::for_tests(1);
        assert_eq!(a.hasher().hash_one(key), Keys::for_tests(1).hasher().hash_one(key));
        assert_ne!(a.hasher().hash_one(key), Keys::for_tests(2).hasher().hash_one(key));
        let other = Keys::with_secrets(1, [12, 22, 33, 44, 55, 66, 77]);
        assert_ne!(a.hasher().hash_one(key), other.hasher().hash_one(key));
    }

    #[test]
    fn a_map_and_a_set_find_what_they_hold() {
        let keys = Keys::for_tests(9);
        let (mut m, mut s) = (map(keys), set(keys));
        for i in 0..1000u32 {
            m.insert(i, i + 1);
            s.insert(i);
        }
        assert!((0..1000u32).all(|i| m.get(&i) == Some(&(i + 1)) && s.contains(&i)));
        assert!(m.get(&1000).is_none() && !s.contains(&1000));
    }

    #[test]
    fn a_draw_with_a_zero_secret_or_two_equal_secrets_is_refused() {
        for secrets in [[1, 2, 3, 0, 5, 6, 7], [1, 2, 3, 4, 5, 6, 3], [9; 7]] {
            let e = draw(bytes(1, secrets)).unwrap_err();
            assert_eq!(e.kind(), ErrorKind::Config);
        }
        assert!(draw(bytes(1, [1, 2, 3, 4, 5, 6, 7])).is_ok());
    }

    #[test]
    fn a_failing_source_fails_the_draw() {
        assert!(Keys::draw(|_| Err(Error::config("no source"))).is_err());
    }

    #[test]
    fn endpoints_of_a_process_share_the_secrets_and_differ_in_the_seed() {
        let a = draw(bytes(1, [1, 2, 3, 4, 5, 6, 7])).unwrap();
        let b = draw(bytes(2, [8, 9, 10, 11, 12, 13, 14])).unwrap();
        let ((sa, ka), (sb, kb)) = (a.parts(), b.parts());
        assert!(core::ptr::eq(ka, kb), "the secrets are the process's");
        assert_ne!(sa, sb);
        let key = [3u8; 32];
        assert_ne!(a.hasher().hash_one(key), b.hasher().hash_one(key));
        let all: Vec<u64> = ka.to_vec();
        assert!(all.iter().all(|s| *s != 0));
    }
}
