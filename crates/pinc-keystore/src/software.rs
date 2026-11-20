//! [`SoftwareStore`]: keys held in process memory.
//!
//! Invariants: every private key and the sealing key are zeroized when the store is dropped or the key is removed;
//! randomness comes from the operating system (`new`, with `std`) or from a generator the host seeds (`from_entropy`);
//! the sealing key exists only in memory, so data sealed by one store value cannot be unsealed by another,
//! unless both were built from the same entropy.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec;
use alloc::vec::Vec;

use pinc_crypto::provider::KEM_ENCAPS_KEY_LEN;
use pinc_crypto::software::KemDecapsKey;
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Provider, Secret, Software, identity};
use zeroize::Zeroizing;

use crate::{KeyHandle, KeyStore, KeyStoreError, Result, Signature, sealed};

/// How many times key generation redraws a seed that falls outside the P-256 scalar range (probability about 2^-32).
const SEED_RETRIES: usize = 8;

enum Entry {
    Identity(Box<Keypair>),
    Kem(Box<KemDecapsKey>),
}

/// A [`KeyStore`] that keeps identity keys, ML-KEM-768 prekeys and the sealing key in memory.
///
/// Every algorithm of [`IdentityAlg`] is supported. Keys the TPM cannot hold (Ed25519, ML-DSA-65, hybrid and ML-KEM)
/// belong here even when the node's P-256 identity lives in a TPM.
pub struct SoftwareStore {
    keys: BTreeMap<u64, Entry>,
    /// `None` only if the generator could not give the sealing key, which a 32-byte draw never does.
    seal_key: Option<Secret<{ sealed::KEY_LEN }>>,
    source: Source,
}

/// Where a store's random bytes come from.
enum Source {
    #[cfg(feature = "std")]
    Os,
    Drbg(Drbg),
}

impl Source {
    fn fill(&mut self, out: &mut [u8]) -> Result<()> {
        match self {
            #[cfg(feature = "std")]
            Self::Os => os_random(out),
            Self::Drbg(drbg) => Ok(drbg.fill(out)?),
        }
    }
}

impl core::fmt::Debug for SoftwareStore {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("SoftwareStore(..)")
    }
}

impl SoftwareStore {
    /// An empty store with a fresh sealing key, drawing every random byte from the operating system.
    ///
    /// # Errors
    /// [`KeyStoreError::Entropy`] if the operating system cannot provide random bytes.
    #[cfg(feature = "std")]
    pub fn new() -> Result<Self> {
        let mut key = Zeroizing::new([0u8; sealed::KEY_LEN]);
        os_random(key.as_mut_slice())?;
        Ok(Self {
            keys: BTreeMap::new(),
            seal_key: Some(Secret::new(*key)),
            source: Source::Os,
        })
    }

    /// An empty store whose random bytes and sealing key come from a generator seeded with `entropy`.
    ///
    /// The host must give fresh entropy at every start: the same entropy gives the same keys, nonces and sealing key.
    /// Use [`SoftwareStore::reseed`] to mix in more entropy later.
    pub fn from_entropy(entropy: [u8; 32]) -> Self {
        let mut drbg = Drbg::new(&entropy);
        let mut key = Zeroizing::new([0u8; sealed::KEY_LEN]);
        let seal_key = drbg.fill(key.as_mut_slice()).is_ok().then(|| Secret::new(*key));
        Self {
            keys: BTreeMap::new(),
            seal_key,
            source: Source::Drbg(drbg),
        }
    }

    /// Mix `entropy` into the generator of a store made by [`SoftwareStore::from_entropy`]. A store that draws from
    /// the operating system ignores it.
    pub fn reseed(&mut self, entropy: &[u8; 32]) {
        match &mut self.source {
            Source::Drbg(drbg) => drbg.reseed(entropy),
            #[cfg(feature = "std")]
            Source::Os => {}
        }
    }

    /// Add an existing key pair.
    pub fn insert(&mut self, keypair: Keypair) -> KeyHandle {
        self.add(Entry::Identity(Box::new(keypair)))
    }

    /// Generate a key pair for `alg` from the store's random source.
    ///
    /// # Errors
    /// [`KeyStoreError::Entropy`] if randomness is unavailable; [`KeyStoreError::Crypto`] if no valid seed was drawn.
    pub fn generate(&mut self, alg: IdentityAlg) -> Result<KeyHandle> {
        let mut seed = Zeroizing::new(vec![0u8; alg.seed_len()]);
        for _ in 0..SEED_RETRIES {
            self.source.fill(&mut seed)?;
            match Keypair::from_seed(alg, &seed) {
                Ok(kp) => return Ok(self.insert(kp)),
                Err(pinc_crypto::CryptoError::InvalidSecretKey) => {}
                Err(e) => return Err(e.into()),
            }
        }
        Err(pinc_crypto::CryptoError::InvalidSecretKey.into())
    }

    /// Add an ML-KEM-768 decapsulation key.
    pub fn insert_kem(&mut self, key: KemDecapsKey) -> KeyHandle {
        self.add(Entry::Kem(Box::new(key)))
    }

    /// Generate an ML-KEM-768 prekey; returns its handle and the encapsulation (public) key bytes.
    ///
    /// # Errors
    /// [`KeyStoreError::Entropy`] if randomness is unavailable.
    pub fn generate_kem(&mut self) -> Result<(KeyHandle, [u8; KEM_ENCAPS_KEY_LEN])> {
        let mut d = Zeroizing::new([0u8; 32]);
        let mut z = Zeroizing::new([0u8; 32]);
        self.source.fill(d.as_mut_slice())?;
        self.source.fill(z.as_mut_slice())?;
        let (dk, ek) = Software.kem_keygen(&d, &z);
        Ok((self.insert_kem(dk), Software.kem_encaps_key_bytes(&ek)))
    }

    /// Drop a key, zeroizing it; returns whether it was present.
    pub fn remove(&mut self, key: &KeyHandle) -> bool {
        self.keys.remove(&key.id()).is_some()
    }

    fn add(&mut self, entry: Entry) -> KeyHandle {
        let handle = KeyHandle::next();
        self.keys.insert(handle.id(), entry);
        handle
    }

    fn identity(&self, key: &KeyHandle) -> Result<&Keypair> {
        match self.keys.get(&key.id()) {
            Some(Entry::Identity(kp)) => Ok(kp),
            Some(Entry::Kem(_)) => Err(KeyStoreError::WrongKeyKind),
            None => Err(KeyStoreError::UnknownKey),
        }
    }
}

/// Fill `out` from the operating system.
///
/// # Errors
/// [`KeyStoreError::Entropy`] if the operating system cannot provide random bytes.
#[cfg(feature = "std")]
pub fn os_random(out: &mut [u8]) -> Result<()> {
    getrandom::fill(out).map_err(|_| KeyStoreError::Entropy)
}

impl KeyStore for SoftwareStore {
    fn sign(&mut self, key: &KeyHandle, msg: &[u8]) -> Result<Signature> {
        let kp = self.identity(key)?;
        let alg = kp.alg();
        let mut out = vec![0u8; alg.signature_len()];
        let n = kp.sign(msg, &mut out)?;
        out.truncate(n);
        Ok(Signature::new(alg, out))
    }

    fn public(&self, key: &KeyHandle) -> Result<(IdentityAlg, Vec<u8>)> {
        let kp = self.identity(key)?;
        let mut pk = vec![0u8; identity::MAX_PUBLIC_KEY_LEN];
        let n = kp.public_key(&mut pk)?;
        pk.truncate(n);
        Ok((kp.alg(), pk))
    }

    fn decapsulate(&mut self, key: &KeyHandle, ct: &[u8]) -> Result<Secret<32>> {
        match self.keys.get(&key.id()) {
            Some(Entry::Kem(dk)) => {
                let ct = Software.kem_ciphertext(ct)?;
                Ok(Software.kem_decapsulate(dk, &ct)?)
            }
            Some(Entry::Identity(_)) => Err(KeyStoreError::WrongKeyKind),
            None => Err(KeyStoreError::UnknownKey),
        }
    }

    fn random(&mut self, out: &mut [u8]) -> Result<()> {
        self.source.fill(out)
    }

    fn seal(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        let mut nonce = [0u8; 12];
        self.source.fill(&mut nonce)?;
        let key = self.seal_key.as_ref().ok_or(KeyStoreError::Entropy)?;
        sealed::encrypt(key, &[VERSION], nonce, plaintext)
    }

    fn unseal(&mut self, sealed: &[u8]) -> Result<Zeroizing<Vec<u8>>> {
        match sealed.split_first() {
            Some((&VERSION, _)) => sealed::decrypt(self.seal_key.as_ref().ok_or(KeyStoreError::Entropy)?, sealed, 1),
            _ => Err(KeyStoreError::InvalidSealed),
        }
    }

    fn refresh(&mut self, fresh: &mut dyn FnMut(&mut [u8; 32]) -> bool) {
        if matches!(self.source, Source::Drbg(_)) {
            let mut bytes = Zeroizing::new([0u8; 32]);
            if fresh(&mut bytes) {
                self.reseed(&bytes);
            }
        }
    }
}

/// The first byte of a software-sealed value.
const VERSION: u8 = 1;
