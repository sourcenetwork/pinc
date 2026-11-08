//! [`SoftwareStore`]: keys held in process memory.
//!
//! Invariants: every private key and the sealing key are zeroized when the store is dropped or the key is removed;
//! randomness comes from the operating system; the sealing key exists only in memory, so data sealed by one store
//! value cannot be unsealed by another.

use std::collections::HashMap;

use vinc_crypto::provider::KEM_ENCAPS_KEY_LEN;
use vinc_crypto::software::KemDecapsKey;
use vinc_crypto::{IdentityAlg, Keypair, Provider, Secret, Software, identity};
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
    keys: HashMap<u64, Entry>,
    seal_key: Secret<{ sealed::KEY_LEN }>,
}

impl core::fmt::Debug for SoftwareStore {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("SoftwareStore(..)")
    }
}

impl SoftwareStore {
    /// An empty store with a fresh sealing key.
    ///
    /// # Errors
    /// [`KeyStoreError::Entropy`] if the operating system cannot provide random bytes.
    pub fn new() -> Result<Self> {
        let mut key = Zeroizing::new([0u8; sealed::KEY_LEN]);
        fill_os(key.as_mut_slice())?;
        Ok(Self {
            keys: HashMap::new(),
            seal_key: Secret::new(*key),
        })
    }

    /// Add an existing key pair.
    pub fn insert(&mut self, keypair: Keypair) -> KeyHandle {
        self.add(Entry::Identity(Box::new(keypair)))
    }

    /// Generate a key pair for `alg` from operating system randomness.
    ///
    /// # Errors
    /// [`KeyStoreError::Entropy`] if randomness is unavailable; [`KeyStoreError::Crypto`] if no valid seed was drawn.
    pub fn generate(&mut self, alg: IdentityAlg) -> Result<KeyHandle> {
        let mut seed = Zeroizing::new(vec![0u8; alg.seed_len()]);
        for _ in 0..SEED_RETRIES {
            fill_os(&mut seed)?;
            match Keypair::from_seed(alg, &seed) {
                Ok(kp) => return Ok(self.insert(kp)),
                Err(vinc_crypto::CryptoError::InvalidSecretKey) => {}
                Err(e) => return Err(e.into()),
            }
        }
        Err(vinc_crypto::CryptoError::InvalidSecretKey.into())
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
        fill_os(d.as_mut_slice())?;
        fill_os(z.as_mut_slice())?;
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
pub(crate) fn fill_os(out: &mut [u8]) -> Result<()> {
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
        fill_os(out)
    }

    fn seal(&mut self, plaintext: &[u8]) -> Result<Vec<u8>> {
        let mut nonce = [0u8; 12];
        fill_os(&mut nonce)?;
        sealed::encrypt(&self.seal_key, &[VERSION], nonce, plaintext)
    }

    fn unseal(&mut self, sealed: &[u8]) -> Result<Zeroizing<Vec<u8>>> {
        match sealed.split_first() {
            Some((&VERSION, _)) => sealed::decrypt(&self.seal_key, sealed, 1),
            _ => Err(KeyStoreError::InvalidSealed),
        }
    }
}

/// The first byte of a software-sealed value.
const VERSION: u8 = 1;
