//! Where PINC's long-term keys live.
//!
//! A [`KeyStore`] signs with identity keys, decapsulates ML-KEM-768 prekey ciphertexts, supplies random bytes and
//! seals data (persisted resumption tickets) at rest. Calls block: a driver runs a store that talks to hardware on a
//! worker thread. [`SoftwareStore`] keeps everything in process memory; with the `hwenc` feature, `TpmStore`
//! keeps ECDSA P-256 identity keys and the sealing key in a TPM 2.0, through a pure-Rust client (no C library).
//!
//! Signatures come back in the exact form [`pinc_crypto::identity::verify`] accepts for the key's algorithm.
//!
//! A TPM holds only ECDSA P-256 keys among PINC's algorithms. Ed25519, ML-DSA-65, hybrid and ML-KEM keys stay in a
//! [`SoftwareStore`]; asking a `TpmStore` for one is a typed [`KeyStoreError::Unsupported`], never a fallback.
//!
//! [`KeyHost`] answers the handshake's key requests ([`pinc_security::KeyRequest`]) from a store, the one host path
//! both the endpoint and a relay carrier use.
//!
//! Invariants: errors are small `Copy` values with one-sentence messages and no key material; private keys never
//! appear in `Debug` output; keys held in memory are zeroized when dropped.
//!
//! The crate is `no_std` with `alloc`. The `std` feature adds the operating system as a source of randomness
//! (`SoftwareStore::new`, `os_random`); without it a host seeds the store with entropy of its own
//! (`SoftwareStore::from_entropy`).
#![no_std]
#![forbid(unsafe_code)]

extern crate alloc;
#[cfg(feature = "std")]
extern crate std;

mod error;
mod host;
mod sealed;
mod software;
#[cfg(feature = "hwenc")]
pub mod tpm;

use alloc::vec::Vec;
use core::sync::atomic::{AtomicUsize, Ordering};

use pinc_crypto::{IdentityAlg, NodeId, Secret};
use zeroize::Zeroizing;

pub use error::{KeyStoreError, Result};
pub use host::KeyHost;
pub use software::SoftwareStore;
#[cfg(feature = "std")]
pub use software::os_random;
#[cfg(feature = "hwenc")]
pub use tpm::{TpmConfig, TpmStore};

/// Names one key in the store that issued it.
///
/// Handles are unique across stores in a process; a handle presented to another store is
/// [`KeyStoreError::UnknownKey`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct KeyHandle(u64);

impl KeyHandle {
    pub(crate) fn next() -> Self {
        // A `usize` counter: 32-bit targets have no 64-bit atomics. A wrap needs 2^32 allocations between two live handles.
        static NEXT: AtomicUsize = AtomicUsize::new(1);
        Self(NEXT.fetch_add(1, Ordering::Relaxed) as u64)
    }

    pub(crate) const fn id(&self) -> u64 {
        self.0
    }
}

/// A signature and the algorithm that made it, in the form [`pinc_crypto::identity::verify`] accepts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Signature {
    alg: IdentityAlg,
    bytes: Vec<u8>,
}

impl Signature {
    pub(crate) const fn new(alg: IdentityAlg, bytes: Vec<u8>) -> Self {
        Self { alg, bytes }
    }

    /// The algorithm of the key that signed.
    pub const fn alg(&self) -> IdentityAlg {
        self.alg
    }

    /// The signature bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Take the signature bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

/// Where long-term keys live: signing, decapsulation, randomness and sealing at rest.
pub trait KeyStore: Send {
    /// Sign `msg` with the identity key `key`.
    ///
    /// # Errors
    /// [`KeyStoreError::UnknownKey`] or [`KeyStoreError::WrongKeyKind`] for a bad handle; a backend failure
    /// otherwise.
    fn sign(&mut self, key: &KeyHandle, msg: &[u8]) -> Result<Signature>;

    /// The algorithm and public key bytes of the identity key `key`.
    ///
    /// # Errors
    /// [`KeyStoreError::UnknownKey`] or [`KeyStoreError::WrongKeyKind`] for a bad handle.
    fn public(&self, key: &KeyHandle) -> Result<(IdentityAlg, Vec<u8>)>;

    /// The node id of the identity key `key`.
    ///
    /// # Errors
    /// As [`KeyStore::public`].
    fn node_id(&self, key: &KeyHandle) -> Result<NodeId> {
        let (alg, pk) = self.public(key)?;
        Ok(NodeId::from_public(alg, &pk)?)
    }

    /// ML-KEM-768 decapsulation of `ct` with the prekey `key`. A forged ciphertext gives a pseudo-random secret,
    /// never an error.
    ///
    /// # Errors
    /// [`KeyStoreError::Unsupported`] if the store cannot hold ML-KEM keys; [`KeyStoreError::WrongKeyKind`] if `key` is
    /// not a KEM key; [`KeyStoreError::Crypto`] if `ct` has the wrong length.
    fn decapsulate(&mut self, key: &KeyHandle, ct: &[u8]) -> Result<Secret<32>>;

    /// Fill `out` with random bytes from the store's source.
    ///
    /// # Errors
    /// [`KeyStoreError::Entropy`] or a backend failure.
    fn random(&mut self, out: &mut [u8]) -> Result<()>;

    /// Seal `plaintext` for storage at rest. Only this store (or one holding the same sealing key) can unseal it.
    ///
    /// # Errors
    /// A backend failure.
    fn seal(&mut self, plaintext: &[u8]) -> Result<Vec<u8>>;

    /// Recover data sealed by [`KeyStore::seal`].
    ///
    /// # Errors
    /// [`KeyStoreError::InvalidSealed`] if the bytes are malformed or were altered; a backend failure otherwise.
    fn unseal(&mut self, sealed: &[u8]) -> Result<Zeroizing<Vec<u8>>>;

    /// The caller offers fresh entropy. A store that draws from a generator the host seeded calls `fresh` once and,
    /// if it returns true, mixes the 32 bytes in; a store with a source of its own does not call it.
    fn refresh(&mut self, _fresh: &mut dyn FnMut(&mut [u8; 32]) -> bool) {}
}
