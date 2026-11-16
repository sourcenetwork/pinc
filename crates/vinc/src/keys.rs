//! The node's keys: an identity in a key store that the engine owns, and the prekeys that stay in software.
//!
//! The identity key lives in a [`KeyStore`] the engine owns outright: signing takes `&mut`, and both the engine (the
//! handshake) and the application (signing its own messages, as a request to the engine) sign, one at a time on the
//! engine's task, so no lock is needed. The ML-KEM prekeys always live in the engine's own [`SoftwareStore`], as a TPM
//! cannot hold them; the two newest generations are kept so a handshake that began under the old prekey still
//! completes.
//!
//! Invariants: no private key leaves a store; a rotated-out prekey is removed, which zeroizes it; errors name the
//! failed operation and never a key.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;

use vinc_crypto::{IdentityAlg, Keypair, NodeId};
use vinc_keystore::{KeyHandle, KeyStore, SoftwareStore};
use vinc_security::{KeyHandle as WireHandle, LocalIdentity, PrekeyInfo};

use crate::error::{Error, ErrorKind, Result};

/// The handle the handshake uses for the identity key.
const IDENTITY: WireHandle = WireHandle(0);
/// How long a prekey serves new dials: 10 minutes.
pub(crate) const PREKEY_LIFE: u64 = 600_000_000_000;
/// How many handshakes one prekey serves before it is replaced.
pub(crate) const PREKEY_USES: u32 = 64;

/// The node's identity: a key in a store, and the public facts about it.
pub struct Identity<S = SoftwareStore> {
    store: S,
    handle: KeyHandle,
    node: NodeId,
    public: Rc<[u8]>,
    /// The seed of the software key the broadcast layer signs with, when the identity was made from a seed this crate
    /// holds; given up once, by [`take_signer`](Self::take_signer). A key pair is far larger than a seed.
    seed: Option<[u8; 32]>,
}

impl<S> core::fmt::Debug for Identity<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Identity")
            .field("alg", &self.node.alg)
            .finish_non_exhaustive()
    }
}

fn key_error(_: vinc_keystore::KeyStoreError) -> Error {
    Error::new(ErrorKind::Config, "the key store refused the request")
}

impl Identity {
    /// The identity of the Ed25519 key made from `seed`, held in a new in-memory store.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store cannot start or the seed is refused.
    pub fn from_seed(seed: &[u8; 32]) -> Result<Self> {
        let mut store = SoftwareStore::new().map_err(key_error)?;
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, seed)
            .map_err(|_| Error::config("the identity seed is not valid"))?;
        let handle = store.insert(kp);
        let mut id = Self::from_store(store, handle)?;
        id.seed = Some(*seed);
        Ok(id)
    }

    /// A new Ed25519 identity from operating system randomness, held in a new in-memory store.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the operating system has no randomness or the store cannot start.
    pub fn generate() -> Result<Self> {
        let mut seed = [0u8; 32];
        SoftwareStore::new()
            .map_err(key_error)?
            .random(&mut seed)
            .map_err(key_error)?;
        let id = Self::from_seed(&seed);
        seed.fill(0);
        id
    }
}

impl<S: KeyStore> Identity<S> {
    /// The identity of the key `handle` in `store`.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store does not hold an identity key under `handle`.
    pub fn from_store(store: S, handle: KeyHandle) -> Result<Self> {
        let (alg, public) = store.public(&handle).map_err(key_error)?;
        let node = NodeId::from_public(alg, &public).map_err(|_| Error::config("the identity key is not valid"))?;
        Ok(Self {
            store,
            handle,
            node,
            public: public.into(),
            seed: None,
        })
    }

    /// The software key the node's broadcast layer signs with, given up once: `None` for an identity that lives in a
    /// key store the crate cannot take a key out of, or after the key was taken.
    pub(crate) fn take_signer(&mut self) -> Option<Box<Keypair>> {
        let mut seed = self.seed.take()?;
        let key = Keypair::from_seed(IdentityAlg::Ed25519, &seed).ok().map(Box::new);
        seed.fill(0);
        key
    }

    /// The node id.
    pub const fn node_id(&self) -> NodeId {
        self.node
    }

    /// The public key bytes.
    pub fn public_key(&self) -> &[u8] {
        &self.public
    }

    /// Sign `msg` with the identity key.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store fails.
    pub fn sign(&mut self, msg: &[u8]) -> Result<Vec<u8>> {
        self.store
            .sign(&self.handle, msg)
            .map(vinc_keystore::Signature::into_bytes)
            .map_err(key_error)
    }

    /// Seal `plain` for storage at rest with the key store; only a store holding the same sealing key opens it.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the store fails.
    pub fn seal(&mut self, plain: &[u8]) -> Result<Vec<u8>> {
        self.store.seal(plain).map_err(key_error)
    }

    /// Open bytes made by [`seal`](Self::seal).
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the bytes were altered or sealed by another store.
    pub fn unseal(&mut self, sealed: &[u8]) -> Result<Vec<u8>> {
        self.store.unseal(sealed).map(|z| z.to_vec()).map_err(key_error)
    }

    /// Fill `out` with random bytes from the store.
    pub(crate) fn random(&mut self, out: &mut [u8]) -> Result<()> {
        self.store.random(out).map_err(key_error)
    }

    pub(crate) fn local(&self) -> Result<LocalIdentity> {
        LocalIdentity::new(self.node.alg, &self.public, IDENTITY)
            .map_err(|_| Error::config("the identity key is not valid"))
    }
}

/// The engine's prekeys: the newest and the one before.
pub(crate) struct Prekeys {
    store: SoftwareStore,
    held: Vec<(u64, KeyHandle)>,
    next: u64,
    rotate_at: u64,
    /// Handshakes the newest prekey has served.
    used: u32,
}

impl Prekeys {
    pub(crate) fn new() -> Result<Self> {
        Ok(Self {
            store: SoftwareStore::new().map_err(key_error)?,
            held: Vec::new(),
            next: 1,
            rotate_at: 0,
            used: 0,
        })
    }

    /// A new prekey to set on the endpoint; drops all but the previous one.
    pub(crate) fn rotate(&mut self, now: u64) -> Result<PrekeyInfo> {
        let (h, ek) = self.store.generate_kem().map_err(key_error)?;
        let gen_id = self.next;
        self.next += 1;
        self.held.push((gen_id, h));
        while self.held.len() > 2 {
            let (_, old) = self.held.remove(0);
            self.store.remove(&old);
        }
        self.rotate_at = now.saturating_add(PREKEY_LIFE);
        self.used = 0;
        Ok(PrekeyInfo::new(ek, WireHandle(gen_id)))
    }

    /// Whether the newest prekey is past its lifetime or has served [`PREKEY_USES`] handshakes.
    pub(crate) const fn due(&self, now: u64) -> bool {
        now >= self.rotate_at || self.used >= PREKEY_USES
    }

    pub(crate) fn decapsulate(&mut self, key: WireHandle, ct: &[u8]) -> Option<vinc_crypto::Secret<32>> {
        if key.0 == self.next.saturating_sub(1) {
            self.used = self.used.saturating_add(1);
        }
        let (_, h) = self.held.iter().find(|(g, _)| *g == key.0)?;
        self.store.decapsulate(h, ct).ok()
    }
}

/// Whether a wire handle names the identity key.
pub(crate) const fn is_identity(key: WireHandle) -> bool {
    key.0 == IDENTITY.0
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    #[test]
    fn a_prekey_is_replaced_after_64_handshakes_or_its_lifetime() {
        let mut p = Prekeys::new().unwrap();
        assert!(p.due(0), "no prekey yet");
        p.rotate(1).unwrap();
        assert!(!p.due(2));
        let newest = WireHandle(1);
        for _ in 0..PREKEY_USES - 1 {
            let _ = p.decapsulate(newest, &[]);
        }
        assert!(!p.due(2), "63 handshakes");
        let _ = p.decapsulate(newest, &[]);
        assert!(p.due(2), "the 64th");
        p.rotate(3).unwrap();
        assert!(!p.due(4), "a new prekey starts at zero");
        // A handshake that began under the previous prekey does not count against the new one.
        let _ = p.decapsulate(newest, &[]);
        assert!(!p.due(4));
        assert!(p.due(3 + PREKEY_LIFE), "its lifetime");
    }
}
