//! [`Tracked`]: the [`Provider`] that does the real work through [`Software`] and records where every secret came
//! from.
//!
//! Invariants: the output of every primitive is exactly the base provider's; the ledger is only written, never
//! consulted to decide a result; a secret is identified by its bytes, so a key handed to the provider as raw bytes
//! (an AEAD key) is matched to the derivation that produced them, and a key with no recorded derivation gets an
//! unknown-provenance term instead of passing silently. Work is counted per call for the CPU cost model, except the
//! public-key computation a Diffie-Hellman needs only for the ledger.

use std::cell::OnceCell;

use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::software::{AeadKey, HpKey, KemCiphertext, KemDecapsKey, KemEncapsKey};
use pinc_crypto::{Aead, Capabilities, CryptoError, Provider, Secret, Software};

use super::registry::{Registry, State, Term, TermId};

/// The provider of one node of the run; see the module docs.
#[derive(Clone, Copy)]
pub struct Tracked {
    reg: &'static Registry,
    node: usize,
    base: Software,
}

impl core::fmt::Debug for Tracked {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "Tracked(node {})", self.node)
    }
}

impl Tracked {
    /// The provider of node `node`, recording into `reg` and computing with `base`.
    pub const fn new(reg: &'static Registry, node: usize, base: Software) -> Self {
        Self { reg, node, base }
    }

    /// The ledger this provider records into.
    pub const fn registry(&self) -> &'static Registry {
        self.reg
    }

    /// The node this provider belongs to.
    pub const fn node(&self) -> usize {
        self.node
    }

    fn with<R>(&self, f: impl FnOnce(&mut State) -> R) -> R {
        self.reg.enter(self.node);
        f(&mut self.reg.st.borrow_mut())
    }
}

/// An AEAD key with the term of the bytes it was built from.
pub struct TrackedAeadKey {
    inner: AeadKey,
    term: TermId,
}

impl TrackedAeadKey {
    /// The key's term in the ledger.
    pub const fn term(&self) -> TermId {
        self.term
    }
}

impl core::fmt::Debug for TrackedAeadKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "AeadKey(term {})", self.term)
    }
}

/// An X25519 secret with its term and (once computed) its public key.
pub struct TrackedX25519 {
    inner: Secret<32>,
    term: TermId,
    public: OnceCell<[u8; 32]>,
}

impl TrackedX25519 {
    /// The secret's term in the ledger.
    pub const fn term(&self) -> TermId {
        self.term
    }
}

impl core::fmt::Debug for TrackedX25519 {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "X25519Secret(term {})", self.term)
    }
}

/// An ML-KEM-768 decapsulation key with its term.
pub struct TrackedDecapsKey {
    inner: KemDecapsKey,
    term: TermId,
}

impl TrackedDecapsKey {
    /// The key's term in the ledger.
    pub const fn term(&self) -> TermId {
        self.term
    }
}

impl core::fmt::Debug for TrackedDecapsKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "KemDecapsKey(term {})", self.term)
    }
}

/// An ML-KEM-768 encapsulation key with the digest the ledger knows it by.
#[derive(Clone)]
pub struct TrackedEncapsKey {
    inner: KemEncapsKey,
    id: [u8; 32],
}

impl core::fmt::Debug for TrackedEncapsKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("KemEncapsKey(..)")
    }
}

impl Provider for Tracked {
    type AeadKey = TrackedAeadKey;
    type HpKey = HpKey;
    type X25519Secret = TrackedX25519;
    type KemEncapsKey = TrackedEncapsKey;
    type KemDecapsKey = TrackedDecapsKey;
    type KemCiphertext = KemCiphertext;

    fn capabilities(&self) -> Capabilities {
        self.base.capabilities()
    }

    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<TrackedAeadKey, CryptoError> {
        let inner = self.base.aead_key(alg, key)?;
        let term = self.with(|st| {
            let uid = st.fresh();
            st.bind(key, Term::Unknown(uid))
        });
        Ok(TrackedAeadKey { inner, term })
    }

    fn seal(
        &self,
        key: &TrackedAeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError> {
        self.reg.enter(self.node);
        let pre = self.reg.pre_seal(aad, buf);
        let tag = self.base.seal(&key.inner, nonce, aad, buf)?;
        self.reg.record_seal(self.node, key.term, nonce, &pre, &tag);
        Ok(tag)
    }

    fn open(
        &self,
        key: &TrackedAeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError> {
        let len = buf.len() as u64;
        self.with(|st| {
            let w = st.work_mut(self.node);
            w.aead += 1;
            w.aead_bytes += len + Aead::TAG_LEN as u64;
        });
        self.base.open(&key.inner, nonce, aad, buf, tag)
    }

    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<HpKey, CryptoError> {
        self.base.hp_key(alg, key)
    }

    fn hp_mask(&self, key: &HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN] {
        self.base.hp_mask(key, sample)
    }

    fn sha256(&self, data: &[u8]) -> [u8; 32] {
        let out = self.base.sha256(data);
        self.with(|st| {
            st.work_mut(self.node).hash_bytes += data.len() as u64;
            let mut inputs = std::collections::BTreeSet::new();
            st.windows(data, 32, &mut inputs);
            if !inputs.is_empty() {
                st.bind_derived(&out, inputs, "sha256");
            }
        });
        out
    }

    fn x25519_secret(&self, seed: &[u8; 32]) -> TrackedX25519 {
        let term = self.with(|st| {
            let uid = st.fresh();
            st.bind(seed, Term::XSk(uid))
        });
        TrackedX25519 {
            inner: self.base.x25519_secret(seed),
            term,
            public: OnceCell::new(),
        }
    }

    fn x25519_public(&self, secret: &TrackedX25519) -> [u8; 32] {
        let pk = *secret.public.get_or_init(|| self.base.x25519_public(&secret.inner));
        self.with(|st| {
            st.pk_owner.entry(pk).or_insert(secret.term);
            st.work_mut(self.node).x25519 += 1;
        });
        pk
    }

    fn x25519_dh(&self, secret: &TrackedX25519, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError> {
        let out = self.base.x25519_dh(&secret.inner, peer)?;
        let mine = *secret.public.get_or_init(|| self.base.x25519_public(&secret.inner));
        self.with(|st| {
            st.pk_owner.entry(mine).or_insert(secret.term);
            let term = match st.pk_owner.get(peer) {
                Some(&p) => Term::Dh(p.min(secret.term), p.max(secret.term)),
                None => Term::DhAdv,
            };
            st.bind(out.expose(), term);
            st.work_mut(self.node).x25519 += 1;
        });
        Ok(out)
    }

    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (TrackedDecapsKey, TrackedEncapsKey) {
        let (dk, ek) = self.base.kem_keygen(d, z);
        let id = self.base.sha256(&self.base.kem_encaps_key_bytes(&ek));
        let mut seed = [0u8; 64];
        seed[..32].copy_from_slice(d);
        seed[32..].copy_from_slice(z);
        let term = self.with(|st| {
            let uid = st.fresh();
            let term = st.bind(&seed, Term::KemSk(uid));
            st.ek_owner.entry(id).or_insert(term);
            st.work_mut(self.node).kem_keygen += 1;
            term
        });
        (TrackedDecapsKey { inner: dk, term }, TrackedEncapsKey { inner: ek, id })
    }

    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<TrackedEncapsKey, CryptoError> {
        let inner = self.base.kem_encaps_key(bytes)?;
        Ok(TrackedEncapsKey {
            inner,
            id: self.base.sha256(bytes),
        })
    }

    fn kem_encaps_key_bytes(&self, ek: &TrackedEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN] {
        self.base.kem_encaps_key_bytes(&ek.inner)
    }

    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<KemCiphertext, CryptoError> {
        self.base.kem_ciphertext(bytes)
    }

    fn kem_ciphertext_bytes(&self, ct: &KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN] {
        self.base.kem_ciphertext_bytes(ct)
    }

    fn kem_encapsulate(&self, ek: &TrackedEncapsKey, m: &[u8; 32]) -> Result<(KemCiphertext, Secret<32>), CryptoError> {
        let (ct, ss) = self.base.kem_encapsulate(&ek.inner, m)?;
        let ct_id = self.base.sha256(&self.base.kem_ciphertext_bytes(&ct));
        self.with(|st| {
            let uid = st.fresh();
            let term = match st.ek_owner.get(&ek.id) {
                Some(&owner) => Term::KemSs { ct: uid, owner },
                None => Term::KemAdv,
            };
            let id = st.bind(ss.expose(), term);
            st.ct_reg.insert(ct_id, (ek.id, id));
            st.work_mut(self.node).kem_encaps += 1;
        });
        Ok((ct, ss))
    }

    fn kem_decapsulate(&self, dk: &TrackedDecapsKey, ct: &KemCiphertext) -> Result<Secret<32>, CryptoError> {
        let ss = self.base.kem_decapsulate(&dk.inner, ct)?;
        let ct_id = self.base.sha256(&self.base.kem_ciphertext_bytes(ct));
        self.with(|st| {
            let made_for_us = st
                .ct_reg
                .get(&ct_id)
                .filter(|(ek_id, _)| st.ek_owner.get(ek_id) == Some(&dk.term))
                .map(|&(_, id)| id);
            if let Some(id) = made_for_us {
                st.alias(ss.expose(), id);
            } else {
                let uid = st.fresh();
                st.bind(ss.expose(), Term::KemRej(dk.term, uid));
            }
            st.work_mut(self.node).kem_decaps += 1;
        });
        Ok(ss)
    }
}
