//! One-shot hybrid encryption to a recipient's static keys, with no live handshake.
//!
//! The sender draws a fresh ephemeral X25519 key and a fresh ML-KEM message, runs X25519 against the recipient's
//! static X25519 key and encapsulates to the recipient's static ML-KEM-768 key, then derives
//! `key = expand(extract(ck0, ss_K || ss_X), slice key, th)` where `ck0` is the public starting chain of this layer
//! and `th` hashes a transcript of every public value: the ephemeral key, the recipient's static X25519 and ML-KEM
//! keys, the ML-KEM ciphertext, the recipient node id, its key epoch and the bundle id. Each sealed slice is
//! ChaCha20-Poly1305 under that key with a nonce derived from the slice index and `th || index` as associated data.
//!
//! Invariants: the key depends on both shared secrets, so breaking either X25519 or ML-KEM alone is not enough; a
//! different recipient, epoch, bundle id or public value gives a different key; a nonce is never reused under a key
//! because the key is unique to the bundle and a slice index is sealed once. There is no forward secrecy beyond the
//! recipient's static-key rotation: the recipient record carries the current keys and their epoch, and rotation is
//! configuration. Secrets are zeroized; nothing here allocates, reads randomness (the seeds are inputs) or panics.

use vinc_crypto::provider::{KEM_ENCAPS_KEY_LEN, Provider};
use vinc_crypto::{Aead, NodeId, Secret, Transcript, expand, extract};
use zeroize::Zeroize;

use crate::error::DtnError;
use crate::head::{BundleId, Envelope, Head, absorb_node};
use crate::hlc::Hlc;
use crate::labels;
use crate::layout::TAG_LEN;

/// A recipient's published static keys: what a sender needs, and nothing secret.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecipientKeys {
    /// The recipient's node id.
    pub node: NodeId,
    /// The epoch of these static keys; a rotation bumps it.
    pub epoch: u32,
    /// The recipient's static ML-KEM-768 encapsulation key.
    pub kem_ek: [u8; KEM_ENCAPS_KEY_LEN],
    /// The recipient's static X25519 public key.
    pub x25519: [u8; 32],
}

/// The sender's per-bundle randomness, supplied by the caller and used once.
pub struct SealSeeds {
    /// Seed of the ephemeral X25519 key.
    pub eph_x25519: Secret<32>,
    /// The ML-KEM encapsulation message.
    pub kem_m: Secret<32>,
}

/// The slice cipher of one bundle: the AEAD key and the transcript hash bound into every slice.
pub struct Cipher<P: Provider> {
    key: P::AeadKey,
    th: [u8; 32],
}

impl<P: Provider> core::fmt::Debug for Cipher<P> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Cipher(..)")
    }
}

/// The nonce of data slice `index`: four zero bytes and the big-endian index.
fn nonce(index: u64) -> [u8; Aead::NONCE_LEN] {
    let mut n = [0u8; Aead::NONCE_LEN];
    if let Some(tail) = n.get_mut(4..) {
        tail.copy_from_slice(&index.to_be_bytes());
    }
    n
}

/// The associated data of data slice `index`: the transcript hash and the index.
fn aad(th: &[u8; 32], index: u64) -> [u8; 40] {
    let mut a = [0u8; 40];
    let (head, tail) = a.split_at_mut(32);
    head.copy_from_slice(th);
    tail.copy_from_slice(&index.to_be_bytes());
    a
}

/// The transcript hash over every public value of the exchange.
fn transcript_hash(rcpt: &RecipientKeys, eph: &[u8; 32], kem_ct: &[u8], id: &BundleId) -> [u8; 32] {
    let mut t = Transcript::with_label(labels::TRANSCRIPT);
    t.absorb(eph);
    t.absorb(&rcpt.x25519);
    t.absorb(&rcpt.kem_ek);
    t.absorb(kem_ct);
    absorb_node(&mut t, &rcpt.node);
    t.absorb(&rcpt.epoch.to_be_bytes());
    t.absorb(&id.0);
    t.snapshot()
}

/// `key = expand(extract(ck0, ss_K || ss_X), th)` as a ready AEAD key.
fn derive<P: Provider>(p: &P, ss_k: &Secret<32>, ss_x: &Secret<32>, th: [u8; 32]) -> Result<Cipher<P>, DtnError> {
    let ck0 = Transcript::with_label(labels::CHAIN).snapshot();
    let mut ikm = [0u8; 64];
    let (a, b) = ikm.split_at_mut(32);
    a.copy_from_slice(ss_k.expose());
    b.copy_from_slice(ss_x.expose());
    let mut prk = extract(&ck0, &ikm);
    let mut key = [0u8; 32];
    expand(&prk, labels::SLICE_KEY, &th, &mut key);
    let aead = p.aead_key(Aead::ChaCha20Poly1305, &key);
    ikm.zeroize();
    prk.zeroize();
    key.zeroize();
    Ok(Cipher { key: aead?, th })
}

/// The sender's half: encapsulate to `rcpt`, returning the bundle id, the envelope for the head and the cipher.
///
/// # Errors
/// [`DtnError::Crypto`] if the recipient's X25519 key is a low-order point or the KEM fails.
pub fn encapsulate<P: Provider>(
    p: &P,
    rcpt: &RecipientKeys,
    source: &NodeId,
    created: Hlc,
    seeds: &SealSeeds,
) -> Result<(BundleId, Envelope, Cipher<P>), DtnError> {
    let eph = p.x25519_secret(seeds.eph_x25519.expose());
    let eph_pub = p.x25519_public(&eph);
    let ss_x = p.x25519_dh(&eph, &rcpt.x25519)?;
    let ek = p.kem_encaps_key(&rcpt.kem_ek)?;
    let (ct, ss_k) = p.kem_encapsulate(&ek, seeds.kem_m.expose())?;
    let kem_ct = p.kem_ciphertext_bytes(&ct);
    let id = BundleId::derive(source, created, &eph_pub);
    let th = transcript_hash(rcpt, &eph_pub, &kem_ct, &id);
    let cipher = derive(p, &ss_k, &ss_x, th)?;
    let envelope = Envelope {
        epoch: rcpt.epoch,
        eph_x25519: eph_pub,
        kem_ct,
    };
    Ok((id, envelope, cipher))
}

/// The recipient's half: decapsulate the head's envelope with the static secret keys.
///
/// `own` is the recipient's own published record (its keys must match the secrets); the head must be addressed to
/// `own.node` under `own.epoch`.
///
/// # Errors
/// [`DtnError::WrongRecipient`] for another node or epoch; [`DtnError::Crypto`] for a low-order ephemeral key. A
/// forged KEM ciphertext does not error here: ML-KEM rejects implicitly, so the key differs and the first slice
/// fails authentication.
pub fn decapsulate<P: Provider>(
    p: &P,
    own: &RecipientKeys,
    kem_dk: &P::KemDecapsKey,
    x25519_secret: &P::X25519Secret,
    head: &Head,
) -> Result<Cipher<P>, DtnError> {
    if head.destination != own.node || head.envelope.epoch != own.epoch {
        return Err(DtnError::WrongRecipient);
    }
    let ss_x = p.x25519_dh(x25519_secret, &head.envelope.eph_x25519)?;
    let ct = p.kem_ciphertext(&head.envelope.kem_ct)?;
    let ss_k = p.kem_decapsulate(kem_dk, &ct)?;
    let th = transcript_hash(own, &head.envelope.eph_x25519, &head.envelope.kem_ct, &head.id);
    derive(p, &ss_k, &ss_x, th)
}

impl<P: Provider> Cipher<P> {
    /// Seal data slice `index` in place: `buf` is the plaintext and the detached tag is returned.
    ///
    /// # Errors
    /// [`DtnError::Crypto`] if `buf` is beyond the AEAD's limit.
    pub fn seal_slice(&self, p: &P, index: u64, buf: &mut [u8]) -> Result<[u8; TAG_LEN], DtnError> {
        Ok(p.seal(&self.key, &nonce(index), &aad(&self.th, index), buf)?)
    }

    /// Open data slice `index` in place with its tag.
    ///
    /// # Errors
    /// [`DtnError::Crypto`] with [`vinc_crypto::CryptoError::Authentication`] if the slice, the index or the key is
    /// wrong.
    pub fn open_slice(&self, p: &P, index: u64, buf: &mut [u8], tag: &[u8; TAG_LEN]) -> Result<(), DtnError> {
        Ok(p.open(&self.key, &nonce(index), &aad(&self.th, index), buf, tag)?)
    }
}
