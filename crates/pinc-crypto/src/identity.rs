//! Identities: signature algorithms, software key pairs and node ids.
//!
//! Invariants: verification is always available and never panics; a signature is accepted only in its canonical
//! form (Ed25519 by `verify_strict`, ECDSA only with a low `s`); a [`NodeId`] is a pure function of the algorithm
//! tag and the public key; a hybrid signature is valid only if both halves verify, and both sign a digest that is
//! domain-separated from the plain algorithms. Signing here is the software path: it is deterministic and takes any
//! randomness from the caller.
//!
//! ML-DSA-65 keys hold their expanded matrix inline on a target without an allocator (about 64 KiB, for the hybrid
//! too): there is nowhere else for it to stay. With the `alloc` feature (default) the expanded key is boxed once, in
//! [`Keypair::from_seed`], and a key pair of any algorithm is 240 bytes. Storage is not construction:
//! [`Keypair::from_seed`] for ML-DSA-65 and the hybrid builds the 64 KiB expanded key in the caller's frame before
//! the box copies it out, in every build, so those two algorithms need several hundred KiB of stack to construct a
//! key pair (measured on aarch64: 512 KiB with this crate optimised, 256 KiB overflowing; 1 MiB at opt-level 0);
//! Ed25519 and P-256 construct on 8 KiB.

#[cfg(feature = "alloc")]
extern crate alloc;

use ed25519_dalek::{Signer as _, SigningKey as EdSigningKey, VerifyingKey as EdVerifyingKey};
use ml_dsa::{KeyExport as _, Keypair as _, MlDsa65, Seed, Signature as MlSignature, SigningKey as MlSigningKey};
use p256::ecdsa::signature::Verifier as _;
use p256::ecdsa::{Signature as P256Signature, SigningKey as P256SigningKey, VerifyingKey as P256VerifyingKey};

use crate::{CryptoError, ct_eq, labels};

const ED_PK: usize = 32;
const ED_SIG: usize = 64;
const P256_PK: usize = 33;
const P256_SIG: usize = 64;
const ML_PK: usize = 1952;
const ML_SIG: usize = 3309;

/// The longest public key of any algorithm.
pub const MAX_PUBLIC_KEY_LEN: usize = ED_PK + ML_PK;
/// The longest signature of any algorithm.
pub const MAX_SIGNATURE_LEN: usize = ED_SIG + ML_SIG;

/// A signature algorithm, with a stable one-byte wire tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum IdentityAlg {
    /// Ed25519: a 32-byte public key and a 64-byte signature.
    Ed25519 = 1,
    /// ECDSA over P-256 with SHA-256: a 33-byte compressed SEC1 public key and a 64-byte `r || s` signature.
    EcdsaP256 = 2,
    /// ML-DSA-65 (FIPS 204): a 1952-byte public key and a 3309-byte signature.
    MlDsa65 = 3,
    /// Ed25519 plus ML-DSA-65: the two public keys and the two signatures concatenated, Ed25519 first.
    Hybrid = 4,
}

impl IdentityAlg {
    /// The wire tag.
    pub const fn tag(self) -> u8 {
        self as u8
    }

    /// The algorithm for a wire tag, or `None` for an unknown one.
    pub const fn from_tag(tag: u8) -> Option<Self> {
        match tag {
            1 => Some(Self::Ed25519),
            2 => Some(Self::EcdsaP256),
            3 => Some(Self::MlDsa65),
            4 => Some(Self::Hybrid),
            _ => None,
        }
    }

    /// The length of this algorithm's public key.
    pub const fn public_key_len(self) -> usize {
        match self {
            Self::Ed25519 => ED_PK,
            Self::EcdsaP256 => P256_PK,
            Self::MlDsa65 => ML_PK,
            Self::Hybrid => ED_PK + ML_PK,
        }
    }

    /// The length of this algorithm's signature.
    pub const fn signature_len(self) -> usize {
        match self {
            Self::Ed25519 => ED_SIG,
            Self::EcdsaP256 => P256_SIG,
            Self::MlDsa65 => ML_SIG,
            Self::Hybrid => ED_SIG + ML_SIG,
        }
    }

    /// The length of the seed [`Keypair::from_seed`] takes.
    pub const fn seed_len(self) -> usize {
        match self {
            Self::Hybrid => 64,
            _ => 32,
        }
    }
}

/// A node identifier: the algorithm and 32 bytes derived from the public key.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct NodeId {
    /// The identity algorithm.
    pub alg: IdentityAlg,
    /// For Ed25519 the public key itself; otherwise the BLAKE3 `derive_key` of `alg tag || public key`.
    pub bytes: [u8; 32],
}

impl NodeId {
    /// The node id of a public key.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `public_key` has the wrong length for `alg`.
    pub fn from_public(alg: IdentityAlg, public_key: &[u8]) -> Result<Self, CryptoError> {
        if public_key.len() != alg.public_key_len() {
            return Err(CryptoError::InvalidLength);
        }
        let bytes = if let (IdentityAlg::Ed25519, Ok(pk)) = (alg, <[u8; 32]>::try_from(public_key)) {
            pk
        } else {
            let mut h = blake3::Hasher::new_derive_key(labels::NODE_ID);
            h.update(&[alg.tag()]);
            h.update(public_key);
            *h.finalize().as_bytes()
        };
        Ok(Self { alg, bytes })
    }

    /// Whether this id is the node id of `public_key` under `alg` (compared in constant time).
    pub fn matches(&self, alg: IdentityAlg, public_key: &[u8]) -> bool {
        Self::from_public(alg, public_key).is_ok_and(|id| id.alg == self.alg && ct_eq(&id.bytes, &self.bytes))
    }
}

/// The 32-byte digest both halves of a hybrid signature sign, so neither half is a valid plain signature.
fn hybrid_digest(msg: &[u8]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(labels::HYBRID_SIGNATURE);
    h.update(msg);
    *h.finalize().as_bytes()
}

/// ML-DSA-65 signs `M' = 0x00 || len(ctx) || ctx || msg` (FIPS 204 Algorithm 2) with an empty context.
fn ml_sign(key: &MlSigningKey<MlDsa65>, msg: &[u8], rnd: &[u8; 32]) -> [u8; ML_SIG] {
    key.expanded_key()
        .sign_internal(&[&[0, 0], msg], &(*rnd).into())
        .encode()
        .into()
}

/// Verify an ML-DSA-65 signature made with the FIPS 204 context string `ctx` (at most 255 bytes).
///
/// [`verify`] is this with an empty context.
///
/// # Errors
/// [`CryptoError::InvalidLength`] for a wrong-sized key or signature or a context over 255 bytes,
/// [`CryptoError::InvalidSignature`] otherwise.
pub fn verify_ml_dsa_65(public_key: &[u8], ctx: &[u8], msg: &[u8], sig: &[u8]) -> Result<(), CryptoError> {
    if ctx.len() > 255 || sig.len() != ML_SIG {
        return Err(CryptoError::InvalidLength);
    }
    let pk: &[u8; ML_PK] = public_key.try_into().map_err(|_| CryptoError::InvalidLength)?;
    let vk = ml_dsa::VerifyingKey::<MlDsa65>::decode(&(*pk).into());
    let sig = MlSignature::<MlDsa65>::try_from(sig).map_err(|_| CryptoError::InvalidSignature)?;
    vk.verify_with_context(msg, ctx, &sig)
        .then_some(())
        .ok_or(CryptoError::InvalidSignature)
}

fn ed_verify(public_key: &[u8], msg: &[u8], sig: &[u8]) -> Result<(), CryptoError> {
    let pk: &[u8; ED_PK] = public_key.try_into().map_err(|_| CryptoError::InvalidLength)?;
    let sig: &[u8; ED_SIG] = sig.try_into().map_err(|_| CryptoError::InvalidLength)?;
    let vk = EdVerifyingKey::from_bytes(pk).map_err(|_| CryptoError::InvalidPublicKey)?;
    vk.verify_strict(msg, &ed25519_dalek::Signature::from_bytes(sig))
        .map_err(|_| CryptoError::InvalidSignature)
}

fn p256_verify(public_key: &[u8], msg: &[u8], sig: &[u8]) -> Result<(), CryptoError> {
    if public_key.len() != P256_PK {
        return Err(CryptoError::InvalidLength);
    }
    // Only the compressed form: SEC1 also allows the compact form (tag 5) of the same length, a second encoding of
    // the same key that would give it a second node id.
    if !matches!(public_key.first(), Some(2 | 3)) {
        return Err(CryptoError::InvalidPublicKey);
    }
    let vk = P256VerifyingKey::from_sec1_bytes(public_key).map_err(|_| CryptoError::InvalidPublicKey)?;
    let sig = P256Signature::from_slice(sig).map_err(|_| CryptoError::InvalidSignature)?;
    if sig.normalize_s() != sig {
        return Err(CryptoError::HighS);
    }
    vk.verify(msg, &sig).map_err(|_| CryptoError::InvalidSignature)
}

/// Verify `signature` over `msg` under `public_key`.
///
/// # Errors
/// [`CryptoError::InvalidLength`] for a wrong-sized key or signature, [`CryptoError::InvalidPublicKey`] for a key
/// that is not a point, [`CryptoError::HighS`] for a malleable ECDSA signature, [`CryptoError::InvalidSignature`]
/// otherwise.
pub fn verify(alg: IdentityAlg, public_key: &[u8], msg: &[u8], signature: &[u8]) -> Result<(), CryptoError> {
    if public_key.len() != alg.public_key_len() || signature.len() != alg.signature_len() {
        return Err(CryptoError::InvalidLength);
    }
    match alg {
        IdentityAlg::Ed25519 => ed_verify(public_key, msg, signature),
        IdentityAlg::EcdsaP256 => p256_verify(public_key, msg, signature),
        IdentityAlg::MlDsa65 => verify_ml_dsa_65(public_key, &[], msg, signature),
        IdentityAlg::Hybrid => {
            let ((ed_pk, ml_pk), (ed_sig, ml_sig)) = (public_key.split_at(ED_PK), signature.split_at(ED_SIG));
            let digest = hybrid_digest(msg);
            let ed = ed_verify(ed_pk, &digest, ed_sig);
            let ml = verify_ml_dsa_65(ml_pk, &[], &digest, ml_sig);
            ed.and(ml)
        }
    }
}

/// Verify `signature` over `msg` for the node `id`, whose public key is `public_key`.
///
/// # Errors
/// [`CryptoError::NodeIdMismatch`] if `public_key` is not the key of `id`; otherwise as [`verify`].
pub fn verify_node(id: &NodeId, public_key: &[u8], msg: &[u8], signature: &[u8]) -> Result<(), CryptoError> {
    if !id.matches(id.alg, public_key) {
        return Err(CryptoError::NodeIdMismatch);
    }
    verify(id.alg, public_key, msg, signature)
}

#[cfg_attr(
    not(feature = "alloc"),
    allow(
        clippy::large_enum_variant,
        reason = "without an allocator the expanded ML-DSA-65 key has nowhere to stay but inline"
    )
)]
enum Inner {
    Ed25519(EdSigningKey),
    P256(P256SigningKey),
    #[cfg(feature = "alloc")]
    MlDsa65(alloc::boxed::Box<MlSigningKey<MlDsa65>>),
    #[cfg(not(feature = "alloc"))]
    MlDsa65(MlSigningKey<MlDsa65>),
    #[cfg(feature = "alloc")]
    Hybrid(EdSigningKey, alloc::boxed::Box<MlSigningKey<MlDsa65>>),
    #[cfg(not(feature = "alloc"))]
    Hybrid(EdSigningKey, MlSigningKey<MlDsa65>),
}

/// The hybrid arm of [`Keypair::from_seed`] with an allocator: the ML-DSA-65 half goes through [`ml_boxed`], so its
/// 64 KiB never sit in this frame either.
#[cfg(feature = "alloc")]
#[inline(never)]
fn hybrid_inner(seed: &[u8]) -> Result<Inner, CryptoError> {
    let (ed, ml) = seed.split_at(32);
    Ok(Inner::Hybrid(ed_key(ed)?, ml_boxed(ml)?))
}

/// The hybrid arm of [`Keypair::from_seed`] without an allocator: the expanded key is built in place, out of line.
#[cfg(not(feature = "alloc"))]
#[inline(never)]
fn hybrid_inner(seed: &[u8]) -> Result<Inner, CryptoError> {
    let (ed, ml) = seed.split_at(32);
    Ok(Inner::Hybrid(ed_key(ed)?, ml_key(ml)?))
}

/// A software signing key pair, zeroized on drop.
///
/// With the `alloc` feature the expanded ML-DSA-65 key is boxed once, in [`Keypair::from_seed`], so a key pair of any
/// algorithm is `size_of::<Keypair>()` = 240 bytes: the largest small algorithm's expanded key, plus the algorithm
/// tag. Without an allocator the ML-DSA-65 expanded key lives inline and a key pair is 65,928 bytes for every
/// algorithm. Storage is not construction: `from_seed` for ML-DSA-65 and the hybrid still builds the 64 KiB
/// expanded key in the caller's frame before the box copies it out, so those two algorithms need several hundred
/// KiB of stack to construct a key pair; an Ed25519 or P-256 key pair constructs on 8 KiB.
pub struct Keypair(Inner);

impl core::fmt::Debug for Keypair {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Keypair(..)")
    }
}

fn ml_key(seed: &[u8]) -> Result<MlSigningKey<MlDsa65>, CryptoError> {
    let seed: &[u8; 32] = seed.try_into().map_err(|_| CryptoError::InvalidLength)?;
    Ok(MlSigningKey::from_seed(&Seed::from(*seed)))
}

/// The expanded ML-DSA-65 key built from `seed` and boxed, out of line: the key is 64 KiB by value, and an
/// unoptimised build reserves its stack in the frame of every function whose code could build one. Keeping the build
/// in this frame means a small algorithm's [`Keypair::from_seed`] never pays for it.
#[cfg(feature = "alloc")]
#[inline(never)]
fn ml_boxed(seed: &[u8]) -> Result<alloc::boxed::Box<MlSigningKey<MlDsa65>>, CryptoError> {
    Ok(alloc::boxed::Box::new(ml_key(seed)?))
}

/// The ML-DSA-65 arm of [`Keypair::from_seed`], out of line for the same reason.
#[cfg(feature = "alloc")]
#[inline(never)]
fn ml_inner(seed: &[u8]) -> Result<Inner, CryptoError> {
    Ok(Inner::MlDsa65(ml_boxed(seed)?))
}

/// The ML-DSA-65 arm of [`Keypair::from_seed`] without an allocator: the expanded key is built in place, out of line.
#[cfg(not(feature = "alloc"))]
#[inline(never)]
fn ml_inner(seed: &[u8]) -> Result<Inner, CryptoError> {
    Ok(Inner::MlDsa65(ml_key(seed)?))
}

fn ed_key(seed: &[u8]) -> Result<EdSigningKey, CryptoError> {
    let seed: &[u8; 32] = seed.try_into().map_err(|_| CryptoError::InvalidLength)?;
    Ok(EdSigningKey::from_bytes(seed))
}

/// The public key of an ML-DSA-65 key pair, out of line: the verification key carries the precomputed public matrix
/// (tens of KiB by value), and an unoptimised build reserves its stack in the frame of every function whose code
/// could build one. A small algorithm's [`Keypair::public_key`] never pays for it.
#[inline(never)]
fn ml_public_key(k: &MlSigningKey<MlDsa65>, out: &mut [u8]) -> Result<(), CryptoError> {
    put(out, 0, &k.verifying_key().to_bytes())
}

/// The public key of a hybrid key pair, out of line for the same reason.
#[inline(never)]
fn hybrid_public_key(ed: &EdSigningKey, ml: &MlSigningKey<MlDsa65>, out: &mut [u8]) -> Result<(), CryptoError> {
    put(out, 0, ed.verifying_key().as_bytes())?;
    put(out, ED_PK, &ml.verifying_key().to_bytes())
}

fn put(out: &mut [u8], at: usize, bytes: &[u8]) -> Result<(), CryptoError> {
    out.get_mut(at..at + bytes.len())
        .ok_or(CryptoError::InvalidLength)?
        .copy_from_slice(bytes);
    Ok(())
}

impl Keypair {
    /// Derive a key pair from `seed`, which is [`IdentityAlg::seed_len`] bytes (for a hybrid, the Ed25519 seed
    /// followed by the ML-DSA seed).
    ///
    /// Construction cost is not storage cost: for ML-DSA-65 and the hybrid this builds the 64 KiB expanded key in
    /// the caller's frame before the box copies it out (the crate holds no allocation-free expansion, since
    /// `forbid(unsafe_code)` bars writing into the box in place), so those two algorithms need several hundred KiB
    /// of stack here; Ed25519 and P-256 construct on 8 KiB. The returned key pair is small under `alloc` for
    /// every algorithm.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] for a wrong-sized seed, [`CryptoError::InvalidSecretKey`] for a P-256 seed
    /// that is zero or not below the group order.
    pub fn from_seed(alg: IdentityAlg, seed: &[u8]) -> Result<Self, CryptoError> {
        if seed.len() != alg.seed_len() {
            return Err(CryptoError::InvalidLength);
        }
        Ok(Self(match alg {
            IdentityAlg::Ed25519 => Inner::Ed25519(ed_key(seed)?),
            IdentityAlg::EcdsaP256 => {
                Inner::P256(P256SigningKey::from_slice(seed).map_err(|_| CryptoError::InvalidSecretKey)?)
            }
            IdentityAlg::MlDsa65 => ml_inner(seed)?,
            IdentityAlg::Hybrid => hybrid_inner(seed)?,
        }))
    }

    /// The algorithm of this key pair.
    pub const fn alg(&self) -> IdentityAlg {
        match self.0 {
            Inner::Ed25519(_) => IdentityAlg::Ed25519,
            Inner::P256(_) => IdentityAlg::EcdsaP256,
            Inner::MlDsa65(_) => IdentityAlg::MlDsa65,
            Inner::Hybrid(..) => IdentityAlg::Hybrid,
        }
    }

    /// Write the public key to the start of `out` and return its length.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `out` is shorter than [`IdentityAlg::public_key_len`].
    pub fn public_key(&self, out: &mut [u8]) -> Result<usize, CryptoError> {
        match &self.0 {
            Inner::Ed25519(k) => put(out, 0, k.verifying_key().as_bytes())?,
            Inner::P256(k) => put(out, 0, k.verifying_key().to_sec1_point(true).as_bytes())?,
            Inner::MlDsa65(k) => ml_public_key(k, out)?,
            Inner::Hybrid(ed, ml) => hybrid_public_key(ed, ml, out)?,
        }
        Ok(self.alg().public_key_len())
    }

    /// The node id of this key pair.
    pub fn node_id(&self) -> NodeId {
        let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
        let alg = self.alg();
        let n = alg.public_key_len();
        // `pk` is `MAX_PUBLIC_KEY_LEN` bytes, so neither step can fail; a failure would yield an id of zeros.
        let id = self
            .public_key(&mut pk)
            .and_then(|_| NodeId::from_public(alg, pk.get(..n).unwrap_or(&[])));
        id.unwrap_or(NodeId { alg, bytes: [0; 32] })
    }

    /// Sign `msg` deterministically (ML-DSA uses `rnd` = 32 zero bytes), writing the signature to the start of
    /// `out` and returning its length.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `out` is shorter than [`IdentityAlg::signature_len`].
    pub fn sign(&self, msg: &[u8], out: &mut [u8]) -> Result<usize, CryptoError> {
        self.sign_with_rnd(msg, &[0; 32], out)
    }

    /// Sign `msg`, giving the ML-DSA hedging bytes `rnd` (FIPS 204 `rnd`). Ed25519 and ECDSA are deterministic and
    /// ignore it.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `out` is shorter than [`IdentityAlg::signature_len`].
    pub fn sign_with_rnd(&self, msg: &[u8], rnd: &[u8; 32], out: &mut [u8]) -> Result<usize, CryptoError> {
        // Checked first so a short buffer is left untouched, never holding the first half of a hybrid signature.
        if out.len() < self.alg().signature_len() {
            return Err(CryptoError::InvalidLength);
        }
        match &self.0 {
            Inner::Ed25519(k) => put(out, 0, &k.sign(msg).to_bytes())?,
            Inner::P256(k) => {
                let sig: P256Signature = k.sign(msg);
                put(out, 0, sig.normalize_s().to_bytes().as_slice())?;
            }
            Inner::MlDsa65(k) => put(out, 0, &ml_sign(k, msg, rnd))?,
            Inner::Hybrid(ed, ml) => {
                let digest = hybrid_digest(msg);
                put(out, 0, &ed.sign(&digest).to_bytes())?;
                put(out, ED_SIG, &ml_sign(ml, &digest, rnd))?;
            }
        }
        Ok(self.alg().signature_len())
    }
}

#[cfg(test)]
mod tests {
    /// The size stated on [`super::Keypair`]'s docs, for both layouts: without an allocator it is master's layout,
    /// the expanded ML-DSA-65 key inline in every key pair.
    #[test]
    fn a_key_pair_is_the_size_its_docs_state() {
        let expected = if cfg!(feature = "alloc") { 240 } else { 65_928 };
        assert_eq!(core::mem::size_of::<super::Keypair>(), expected);
    }
}
