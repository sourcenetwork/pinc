//! The [`Provider`] trait: the fast primitives behind one static interface.
//!
//! Invariants: dispatch is static (associated types and generic methods, never `dyn`); no method allocates or
//! reads randomness, so every output is a function of the inputs; secrets live in zeroizing types; the AEAD is
//! chosen by [`Aead`] with a `match`. The trait carries only the synchronous primitives that run per packet or per
//! handshake: the AEADs, header protection, SHA-256, X25519 and ML-KEM-768. Long-term identity keys are handled by
//! [`crate::identity`].

use crate::{CryptoError, Secret};

/// The length of an ML-KEM-768 encapsulation key.
pub const KEM_ENCAPS_KEY_LEN: usize = 1184;
/// The length of an ML-KEM-768 ciphertext.
pub const KEM_CIPHERTEXT_LEN: usize = 1088;

/// An AEAD algorithm. Both take a 12-byte nonce and produce a detached 16-byte tag.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Aead {
    /// ChaCha20-Poly1305 (RFC 8439), a 32-byte key.
    ChaCha20Poly1305,
    /// AES-128-GCM, a 16-byte key.
    Aes128Gcm,
}

impl Aead {
    /// The length of a nonce.
    pub const NONCE_LEN: usize = 12;
    /// The length of the detached authentication tag.
    pub const TAG_LEN: usize = 16;
    /// The length of a header-protection mask.
    pub const MASK_LEN: usize = 5;
    /// The length of a header-protection sample.
    pub const SAMPLE_LEN: usize = 16;

    /// The length of this algorithm's key (and of its header-protection key).
    pub const fn key_len(self) -> usize {
        match self {
            Self::ChaCha20Poly1305 => 32,
            Self::Aes128Gcm => 16,
        }
    }
}

/// What the CPU accelerates, so a node can decide which AEAD to offer.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Capabilities {
    /// AES-GCM runs on hardware AES and carry-less multiplication (AES-NI and PCLMULQDQ on x86, AES and PMULL on
    /// aarch64). When false, AES-GCM is the slower table-free software path.
    pub aes_gcm_hw: bool,
    /// `ChaCha20` runs on SIMD (SSE2 or AVX2 on x86, NEON on aarch64, simd128 on wasm).
    pub chacha20_simd: bool,
}

/// The synchronous primitives of the protocol, behind a static interface.
///
/// [`crate::Software`] implements it with vetted software crates; a hardware backend implements the same trait.
pub trait Provider {
    /// An expanded AEAD key, zeroized on drop.
    type AeadKey;
    /// An expanded header-protection key, zeroized on drop.
    type HpKey;
    /// An X25519 secret, zeroized on drop.
    type X25519Secret;
    /// An ML-KEM-768 encapsulation (public) key that passed the FIPS 203 checks.
    type KemEncapsKey;
    /// An ML-KEM-768 decapsulation (secret) key, zeroized on drop.
    type KemDecapsKey;
    /// An ML-KEM-768 ciphertext.
    type KemCiphertext;

    /// What this provider accelerates on the running CPU.
    fn capabilities(&self) -> Capabilities;

    /// Set up an AEAD key.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `key` is not [`Aead::key_len`] bytes.
    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<Self::AeadKey, CryptoError>;

    /// Encrypt `buf` in place and return the detached tag.
    ///
    /// # Errors
    /// [`CryptoError::InputTooLong`] if `buf` or `aad` is beyond the algorithm's limit.
    fn seal(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError>;

    /// Verify `tag` and decrypt `buf` in place. On failure `buf` is left as the (unauthenticated) ciphertext.
    ///
    /// # Errors
    /// [`CryptoError::Authentication`] if the tag, the ciphertext, the AAD, the nonce or the key is wrong.
    fn open(
        &self,
        key: &Self::AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError>;

    /// Set up a header-protection key: `ChaCha20` for [`Aead::ChaCha20Poly1305`] (RFC 9001 5.4.4), AES-128 for
    /// [`Aead::Aes128Gcm`] (RFC 9001 5.4.3).
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `key` is not [`Aead::key_len`] bytes.
    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<Self::HpKey, CryptoError>;

    /// The 5-byte header-protection mask for a 16-byte ciphertext sample.
    fn hp_mask(&self, key: &Self::HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN];

    /// The SHA-256 digest of `data`.
    fn sha256(&self, data: &[u8]) -> [u8; 32];

    /// An X25519 secret from 32 seed bytes (clamped when used).
    fn x25519_secret(&self, seed: &[u8; 32]) -> Self::X25519Secret;

    /// The X25519 public key of `secret`.
    fn x25519_public(&self, secret: &Self::X25519Secret) -> [u8; 32];

    /// The X25519 shared secret of `secret` and the peer's public key.
    ///
    /// # Errors
    /// [`CryptoError::NonContributory`] if the result is all zero (the peer sent a low-order point).
    fn x25519_dh(&self, secret: &Self::X25519Secret, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError>;

    /// Deterministic ML-KEM-768 key generation from the FIPS 203 seeds `d` and `z`. A stored decapsulation key is
    /// the pair `(d, z)`: regenerate it with this call.
    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (Self::KemDecapsKey, Self::KemEncapsKey);

    /// Parse and validate a received encapsulation key (FIPS 203 section 7.2: length and modulus check).
    ///
    /// # Errors
    /// [`CryptoError::InvalidEncapsulationKey`] if `bytes` is not a valid encapsulation key.
    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<Self::KemEncapsKey, CryptoError>;

    /// The wire bytes of an encapsulation key.
    fn kem_encaps_key_bytes(&self, ek: &Self::KemEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN];

    /// Parse a received ciphertext (length only: ML-KEM accepts every ciphertext of the right length).
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if `bytes` has the wrong length.
    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<Self::KemCiphertext, CryptoError>;

    /// The wire bytes of a ciphertext.
    fn kem_ciphertext_bytes(&self, ct: &Self::KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN];

    /// Deterministic ML-KEM-768 encapsulation with the 32-byte message `m`; returns the ciphertext and the shared
    /// secret.
    ///
    /// # Errors
    /// A backend that can fail (a hardware one) reports it; the software backend does not fail.
    fn kem_encapsulate(
        &self,
        ek: &Self::KemEncapsKey,
        m: &[u8; 32],
    ) -> Result<(Self::KemCiphertext, Secret<32>), CryptoError>;

    /// ML-KEM-768 decapsulation. A forged ciphertext gives a pseudo-random secret (implicit rejection), never an
    /// error.
    ///
    /// # Errors
    /// A backend that can fail (a hardware one) reports it; the software backend does not fail.
    fn kem_decapsulate(&self, dk: &Self::KemDecapsKey, ct: &Self::KemCiphertext) -> Result<Secret<32>, CryptoError>;
}
