//! Record protection: packet keys with nonce construction, key-roll generations and header protection.
//!
//! Invariants: the nonce of a packet is the IV XOR the packet number, and a packet number is below 2^62, so a
//! (key, nonce) pair is never reused within a generation; a key that reached its usage limit refuses to seal or open
//! and says so with [`RecordError::KeyRollRequired`], it never continues silently; a key of the next generation
//! derives only from a secret the two sides computed together with a fresh Diffie-Hellman value (see
//! [`crate::keyroll`]), never from the old secret alone, so there is no hash-only successor; the header key belongs
//! to the first generation and is not rolled. Seal and open work in place over caller buffers with a detached tag.
//! Nothing here allocates, reads a clock or a random source, or panics.

use core::fmt;

use pinc_crypto::{Aead, CryptoError, Provider, Secret, expand};
use zeroize::Zeroize;

use crate::labels;
use crate::schedule::roll_secret;

/// The largest packet number: packet numbers are below 2^62.
pub const MAX_PACKET_NUMBER: u64 = (1 << 62) - 1;
/// An AES-128-GCM key seals fewer than this many packets: 2^22, half of the RFC 9001 confidentiality limit.
pub const AES_GCM_PACKET_LIMIT: u64 = 1 << 22;
/// A ChaCha20-Poly1305 key refuses to open once this many packets failed to open under it: 2^36, its integrity limit.
pub const CHACHA_FAILURE_LIMIT: u64 = 1 << 36;

/// The usage limits of one key generation. [`Limits::default`] is the protocol's; others exist for tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// How many packets an AES-128-GCM key seals.
    pub aes_gcm_packets: u64,
    /// How many failed opens a ChaCha20-Poly1305 key tolerates.
    pub chacha_failures: u64,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            aes_gcm_packets: AES_GCM_PACKET_LIMIT,
            chacha_failures: CHACHA_FAILURE_LIMIT,
        }
    }
}

/// Why a record operation was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecordError {
    /// The packet number is 2^62 or more.
    PacketNumber,
    /// The packet number is not above the last one this key sealed: a number is never sealed twice under one key.
    NotIncreasing,
    /// The tag does not match: the packet, its header, its number or the key is wrong.
    Authentication,
    /// The key reached its usage limit: roll to the next generation with [`PacketKey::rolled`].
    KeyRollRequired,
    /// The packet-number field is not 1 to 4 bytes.
    HeaderLength,
    /// There is no next generation: the generation counter is exhausted.
    GenerationExhausted,
    /// A primitive refused its input.
    Crypto(CryptoError),
}

impl From<CryptoError> for RecordError {
    fn from(e: CryptoError) -> Self {
        Self::Crypto(e)
    }
}

impl fmt::Display for RecordError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PacketNumber => f.write_str("packet number is 2^62 or more"),
            Self::NotIncreasing => f.write_str("packet number does not increase"),
            Self::Authentication => f.write_str("packet failed authentication"),
            Self::KeyRollRequired => f.write_str("the key reached its usage limit; roll keys"),
            Self::HeaderLength => f.write_str("packet number field is not 1 to 4 bytes"),
            Self::GenerationExhausted => f.write_str("no further key generation"),
            Self::Crypto(e) => write!(f, "{e}"),
        }
    }
}

impl core::error::Error for RecordError {}

/// The AEAD key and IV of a traffic secret.
fn derive_material<P: Provider>(
    p: &P,
    aead: Aead,
    secret: &Secret<32>,
) -> Result<(P::AeadKey, Secret<12>), CryptoError> {
    let mut key = [0u8; 32];
    let slot = key.get_mut(..aead.key_len()).ok_or(CryptoError::InvalidLength)?;
    expand(secret.expose(), labels::PACKET_KEY, &[], slot);
    let aead_key = p.aead_key(aead, slot);
    key.zeroize();
    let mut iv = [0u8; Aead::NONCE_LEN];
    expand(secret.expose(), labels::PACKET_IV, &[], &mut iv);
    let iv_secret = Secret::new(iv);
    iv.zeroize();
    Ok((aead_key?, iv_secret))
}

/// The AEAD key of one direction and one key generation, with the usage counters that bound it.
pub struct PacketKey<P: Provider> {
    aead: Aead,
    key: P::AeadKey,
    iv: Secret<12>,
    secret: Secret<32>,
    generation: u32,
    sealed: u64,
    last_sealed: Option<u64>,
    failed: u64,
    limits: Limits,
}

impl<P: Provider> fmt::Debug for PacketKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PacketKey")
            .field("aead", &self.aead)
            .field("generation", &self.generation)
            .finish_non_exhaustive()
    }
}

impl<P: Provider> PacketKey<P> {
    /// The generation-0 key of a traffic `secret`.
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if the provider refuses the derived key.
    pub fn from_secret(p: &P, aead: Aead, secret: &Secret<32>) -> Result<Self, CryptoError> {
        Self::at_generation(p, aead, secret.clone(), 0, Limits::default())
    }

    fn at_generation(
        p: &P,
        aead: Aead,
        secret: Secret<32>,
        generation: u32,
        limits: Limits,
    ) -> Result<Self, CryptoError> {
        let (key, iv) = derive_material(p, aead, &secret)?;
        Ok(Self {
            aead,
            key,
            iv,
            secret,
            generation,
            sealed: 0,
            last_sealed: None,
            failed: 0,
            limits,
        })
    }

    /// This key with other usage limits (used by tests to reach a limit quickly).
    #[must_use]
    pub const fn with_limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// The AEAD of this key.
    pub const fn aead(&self) -> Aead {
        self.aead
    }

    /// The key generation: 0 for the first, one more for each roll.
    pub const fn generation(&self) -> u32 {
        self.generation
    }

    /// A short fingerprint of the secret, for trace validation: equal fingerprints mean equal secrets.
    #[cfg(feature = "trace")]
    pub fn fingerprint(&self) -> u64 {
        let h = pinc_crypto::extract(&[0u8; 32], self.secret.expose());
        let mut b = [0u8; 8];
        b.iter_mut().zip(h).for_each(|(o, x)| *o = x);
        u64::from_le_bytes(b)
    }

    /// How many packets this key sealed.
    pub const fn sealed(&self) -> u64 {
        self.sealed
    }

    /// How many packets failed to open under this key.
    pub const fn failed_opens(&self) -> u64 {
        self.failed
    }

    fn nonce(&self, pn: u64) -> Result<[u8; Aead::NONCE_LEN], RecordError> {
        if pn > MAX_PACKET_NUMBER {
            return Err(RecordError::PacketNumber);
        }
        let mut nonce = *self.iv.expose();
        // The packet number, big-endian, in the last 8 bytes of the 12-byte nonce.
        for (n, b) in nonce.iter_mut().skip(Aead::NONCE_LEN - 8).zip(pn.to_be_bytes()) {
            *n ^= b;
        }
        Ok(nonce)
    }

    /// Encrypt `buf` in place under packet number `pn` and return the detached tag.
    ///
    /// # Errors
    /// [`RecordError::PacketNumber`] for `pn` of 2^62 or more; [`RecordError::NotIncreasing`] unless `pn` is above
    /// every number this key sealed before (a retransmission resends the stored bytes, it never seals again);
    /// [`RecordError::KeyRollRequired`] once an
    /// AES-128-GCM key has sealed [`Limits::aes_gcm_packets`] packets; [`RecordError::Crypto`] if the AEAD refuses
    /// the input length.
    pub fn seal(&mut self, p: &P, pn: u64, aad: &[u8], buf: &mut [u8]) -> Result<[u8; Aead::TAG_LEN], RecordError> {
        let nonce = self.nonce(pn)?;
        if self.last_sealed.is_some_and(|l| pn <= l) {
            return Err(RecordError::NotIncreasing);
        }
        if self.aead == Aead::Aes128Gcm && self.sealed >= self.limits.aes_gcm_packets {
            return Err(RecordError::KeyRollRequired);
        }
        let tag = p.seal(&self.key, &nonce, aad, buf)?;
        self.sealed = self.sealed.saturating_add(1);
        self.last_sealed = Some(pn);
        Ok(tag)
    }

    /// Verify `tag` and decrypt `buf` in place under packet number `pn`. On failure `buf` is the ciphertext.
    ///
    /// # Errors
    /// [`RecordError::PacketNumber`] for `pn` of 2^62 or more; [`RecordError::KeyRollRequired`] once a
    /// ChaCha20-Poly1305 key has seen [`Limits::chacha_failures`] failed opens; [`RecordError::Authentication`] if
    /// the packet does not verify (it counts toward that limit).
    pub fn open(
        &mut self,
        p: &P,
        pn: u64,
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), RecordError> {
        let nonce = self.nonce(pn)?;
        if self.aead == Aead::ChaCha20Poly1305 && self.failed >= self.limits.chacha_failures {
            return Err(RecordError::KeyRollRequired);
        }
        p.open(&self.key, &nonce, aad, buf, tag).map_err(|e| {
            if e == CryptoError::Authentication {
                self.failed = self.failed.saturating_add(1);
                RecordError::Authentication
            } else {
                RecordError::Crypto(e)
            }
        })
    }

    /// Whether this key reached the usage limit that calls for a roll: an AES-128-GCM key that sealed
    /// [`Limits::aes_gcm_packets`] packets, or a ChaCha20-Poly1305 key that saw [`Limits::chacha_failures`] failed
    /// opens.
    pub const fn limit_reached(&self) -> bool {
        match self.aead {
            Aead::Aes128Gcm => self.sealed >= self.limits.aes_gcm_packets,
            Aead::ChaCha20Poly1305 => self.failed >= self.limits.chacha_failures,
        }
    }

    /// The next key generation: its secret is `roll_secret(secret, dh)` for the fresh Diffie-Hellman value `dh` the
    /// two sides computed together (see [`crate::keyroll`]). The usage limits carry over; the counters start again.
    ///
    /// # Errors
    /// [`RecordError::GenerationExhausted`] after 2^32 - 1 rolls; [`RecordError::Crypto`] if the provider refuses
    /// the key.
    pub fn rolled(&self, p: &P, dh: &Secret<32>) -> Result<Self, RecordError> {
        let generation = self.generation.checked_add(1).ok_or(RecordError::GenerationExhausted)?;
        let secret = roll_secret(&self.secret, dh);
        Ok(Self::at_generation(p, self.aead, secret, generation, self.limits)?)
    }
}

/// The header-protection key of one direction (RFC 9001 section 5.4).
pub struct HeaderKey<P: Provider> {
    key: P::HpKey,
}

impl<P: Provider> fmt::Debug for HeaderKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("HeaderKey(..)")
    }
}

/// The bits of the first byte a header mask covers: 4 for a long header, 5 for a short one.
const fn first_byte_mask(long_header: bool) -> u8 {
    if long_header { 0x0f } else { 0x1f }
}

impl<P: Provider> HeaderKey<P> {
    /// The header key of a traffic `secret` (the generation-0 secret: it is never updated).
    ///
    /// # Errors
    /// [`CryptoError::InvalidLength`] if the provider refuses the derived key.
    pub fn from_secret(p: &P, aead: Aead, secret: &Secret<32>) -> Result<Self, CryptoError> {
        let mut key = [0u8; 32];
        let slot = key.get_mut(..aead.key_len()).ok_or(CryptoError::InvalidLength)?;
        expand(secret.expose(), labels::HEADER_KEY, &[], slot);
        let hp = p.hp_key(aead, slot);
        key.zeroize();
        Ok(Self { key: hp? })
    }

    /// Mask a header: the low bits of `first` and the packet-number bytes `pn` (1 to 4 bytes, the length the caller
    /// chose and wrote into `first`), using the 16-byte ciphertext `sample`. `long_header` selects the 4-bit or the
    /// 5-bit first-byte mask.
    ///
    /// # Errors
    /// [`RecordError::HeaderLength`] if `pn` is not 1 to 4 bytes.
    pub fn protect(
        &self,
        p: &P,
        first: &mut u8,
        pn: &mut [u8],
        sample: &[u8; Aead::SAMPLE_LEN],
        long_header: bool,
    ) -> Result<(), RecordError> {
        if !(1..=4).contains(&pn.len()) {
            return Err(RecordError::HeaderLength);
        }
        let mask = p.hp_mask(&self.key, sample);
        apply(mask, first, pn, long_header);
        Ok(())
    }

    /// Remove the mask from a header and return the packet-number length it reveals. `pn` starts at the packet
    /// number and must hold at least that many bytes.
    ///
    /// # Errors
    /// [`RecordError::HeaderLength`] if `pn` is shorter than the revealed length.
    pub fn unprotect(
        &self,
        p: &P,
        first: &mut u8,
        pn: &mut [u8],
        sample: &[u8; Aead::SAMPLE_LEN],
        long_header: bool,
    ) -> Result<usize, RecordError> {
        let mask = p.hp_mask(&self.key, sample);
        let mut unmasked = *first;
        apply(mask, &mut unmasked, &mut [], long_header);
        let len = usize::from(unmasked & 0x03) + 1;
        let field = pn.get_mut(..len).ok_or(RecordError::HeaderLength)?;
        apply(mask, first, field, long_header);
        Ok(len)
    }
}

/// XOR the mask into the first byte and the packet-number bytes.
fn apply(mask: [u8; Aead::MASK_LEN], first: &mut u8, pn: &mut [u8], long_header: bool) {
    let [m0, rest @ ..] = mask;
    *first ^= m0 & first_byte_mask(long_header);
    for (b, m) in pn.iter_mut().zip(rest) {
        *b ^= m;
    }
}
