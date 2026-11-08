//! [`Software`]: the [`Provider`] built from vetted pure-Rust crates.
//!
//! Invariants: no allocation and no randomness; every key type zeroizes on drop; every length is checked before a
//! primitive sees the bytes, so no input panics; authentication tags are compared inside the AEAD crates in constant
//! time. AES-GCM and `ChaCha20` pick the hardware or SIMD path at run time inside their crates.

use aes::Aes128;
use aes::cipher::BlockCipherEncrypt;
use aes_gcm::{AeadInOut, Aes128Gcm, KeyInit};
use chacha20::ChaCha20;
use chacha20::cipher::{KeyIvInit, StreamCipher, StreamCipherSeek};
use chacha20poly1305::ChaCha20Poly1305;
use ml_kem::ml_kem_768::{Ciphertext, DecapsulationKey, EncapsulationKey};
use ml_kem::{B32, Decapsulate, KeyExport, Seed};
use sha2::{Digest, Sha256};
use subtle::ConstantTimeEq;
use zeroize::Zeroize;

use crate::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use crate::{Aead, Capabilities, CryptoError, Provider, Secret};

#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
cpufeatures::new!(aes_gcm_hw, "aes", "pclmulqdq");
#[cfg(target_arch = "aarch64")]
cpufeatures::new!(aes_gcm_hw, "aes", "pmull");

/// The software provider: a zero-sized handle.
#[derive(Debug, Clone, Copy, Default)]
pub struct Software;

/// A [`Software`] AEAD key for either algorithm.
#[allow(clippy::large_enum_variant, reason = "keys live on the stack; boxing would allocate")]
pub enum AeadKey {
    /// A ChaCha20-Poly1305 key.
    ChaCha20Poly1305(ChaCha20Poly1305),
    /// An AES-128-GCM key with its expanded round keys.
    Aes128Gcm(Aes128Gcm),
}

impl core::fmt::Debug for AeadKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("AeadKey(..)")
    }
}

/// A [`Software`] header-protection key for either algorithm.
#[allow(clippy::large_enum_variant, reason = "keys live on the stack; boxing would allocate")]
pub enum HpKey {
    /// The `ChaCha20` key.
    ChaCha20(Secret<32>),
    /// The expanded AES-128 key.
    Aes128(Aes128),
}

impl core::fmt::Debug for HpKey {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("HpKey(..)")
    }
}

/// An ML-KEM-768 encapsulation key.
pub type KemEncapsKey = EncapsulationKey;
/// An ML-KEM-768 decapsulation key.
pub type KemDecapsKey = DecapsulationKey;
/// An ML-KEM-768 ciphertext.
pub type KemCiphertext = Ciphertext;

impl Provider for Software {
    type AeadKey = AeadKey;
    type HpKey = HpKey;
    type X25519Secret = Secret<32>;
    type KemEncapsKey = KemEncapsKey;
    type KemDecapsKey = KemDecapsKey;
    type KemCiphertext = KemCiphertext;

    fn capabilities(&self) -> Capabilities {
        #[cfg(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64"))]
        let aes_gcm_hw = aes_gcm_hw::get();
        #[cfg(not(any(target_arch = "x86", target_arch = "x86_64", target_arch = "aarch64")))]
        let aes_gcm_hw = false;
        Capabilities {
            aes_gcm_hw,
            chacha20_simd: cfg!(any(
                target_feature = "sse2",
                target_feature = "neon",
                target_feature = "simd128"
            )),
        }
    }

    fn aead_key(&self, alg: Aead, key: &[u8]) -> Result<AeadKey, CryptoError> {
        match alg {
            Aead::ChaCha20Poly1305 => ChaCha20Poly1305::new_from_slice(key).map(AeadKey::ChaCha20Poly1305),
            Aead::Aes128Gcm => Aes128Gcm::new_from_slice(key).map(AeadKey::Aes128Gcm),
        }
        .map_err(|_| CryptoError::InvalidLength)
    }

    fn seal(
        &self,
        key: &AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
    ) -> Result<[u8; Aead::TAG_LEN], CryptoError> {
        match key {
            AeadKey::ChaCha20Poly1305(k) => k
                .encrypt_inout_detached(&(*nonce).into(), aad, buf.into())
                .map(Into::into),
            AeadKey::Aes128Gcm(k) => k
                .encrypt_inout_detached(&(*nonce).into(), aad, buf.into())
                .map(Into::into),
        }
        .map_err(|_| CryptoError::InputTooLong)
    }

    fn open(
        &self,
        key: &AeadKey,
        nonce: &[u8; Aead::NONCE_LEN],
        aad: &[u8],
        buf: &mut [u8],
        tag: &[u8; Aead::TAG_LEN],
    ) -> Result<(), CryptoError> {
        match key {
            AeadKey::ChaCha20Poly1305(k) => k.decrypt_inout_detached(&(*nonce).into(), aad, buf.into(), &(*tag).into()),
            AeadKey::Aes128Gcm(k) => k.decrypt_inout_detached(&(*nonce).into(), aad, buf.into(), &(*tag).into()),
        }
        .map_err(|_| CryptoError::Authentication)
    }

    fn hp_key(&self, alg: Aead, key: &[u8]) -> Result<HpKey, CryptoError> {
        match alg {
            Aead::ChaCha20Poly1305 => <[u8; 32]>::try_from(key).map(|k| HpKey::ChaCha20(Secret::new(k))).ok(),
            Aead::Aes128Gcm => Aes128::new_from_slice(key).map(HpKey::Aes128).ok(),
        }
        .ok_or(CryptoError::InvalidLength)
    }

    fn hp_mask(&self, key: &HpKey, sample: &[u8; Aead::SAMPLE_LEN]) -> [u8; Aead::MASK_LEN] {
        let mut mask = [0u8; Aead::MASK_LEN];
        match key {
            HpKey::Aes128(cipher) => {
                let mut block = (*sample).into();
                cipher.encrypt_block(&mut block);
                let block: [u8; 16] = block.into();
                mask.copy_from_slice(block.first_chunk().unwrap_or(&[0; Aead::MASK_LEN]));
            }
            HpKey::ChaCha20(k) => {
                let [c0, c1, c2, c3, nonce @ ..] = *sample;
                let counter = u32::from_le_bytes([c0, c1, c2, c3]);
                let mut cipher = ChaCha20::new(k.expose().into(), &nonce.into());
                // The counter is a block number and the stream holds 2^32 blocks, so neither call can fail.
                if cipher.try_seek(u64::from(counter) * 64).is_err() || cipher.try_write_keystream(&mut mask).is_err() {
                    mask = [0; Aead::MASK_LEN];
                }
            }
        }
        mask
    }

    fn sha256(&self, data: &[u8]) -> [u8; 32] {
        Sha256::digest(data).into()
    }

    fn x25519_secret(&self, seed: &[u8; 32]) -> Secret<32> {
        Secret::new(*seed)
    }

    fn x25519_public(&self, secret: &Secret<32>) -> [u8; 32] {
        x25519_dalek::x25519(*secret.expose(), x25519_dalek::X25519_BASEPOINT_BYTES)
    }

    fn x25519_dh(&self, secret: &Secret<32>, peer: &[u8; 32]) -> Result<Secret<32>, CryptoError> {
        let shared = Secret::new(x25519_dalek::x25519(*secret.expose(), *peer));
        if bool::from(shared.expose().ct_eq(&[0u8; 32])) {
            return Err(CryptoError::NonContributory);
        }
        Ok(shared)
    }

    fn kem_keygen(&self, d: &[u8; 32], z: &[u8; 32]) -> (KemDecapsKey, KemEncapsKey) {
        let mut seed = [0u8; 64];
        let (sd, sz) = seed.split_at_mut(32);
        sd.copy_from_slice(d);
        sz.copy_from_slice(z);
        let dk = DecapsulationKey::from_seed(Seed::from(seed));
        seed.zeroize();
        let ek = dk.encapsulation_key().clone();
        (dk, ek)
    }

    fn kem_encaps_key(&self, bytes: &[u8]) -> Result<KemEncapsKey, CryptoError> {
        let bytes: &[u8; KEM_ENCAPS_KEY_LEN] = bytes.try_into().map_err(|_| CryptoError::InvalidEncapsulationKey)?;
        EncapsulationKey::new(&(*bytes).into()).map_err(|_| CryptoError::InvalidEncapsulationKey)
    }

    fn kem_encaps_key_bytes(&self, ek: &KemEncapsKey) -> [u8; KEM_ENCAPS_KEY_LEN] {
        ek.to_bytes().into()
    }

    fn kem_ciphertext(&self, bytes: &[u8]) -> Result<KemCiphertext, CryptoError> {
        let bytes: &[u8; KEM_CIPHERTEXT_LEN] = bytes.try_into().map_err(|_| CryptoError::InvalidLength)?;
        Ok((*bytes).into())
    }

    fn kem_ciphertext_bytes(&self, ct: &KemCiphertext) -> [u8; KEM_CIPHERTEXT_LEN] {
        (*ct).into()
    }

    fn kem_encapsulate(&self, ek: &KemEncapsKey, m: &[u8; 32]) -> Result<(KemCiphertext, Secret<32>), CryptoError> {
        let (ct, shared) = ek.encapsulate_deterministic(&B32::from(*m));
        Ok((ct, Secret::new(shared.into())))
    }

    fn kem_decapsulate(&self, dk: &KemDecapsKey, ct: &KemCiphertext) -> Result<Secret<32>, CryptoError> {
        Ok(Secret::new(dk.decapsulate(ct).into()))
    }
}
