//! The sealed-data envelope shared by every store: ChaCha20-Poly1305 under a 32-byte key.
//!
//! Layout: `header || nonce (12) || ciphertext || tag (16)`. The whole header is authenticated as associated data, so
//! a store that keeps extra material in the header (the TPM store keeps the wrapped key there) binds it to the
//! ciphertext. The nonce is random per seal, which is safe for far fewer than 2^32 seals under one key.

use vinc_crypto::{Aead, Provider, Secret, Software};
use zeroize::Zeroizing;

use crate::{KeyStoreError, Result};

/// The envelope key length.
pub(crate) const KEY_LEN: usize = 32;
const NONCE_LEN: usize = Aead::NONCE_LEN;
const TAG_LEN: usize = Aead::TAG_LEN;

/// Encrypt `plaintext` under `key`, returning `header || nonce || ciphertext || tag`.
pub(crate) fn encrypt(
    key: &Secret<KEY_LEN>,
    header: &[u8],
    nonce: [u8; NONCE_LEN],
    plaintext: &[u8],
) -> Result<Vec<u8>> {
    let aead = Software.aead_key(Aead::ChaCha20Poly1305, key.expose())?;
    let mut body = Zeroizing::new(plaintext.to_vec());
    let tag = Software.seal(&aead, &nonce, header, &mut body)?;
    let mut out = Vec::with_capacity(header.len() + NONCE_LEN + body.len() + TAG_LEN);
    out.extend_from_slice(header);
    out.extend_from_slice(&nonce);
    out.extend_from_slice(&body);
    out.extend_from_slice(&tag);
    Ok(out)
}

/// Decrypt an envelope whose first `header_len` bytes are the header.
pub(crate) fn decrypt(key: &Secret<KEY_LEN>, sealed: &[u8], header_len: usize) -> Result<Zeroizing<Vec<u8>>> {
    let (header, rest) = sealed
        .split_at_checked(header_len)
        .ok_or(KeyStoreError::InvalidSealed)?;
    let (nonce, rest) = rest
        .split_first_chunk::<NONCE_LEN>()
        .ok_or(KeyStoreError::InvalidSealed)?;
    let (body, tag) = rest.split_last_chunk::<TAG_LEN>().ok_or(KeyStoreError::InvalidSealed)?;
    let aead = Software.aead_key(Aead::ChaCha20Poly1305, key.expose())?;
    let mut plain = Zeroizing::new(body.to_vec());
    Software
        .open(&aead, nonce, header, &mut plain, tag)
        .map_err(|_| KeyStoreError::InvalidSealed)?;
    Ok(plain)
}
