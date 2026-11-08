//! Address-validation tokens: an AEAD-sealed claim "this address was seen at this time, for this purpose".
//!
//! A token is `nonce(12) || ciphertext || tag(16)`, where the plaintext is `address || issued_at(8, big-endian
//! nanoseconds) || kind(1)`, sealed under a key only the issuer holds with [`labels::TOKEN`] as associated data.
//! Invariants: [`TokenKey::validate`] accepts exactly the tokens this key issued for that address and kind whose age
//! is within the lifetime of the kind; any other input gets an error and nothing else. The nonce comes from the
//! caller's random generator; with one key, random 96-bit nonces stay safe for about 2^32 tokens, so rotate the key
//! well before that. The crate holds no clock: `now` and `issued_at` are the caller's nanoseconds.

use core::fmt;

use vinc_crypto::{Aead, CryptoError, Provider, Secret, ct_eq};

use crate::labels;

/// The longest address (the bytes of an IP address and port, or a relay path) a token can cover.
pub const MAX_ADDR_LEN: usize = 64;
/// The length of the token nonce.
pub const NONCE_LEN: usize = Aead::NONCE_LEN;
/// The length of the issue time and kind that follow the address in the plaintext.
const SUFFIX_LEN: usize = 9;
/// The longest token.
pub const MAX_TOKEN_LEN: usize = NONCE_LEN + MAX_ADDR_LEN + SUFFIX_LEN + Aead::TAG_LEN;
/// How long a [`TokenKind::Retry`] token stays valid: 10 seconds.
pub const RETRY_LIFETIME_NS: u64 = 10_000_000_000;
/// How long a [`TokenKind::NewToken`] token stays valid: 24 hours.
pub const NEW_TOKEN_LIFETIME_NS: u64 = 86_400_000_000_000;

/// What a token was issued for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenKind {
    /// Sent in a Retry: proves the client can receive at its address right now; short lifetime.
    Retry = 1,
    /// Sent for a later connection: proves the address was validated before; longer lifetime.
    NewToken = 2,
}

impl TokenKind {
    /// The lifetime of tokens of this kind, in nanoseconds.
    pub const fn lifetime_ns(self) -> u64 {
        match self {
            Self::Retry => RETRY_LIFETIME_NS,
            Self::NewToken => NEW_TOKEN_LIFETIME_NS,
        }
    }
}

/// Why a token was not issued or not accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenError {
    /// The address is longer than [`MAX_ADDR_LEN`].
    AddressTooLong,
    /// The output buffer is too small.
    BufferTooSmall,
    /// The token has an impossible length.
    Malformed,
    /// The token was not issued by this key, or was altered.
    Authentication,
    /// The token was issued for another address.
    WrongAddress,
    /// The token was issued for another purpose.
    WrongKind,
    /// The token is older than the lifetime of its kind.
    Expired,
    /// The token claims an issue time in the future.
    NotYetValid,
    /// A primitive refused its input.
    Crypto(CryptoError),
}

impl fmt::Display for TokenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AddressTooLong => f.write_str("address too long for a token"),
            Self::BufferTooSmall => f.write_str("output buffer too small"),
            Self::Malformed => f.write_str("token has an invalid length"),
            Self::Authentication => f.write_str("token was not issued by this key"),
            Self::WrongAddress => f.write_str("token was issued for another address"),
            Self::WrongKind => f.write_str("token was issued for another purpose"),
            Self::Expired => f.write_str("token expired"),
            Self::NotYetValid => f.write_str("token claims a future issue time"),
            Self::Crypto(e) => write!(f, "{e}"),
        }
    }
}

impl core::error::Error for TokenError {}

/// The key tokens are sealed under (ChaCha20-Poly1305).
pub struct TokenKey<P: Provider>(P::AeadKey);

impl<P: Provider> fmt::Debug for TokenKey<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("TokenKey(..)")
    }
}

impl<P: Provider> TokenKey<P> {
    /// A token key from 32 secret bytes.
    ///
    /// # Errors
    /// Never fails for a software provider; a hardware one may refuse the key.
    pub fn new(p: &P, key: &Secret<32>) -> Result<Self, CryptoError> {
        p.aead_key(Aead::ChaCha20Poly1305, key.expose()).map(Self)
    }

    /// Issue a token for `addr` into the start of `out` and return its length. `nonce` must be fresh random bytes.
    ///
    /// # Errors
    /// [`TokenError::AddressTooLong`] if `addr` is over [`MAX_ADDR_LEN`] bytes; [`TokenError::BufferTooSmall`] if
    /// `out` cannot hold the token.
    pub fn issue(
        &self,
        p: &P,
        addr: &[u8],
        kind: TokenKind,
        issued_at: u64,
        nonce: &[u8; NONCE_LEN],
        out: &mut [u8],
    ) -> Result<usize, TokenError> {
        if addr.len() > MAX_ADDR_LEN {
            return Err(TokenError::AddressTooLong);
        }
        let plain_len = addr.len() + SUFFIX_LEN;
        let total = NONCE_LEN + plain_len + Aead::TAG_LEN;
        let token = out.get_mut(..total).ok_or(TokenError::BufferTooSmall)?;
        let (nonce_out, rest) = token
            .split_at_mut_checked(NONCE_LEN)
            .ok_or(TokenError::BufferTooSmall)?;
        let (body, tag_out) = rest.split_at_mut_checked(plain_len).ok_or(TokenError::BufferTooSmall)?;
        nonce_out.copy_from_slice(nonce);
        let (addr_out, suffix) = body
            .split_at_mut_checked(addr.len())
            .ok_or(TokenError::BufferTooSmall)?;
        addr_out.copy_from_slice(addr);
        let (time_out, kind_out) = suffix.split_at_mut_checked(8).ok_or(TokenError::BufferTooSmall)?;
        time_out.copy_from_slice(&issued_at.to_be_bytes());
        kind_out.fill(kind as u8);
        let tag = p
            .seal(&self.0, nonce, labels::TOKEN.as_bytes(), body)
            .map_err(TokenError::Crypto)?;
        tag_out.copy_from_slice(&tag);
        Ok(total)
    }

    /// Accept `token` only if this key issued it for `addr` and `kind`, no later than the lifetime of `kind` ago.
    ///
    /// # Errors
    /// [`TokenError::Malformed`], [`TokenError::Authentication`], [`TokenError::WrongKind`],
    /// [`TokenError::WrongAddress`], [`TokenError::NotYetValid`] or [`TokenError::Expired`], in that order of checks.
    pub fn validate(&self, p: &P, token: &[u8], addr: &[u8], kind: TokenKind, now: u64) -> Result<(), TokenError> {
        let min = NONCE_LEN + SUFFIX_LEN + Aead::TAG_LEN;
        if token.len() < min || token.len() > MAX_TOKEN_LEN {
            return Err(TokenError::Malformed);
        }
        let (nonce, rest) = token.split_at_checked(NONCE_LEN).ok_or(TokenError::Malformed)?;
        let (sealed, tag) = rest
            .split_at_checked(rest.len() - Aead::TAG_LEN)
            .ok_or(TokenError::Malformed)?;
        let nonce: &[u8; NONCE_LEN] = nonce.try_into().map_err(|_| TokenError::Malformed)?;
        let tag: &[u8; Aead::TAG_LEN] = tag.try_into().map_err(|_| TokenError::Malformed)?;
        let mut buf = [0u8; MAX_ADDR_LEN + SUFFIX_LEN];
        let body = buf.get_mut(..sealed.len()).ok_or(TokenError::Malformed)?;
        body.copy_from_slice(sealed);
        p.open(&self.0, nonce, labels::TOKEN.as_bytes(), body, tag)
            .map_err(|_| TokenError::Authentication)?;
        let (claimed_addr, suffix) = body
            .split_at_checked(body.len() - SUFFIX_LEN)
            .ok_or(TokenError::Malformed)?;
        let (time, claimed_kind) = suffix.split_at_checked(8).ok_or(TokenError::Malformed)?;
        let issued_at = u64::from_be_bytes(time.try_into().map_err(|_| TokenError::Malformed)?);
        if claimed_kind != [kind as u8] {
            return Err(TokenError::WrongKind);
        }
        if !ct_eq(claimed_addr, addr) {
            return Err(TokenError::WrongAddress);
        }
        let age = now.checked_sub(issued_at).ok_or(TokenError::NotYetValid)?;
        if age > kind.lifetime_ns() {
            return Err(TokenError::Expired);
        }
        Ok(())
    }
}
