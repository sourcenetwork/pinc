//! The single error type of every primitive in this crate.
//!
//! Invariants: the type is `Copy`, carries no heap data and never includes key material. Every failure of an
//! operation on untrusted input is one of these variants; nothing in the crate panics.

use core::fmt;

/// Why a cryptographic operation was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CryptoError {
    /// A key, seed, public key, signature or tag has the wrong length for its algorithm.
    InvalidLength,
    /// The authentication tag does not match: the ciphertext, the associated data, the nonce or the key is wrong.
    Authentication,
    /// The input is too long for the algorithm to process.
    InputTooLong,
    /// The X25519 result is all zero: the peer sent a low-order point, so the exchange is not contributory.
    NonContributory,
    /// The ML-KEM encapsulation key failed the FIPS 203 modulus check.
    InvalidEncapsulationKey,
    /// A secret key or seed is out of range for its algorithm.
    InvalidSecretKey,
    /// A public key is not a valid point or encoding for its algorithm.
    InvalidPublicKey,
    /// The signature does not verify for this key and message.
    InvalidSignature,
    /// The ECDSA signature has a high `s` value; only the low-`s` form is accepted, so signatures cannot be malleated.
    HighS,
    /// A node identifier does not match the public key and algorithm it claims.
    NodeIdMismatch,
}

impl fmt::Display for CryptoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::InvalidLength => "a key, seed, signature or tag has the wrong length",
            Self::Authentication => "authentication failed",
            Self::InputTooLong => "input too long for the algorithm",
            Self::NonContributory => "the peer key is a low-order point",
            Self::InvalidEncapsulationKey => "invalid ML-KEM encapsulation key",
            Self::InvalidSecretKey => "secret key out of range",
            Self::InvalidPublicKey => "invalid public key",
            Self::InvalidSignature => "signature does not verify",
            Self::HighS => "ECDSA signature is not in low-s form",
            Self::NodeIdMismatch => "node id does not match the public key",
        })
    }
}

impl core::error::Error for CryptoError {}
