//! The error type of every key store operation.
//!
//! Invariants: the type is `Copy`, carries no heap data and never holds key material, a message or a path. A TPM
//! refusal carries the TPM response code so the caller can tell an authorization failure from a missing handle.

use core::fmt;

use pinc_crypto::CryptoError;

/// Why a key store operation failed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum KeyStoreError {
    /// The key handle does not name a key in this store.
    UnknownKey,
    /// The key exists but is not the kind this operation needs (a signing key where a KEM key is required, or the reverse).
    WrongKeyKind,
    /// This store cannot hold that kind of key or perform that operation.
    Unsupported,
    /// A cryptographic primitive refused its input.
    Crypto(CryptoError),
    /// The operating system could not provide random bytes.
    Entropy,
    /// Sealed data is malformed, was altered, or was sealed by another store.
    InvalidSealed,
    /// A TPM handle is not valid for this operation (a persistent handle must be in `0x8100_0000..=0x81FF_FFFF`).
    #[cfg(feature = "hwenc")]
    InvalidHandle,
    /// An auth value is longer than a TPM accepts.
    #[cfg(feature = "hwenc")]
    InvalidAuth,
    /// The link to the TPM failed.
    #[cfg(feature = "hwenc")]
    Transport(std::io::ErrorKind),
    /// The TPM sent a message that is not valid TPM 2.0, or a command could not be built.
    #[cfg(feature = "hwenc")]
    Protocol,
    /// The TPM refused a command; `code` is its response code.
    #[cfg(feature = "hwenc")]
    Tpm {
        /// The TPM response code (`TPM_RC_*`), as sent on the wire.
        code: u32,
    },
    /// The TPM kept answering "send the command again" until the retry bound ran out; `code` is the last answer.
    #[cfg(feature = "hwenc")]
    TpmBusy {
        /// The TPM warning code (`TPM_RC_RETRY`, `TPM_RC_YIELDED` or `TPM_RC_TESTING`).
        code: u32,
    },
}

impl fmt::Display for KeyStoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownKey => f.write_str("the key handle is not in this store"),
            Self::WrongKeyKind => f.write_str("the key is not the kind this operation needs"),
            Self::Unsupported => f.write_str("this store cannot hold that key or do that operation"),
            Self::Crypto(e) => write!(f, "cryptographic failure: {e}"),
            Self::Entropy => f.write_str("the operating system could not provide random bytes"),
            Self::InvalidSealed => f.write_str("the sealed data is malformed or was altered"),
            #[cfg(feature = "hwenc")]
            Self::InvalidHandle => f.write_str("the TPM handle is not valid for this operation"),
            #[cfg(feature = "hwenc")]
            Self::InvalidAuth => f.write_str("the auth value is longer than a TPM accepts"),
            #[cfg(feature = "hwenc")]
            Self::Transport(kind) => write!(f, "the link to the TPM failed: {kind}"),
            #[cfg(feature = "hwenc")]
            Self::Protocol => f.write_str("the TPM message is not valid"),
            #[cfg(feature = "hwenc")]
            Self::Tpm { code } => write!(f, "the TPM refused the command (response code {code:#06x})"),
            #[cfg(feature = "hwenc")]
            Self::TpmBusy { code } => write!(
                f,
                "the TPM stayed busy and did not take the command (response code {code:#06x})"
            ),
        }
    }
}

impl core::error::Error for KeyStoreError {}

impl From<CryptoError> for KeyStoreError {
    fn from(e: CryptoError) -> Self {
        Self::Crypto(e)
    }
}

/// The result of a key store operation.
pub type Result<T> = core::result::Result<T, KeyStoreError>;
