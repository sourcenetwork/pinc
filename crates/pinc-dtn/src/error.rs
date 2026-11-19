//! The error type of the bundle, encryption and erasure code paths.
//!
//! Invariants: the type is `Copy`, carries no heap data and never includes key material; every failure on
//! untrusted input is one of these variants.

use core::fmt;

use pinc_crypto::CryptoError;
use pinc_dag::tree::TreeError;
use pinc_wire::WireError;

/// Why a bundle, encryption or erasure-code operation was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DtnError {
    /// A cryptographic operation failed (a bad signature, a failed authentication, a bad key).
    Crypto(CryptoError),
    /// A slice proof or the tree layout failed.
    Tree(TreeError),
    /// A head or acknowledgement could not be encoded or decoded.
    Wire(WireError),
    /// The erasure or slice parameters, or the payload length, are not valid.
    Params,
    /// A caller buffer or range has the wrong size or alignment for the bundle.
    Buffer,
    /// The bundle is addressed to another node or to another key epoch.
    WrongRecipient,
    /// The bundle is past its lifetime.
    Expired,
    /// Fewer symbols than the code needs are held, so the bundle cannot be decoded yet.
    Incomplete,
    /// The decoded bundle does not hash to the signed root: the sender's parity was not a valid code word.
    Inconsistent,
    /// The bundle id in the head is not the one derived from its source, creation time and ephemeral key.
    BadId,
    /// The set of verified ranges is full; the slice was not recorded and can be fetched again.
    ReceptionFull,
}

impl From<CryptoError> for DtnError {
    fn from(e: CryptoError) -> Self {
        Self::Crypto(e)
    }
}

impl From<TreeError> for DtnError {
    fn from(e: TreeError) -> Self {
        Self::Tree(e)
    }
}

impl From<WireError> for DtnError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl fmt::Display for DtnError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Crypto(e) => write!(f, "cryptographic failure: {e}"),
            Self::Tree(e) => write!(f, "slice proof failure: {e}"),
            Self::Wire(e) => write!(f, "encoding failure: {e}"),
            Self::Params => f.write_str("invalid erasure or slice parameters"),
            Self::Buffer => f.write_str("a buffer or range has the wrong size for the bundle"),
            Self::WrongRecipient => f.write_str("the bundle is not addressed to this node and key epoch"),
            Self::Expired => f.write_str("the bundle is past its lifetime"),
            Self::Incomplete => f.write_str("too few symbols held to decode"),
            Self::Inconsistent => f.write_str("the decoded bundle does not match its root"),
            Self::BadId => f.write_str("the bundle id does not match the head"),
            Self::ReceptionFull => f.write_str("the verified-range set is full"),
        }
    }
}

impl core::error::Error for DtnError {}
