//! The error type of the CID layer.

use core::fmt;

use vinc_wire::WireError;

/// Why a CID was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CidError {
    /// A varint or the CBOR around the CID is malformed or truncated.
    Wire(WireError),
    /// The bytes are a `CIDv0` (a bare SHA2-256 multihash), which is not accepted.
    CidV0,
    /// The version is not 1.
    UnsupportedVersion(u64),
    /// The digest is longer than 64 bytes.
    DigestTooLong(u64),
    /// A known hash code carries a digest that is not 32 bytes.
    DigestLenMismatch {
        /// The multihash code.
        hash: u64,
        /// The declared digest length.
        len: u64,
    },
    /// Bytes follow the CID.
    TrailingBytes,
    /// The hash code is neither SHA2-256 nor BLAKE3, so the digest cannot be computed.
    UnsupportedHash(u64),
    /// The digest does not match the block.
    DigestMismatch,
    /// The text is not a multibase base32 lower CID; the reason is named.
    BadText(&'static str),
    /// The output buffer is too small.
    BufferTooSmall {
        /// How many more bytes of room were needed.
        needed: usize,
    },
}

impl From<WireError> for CidError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl fmt::Display for CidError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "malformed CID: {e}"),
            Self::CidV0 => f.write_str("CIDv0 is not accepted"),
            Self::UnsupportedVersion(v) => write!(f, "CID version {v} is not supported"),
            Self::DigestTooLong(n) => write!(f, "digest of {n} bytes is longer than 64"),
            Self::DigestLenMismatch { hash, len } => {
                write!(f, "hash code {hash:#x} needs a 32 byte digest, found {len}")
            }
            Self::TrailingBytes => f.write_str("bytes follow the CID"),
            Self::UnsupportedHash(h) => write!(f, "hash code {h:#x} is not supported"),
            Self::DigestMismatch => f.write_str("digest does not match the block"),
            Self::BadText(why) => write!(f, "not a CID text: {why}"),
            Self::BufferTooSmall { needed } => write!(f, "output buffer too small, {needed} more bytes needed"),
        }
    }
}

impl core::error::Error for CidError {}
