//! The single error type of every codec in this crate.
//!
//! Invariants: the type is `Copy`, carries no heap data, and a decode or encode failure is always one of these
//! variants (no codec panics on any input).

use core::fmt;

/// Why a read, write, decode or encode was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WireError {
    /// The input ended early.
    Truncated {
        /// How many more bytes were needed.
        needed: usize,
    },
    /// The output buffer is too small; nothing was written.
    BufferTooSmall {
        /// How many more bytes of room were needed.
        needed: usize,
    },
    /// A varint is longer than 9 bytes.
    VarintTooLong,
    /// A varint value is 2^63 or more.
    VarintOverflow,
    /// A varint has a redundant trailing zero byte.
    VarintNonMinimal,
    /// The bytes are well formed CBOR but violate a DAG-CBOR strictness rule, named by the reason.
    NonCanonical(&'static str),
    /// A valid item of the wrong kind was found where another was required.
    Unexpected(&'static str),
    /// Nesting is deeper than [`crate::cbor::MAX_DEPTH`].
    DepthExceeded,
}

impl fmt::Display for WireError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Truncated { needed } => write!(f, "input ended early, {needed} more bytes needed"),
            Self::BufferTooSmall { needed } => write!(f, "output buffer too small, {needed} more bytes needed"),
            Self::VarintTooLong => f.write_str("varint is longer than 9 bytes"),
            Self::VarintOverflow => f.write_str("varint value is 2^63 or more"),
            Self::VarintNonMinimal => f.write_str("varint is not minimally encoded"),
            Self::NonCanonical(reason) => write!(f, "not canonical DAG-CBOR: {reason}"),
            Self::Unexpected(what) => write!(f, "unexpected item: {what}"),
            Self::DepthExceeded => f.write_str("nesting is too deep"),
        }
    }
}

// `core::error::Error` is the same trait `std::error::Error` re-exports, so this serves `std` users as well.
impl core::error::Error for WireError {}
