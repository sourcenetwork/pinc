//! `DefraDB`'s block format: a DAG-CBOR map around an opaque CRDT delta, parsed in place and encoded canonically.
//!
//! A block is the map `{"delta", "heads"?, "links"?, "signature"?, "encryption"?}` (the canonical key order:
//! shorter keys first, then bytewise). `delta` is any DAG-CBOR item and is kept as borrowed raw bytes; CRDT deltas
//! are not modelled here. `heads` is an array of CID links sorted by CID text; `links` is an array of
//! `{"link": CID, "name": text}` maps sorted by CID text, then by name; `signature` and `encryption` are single CID
//! links to separate blocks. An absent option is a missing key, and the encoder never writes an empty array.
//!
//! Invariants of [`BlockRef::parse`]: the whole input is one canonical map (no trailing bytes), `delta` is present,
//! heads and links are strictly ascending (so a duplicate or out-of-order entry is refused and the canonical form
//! of a block is unique), and every CID is valid. Following `DefraDB`, which reads blocks with serde and no
//! `deny_unknown_fields`, an unknown key is accepted and its value validated and skipped (inside a link map too);
//! a block with unknown keys therefore parses but does not re-encode byte for byte. Also as there, a `null` or an
//! empty array stands for "no heads" or "no links", and `null` for an absent CID.

mod encode;
mod parse;

pub use encode::{BlockParts, Link, encode_block};
pub use parse::{BlockRef, Heads, LinkRef, Links};

use core::fmt;

use crate::cid::CidError;
use pinc_wire::WireError;

/// Why a block was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockError {
    /// The CBOR is malformed, not canonical, or the output buffer is too small.
    Wire(WireError),
    /// A CID inside the block is invalid.
    Cid(CidError),
    /// Bytes follow the block map.
    TrailingBytes,
    /// The block has no `delta`.
    MissingDelta,
    /// A field holds an item of the wrong kind or lacks a required part; the field is named.
    Malformed(&'static str),
    /// Heads or links are not strictly ascending; the field is named.
    Unordered(&'static str),
}

impl From<WireError> for BlockError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl From<CidError> for BlockError {
    fn from(e: CidError) -> Self {
        Self::Cid(e)
    }
}

impl fmt::Display for BlockError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "malformed block: {e}"),
            Self::Cid(e) => write!(f, "invalid CID in block: {e}"),
            Self::TrailingBytes => f.write_str("bytes follow the block"),
            Self::MissingDelta => f.write_str("block has no delta"),
            Self::Malformed(what) => write!(f, "malformed block field: {what}"),
            Self::Unordered(what) => write!(f, "{what} are not strictly ascending by CID text"),
        }
    }
}

impl core::error::Error for BlockError {}
