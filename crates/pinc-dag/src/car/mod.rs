//! CAR v1 archives: a header naming the roots, then length-prefixed sections of a CID and its block.
//!
//! Layout: `varint(len) header` then any number of `varint(len) cid block` sections, where `len` counts the bytes
//! after the varint and the header is the canonical DAG-CBOR map `{"roots": [CID...], "version": 1}`.
//! Invariants: the header holds exactly those two keys, the version is 1, every varint is minimal, and every length
//! is checked against a caller-given maximum before any byte of the body is required, so a hostile length can
//! neither allocate nor stall a reader. Truncation and oversize are typed errors, never panics.
//!
//! [`CarReader`] walks a complete borrowed buffer; [`CarDecoder`] takes streamed input, holding at most one section.

mod reader;
mod stream;
mod writer;

use core::fmt;

use pinc_wire::{WireError, varint};

use crate::cid::{CidError, CidRef};

pub use reader::{CarReader, Sections};
pub use stream::{CarDecoder, Decoded};
pub use writer::CarWriter;

/// The roots of a CAR: an iterator of the header's CIDs.
pub type Roots<'a> = crate::cid::CidList<'a>;

/// Why a CAR was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CarError {
    /// A varint or the header CBOR is malformed, or an output buffer is too small.
    Wire(WireError),
    /// A CID is invalid, or a section's block does not match its CID.
    Cid(CidError),
    /// The input ended early.
    Truncated {
        /// How many more bytes were needed.
        needed: usize,
    },
    /// A header or section is longer than the caller's maximum.
    TooLarge {
        /// The declared length.
        len: u64,
        /// The maximum allowed.
        max: usize,
    },
    /// The header is not `{"roots": [CID...], "version": 1}`; the reason is named.
    BadHeader(&'static str),
}

impl From<WireError> for CarError {
    fn from(e: WireError) -> Self {
        Self::Wire(e)
    }
}

impl From<CidError> for CarError {
    fn from(e: CidError) -> Self {
        Self::Cid(e)
    }
}

impl fmt::Display for CarError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Wire(e) => write!(f, "malformed CAR: {e}"),
            Self::Cid(e) => write!(f, "invalid CID in CAR: {e}"),
            Self::Truncated { needed } => write!(f, "CAR ended early, {needed} more bytes needed"),
            Self::TooLarge { len, max } => write!(f, "CAR section of {len} bytes is over the {max} byte limit"),
            Self::BadHeader(why) => write!(f, "bad CAR header: {why}"),
        }
    }
}

impl core::error::Error for CarError {}

/// One length-prefixed frame at the start of some input.
pub(crate) enum Frame<'a> {
    /// The frame is incomplete; at least this many more bytes are needed.
    Need(usize),
    /// The frame body, and the bytes it occupied including its length prefix.
    Ready { consumed: usize, body: &'a [u8] },
}

/// Split the frame at the start of `input`, refusing a body longer than `max` before any of it is required.
pub(crate) fn frame(input: &[u8], max: usize) -> Result<Frame<'_>, CarError> {
    let (len, prefix) = match varint::decode(input) {
        Ok(v) => v,
        Err(WireError::Truncated { needed }) => return Ok(Frame::Need(needed)),
        Err(e) => return Err(e.into()),
    };
    let body_len = usize::try_from(len)
        .ok()
        .filter(|&l| l <= max)
        .ok_or(CarError::TooLarge { len, max })?;
    let total = prefix.saturating_add(body_len);
    match input.get(prefix..total) {
        Some(body) => Ok(Frame::Ready { consumed: total, body }),
        None => Ok(Frame::Need(total.saturating_sub(input.len()))),
    }
}

/// Split a section body into its CID and block, checking the block against the CID when `verify` is set.
pub(crate) fn split_section(body: &[u8], verify: bool) -> Result<(CidRef<'_>, &[u8]), CarError> {
    let (cid, block) = CidRef::parse_prefix(body)?;
    if verify {
        cid.verify(block)?;
    }
    Ok((cid, block))
}
