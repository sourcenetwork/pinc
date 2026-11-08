//! Strict DAG-CBOR: a pull decoder and a canonical encoder over caller buffers.
//!
//! Invariants: the decoder accepts only the canonical DAG-CBOR subset (minimal arguments, definite lengths, valid
//! UTF-8, 64-bit finite floats, only tag 42 over a `0x00`-prefixed byte string, text map keys unique and in
//! length-then-bytewise order) and the encoder emits exactly that subset, so decode then encode is the identity. Map
//! keys are checked wherever a map is walked: by [`MapReader`] and by [`Decoder::skip_value`]; a caller that reads map
//! entries with bare [`Decoder::next_item`] calls takes on that check itself.
//! Neither side allocates; nesting is bounded by [`MAX_DEPTH`] wherever it is walked.

mod decode;
mod encode;

pub use decode::{Decoder, MapReader};
pub use encode::{Encoder, MapKeys};

use crate::error::WireError;

/// The deepest container nesting [`Decoder::skip_value`] walks.
pub const MAX_DEPTH: usize = 64;

/// The tag number DAG-CBOR reserves for CIDs.
pub(crate) const TAG_CID: u64 = 42;

/// One decoded item. Containers and tags yield only their header; their content follows as further items.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Item<'a> {
    /// An unsigned integer.
    Unsigned(u64),
    /// A negative integer, meaning `-1 - n`.
    Negative(u64),
    /// A byte string, borrowed from the input.
    Bytes(&'a [u8]),
    /// A text string, borrowed from the input.
    Text(&'a str),
    /// An array header with its element count.
    Array(u64),
    /// A map header with its entry count.
    Map(u64),
    /// A tag header (always 42, followed by the CID byte string).
    Tag(u64),
    /// A boolean.
    Bool(bool),
    /// Null.
    Null,
    /// A finite 64-bit float.
    Float(f64),
}

/// Check that `key` follows `prev` in DAG-CBOR key order (shorter first, then bytewise) and is not a duplicate.
pub(crate) fn check_key_order(prev: Option<&str>, key: &str) -> Result<(), WireError> {
    let Some(prev) = prev else { return Ok(()) };
    match (prev.len(), prev.as_bytes()).cmp(&(key.len(), key.as_bytes())) {
        core::cmp::Ordering::Less => Ok(()),
        core::cmp::Ordering::Equal => Err(WireError::NonCanonical("duplicate map key")),
        core::cmp::Ordering::Greater => Err(WireError::NonCanonical("map keys out of order")),
    }
}
