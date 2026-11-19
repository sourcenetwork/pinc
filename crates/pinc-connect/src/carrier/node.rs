//! Node ids on the wire: one algorithm tag byte, then the 32 identifier bytes.
//!
//! Invariants: a node id is exactly [`NODE_ID_LEN`] bytes; an unknown algorithm tag is refused, never mapped to a
//! default.

use pinc_crypto::{IdentityAlg, NodeId};
use pinc_wire::{Reader, WireError, Writer};

/// The encoded size of a node id: the algorithm tag and 32 bytes.
pub const NODE_ID_LEN: usize = 33;

/// Read a node id.
///
/// # Errors
/// [`WireError::Truncated`] if fewer than [`NODE_ID_LEN`] bytes remain, [`WireError::Unexpected`] for an unknown
/// algorithm tag. Nothing is consumed on failure.
pub fn read(r: &mut Reader<'_>) -> Result<NodeId, WireError> {
    let mut probe = *r;
    let tag = probe.read_u8()?;
    let bytes = probe.read_array::<32>()?;
    let alg = IdentityAlg::from_tag(tag).ok_or(WireError::Unexpected("identity algorithm tag"))?;
    *r = probe;
    Ok(NodeId { alg, bytes })
}

/// Write a node id.
///
/// # Errors
/// [`WireError::BufferTooSmall`] if it does not fit.
pub fn write(w: &mut Writer<'_>, id: &NodeId) -> Result<(), WireError> {
    w.ensure(NODE_ID_LEN)?;
    w.put_u8(id.alg.tag())?;
    w.put_slice(&id.bytes)
}
