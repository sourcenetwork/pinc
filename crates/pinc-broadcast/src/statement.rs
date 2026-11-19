//! The signed statement of a topic message, its content id and its CID.
//!
//! A statement is one canonical DAG-CBOR map that says who published which message where: the author (algorithm and
//! node id), its position (incarnation and sequence number), the topic, the time, the flags, the parents (content ids
//! of earlier messages) and the body, by the plain BLAKE3 hash of its bytes, so the body is addressable by itself.
//! It is never carried on the wire: the signer and the verifier each build it from the fields of the message head.
//!
//! The content id is the plain BLAKE3 hash of the statement. It covers every field above and does not cover the
//! signature or the public key, so one message keeps one id however it is signed. The signature is made over
//! [`signed_message`], the statement label followed by the id.
//!
//! The integer fields are full 64-bit unsigned values (the incarnation word is already above 2^53), so a reader
//! limited to 53-bit or signed 64-bit integers must decode them with a wide integer type.
//!
//! Invariants: the encoding is canonical (one byte string per set of fields; the map's keys are in DAG-CBOR order
//! and the parents strictly ascending); [`encode`] never panics, allocates nothing, and writes at most
//! [`STATEMENT_MAX`] bytes.

use pinc_crypto::{IdentityAlg, labels};
use pinc_membership::NodeId;
use pinc_wire::cbor::Encoder;
use pinc_wire::hlc::Hlc;

use crate::consts::MAX_TOPIC;

/// The content id of a statement: the plain BLAKE3 hash of its bytes.
pub type ContentId = [u8; 32];

/// The most parents a message names.
pub const MAX_PARENTS: usize = 8;

/// The flag bit of a body that is bytes rather than a stream slice.
pub const FLAG_ISB: u8 = 1;

/// The length of a CID of this module: version, codec, hash code, digest length and the 32-byte digest.
const CID_LEN: usize = 36;
/// A CID link in a statement: tag 42 (2 bytes), the byte string head (2), the `0x00` prefix (1) and the CID.
const LINK_LEN: usize = 2 + 2 + 1 + CID_LEN;
/// The value of the `kind` entry.
const KIND: &str = "pinc/broadcast/2";
/// A `CIDv1` of the raw codec and the BLAKE3 hash, up to its digest.
const BODY_PREFIX: [u8; 4] = [0x01, 0x55, 0x1e, 0x20];
/// A `CIDv1` of the dag-cbor codec and the BLAKE3 hash, up to its digest.
const STATEMENT_PREFIX: [u8; 4] = [0x01, 0x71, 0x1e, 0x20];
/// The length of [`signed_message`].
const SIGNED_LEN: usize = labels::STATEMENT.len() + 32;

const _: () = assert!(
    MAX_TOPIC >= 24 && MAX_TOPIC <= 255,
    "the topic's byte string head is two bytes"
);

/// The longest statement: the longest topic, [`MAX_PARENTS`] parents, and every integer at its widest head.
pub const STATEMENT_MAX: usize = 1 // the map head
    + (3 + 1 + 9) // seq
    + (4 + 1 + LINK_LEN) // body
    + (4 + 1 + 1 + KIND.len()) // kind
    + (4 + 1 + 1 + 9 + 5) // time
    + (5 + 1 + 1) // flags
    + (5 + 1 + 2 + MAX_TOPIC) // topic
    + (6 + 1 + 2 + 1 + 32) // origin
    + (7 + 1 + 1 + MAX_PARENTS * LINK_LEN) // parents
    + (11 + 1 + 9); // incarnation

/// The fields a statement says.
#[derive(Debug, Clone, Copy)]
pub struct Fields<'a> {
    /// The origin's signature algorithm.
    pub origin_alg: IdentityAlg,
    /// The origin: its node id.
    pub origin: &'a NodeId,
    /// The origin's incarnation.
    pub incarnation: u64,
    /// The sequence number within the incarnation.
    pub seq: u64,
    /// The topic.
    pub topic: &'a [u8],
    /// The origin's timestamp.
    pub time: Hlc,
    /// The flags: bit 0 is [`FLAG_ISB`]; the others are reserved and must be 0.
    pub flags: u8,
    /// The content ids of the parents, strictly ascending.
    pub parents: &'a [ContentId],
    /// The plain BLAKE3 hash of the body.
    pub body: &'a [u8; 32],
}

/// Why a statement cannot be built from some fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatementError {
    /// More than [`MAX_PARENTS`] parents.
    TooManyParents,
    /// The parents are not strictly ascending by their bytes.
    ParentsNotAscending,
    /// A flag bit other than bit 0 is set.
    ReservedFlags,
    /// The topic is longer than the format allows.
    TopicTooLong,
    /// The statement does not fit its buffer (the checks above bound every part, so this is not reachable).
    BufferTooSmall,
}

impl core::fmt::Display for StatementError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::TooManyParents => "a message names at most 8 parents",
            Self::ParentsNotAscending => "the parents must be in strictly ascending order",
            Self::ReservedFlags => "a reserved flag bit is set",
            Self::TopicTooLong => "the topic is longer than 255 bytes",
            Self::BufferTooSmall => "the statement does not fit its buffer",
        })
    }
}

impl core::error::Error for StatementError {}

/// The CID of a statement with content id `id`: `01 71 1e 20 || id`.
pub fn cid(id: &ContentId) -> [u8; CID_LEN] {
    link(STATEMENT_PREFIX, id)
}

/// The CID of a body with plain BLAKE3 hash `hash`: `01 55 1e 20 || hash`.
pub fn body_cid(hash: &[u8; 32]) -> [u8; CID_LEN] {
    link(BODY_PREFIX, hash)
}

fn link(prefix: [u8; 4], digest: &[u8; 32]) -> [u8; CID_LEN] {
    let mut out = [0u8; CID_LEN];
    let (p, d) = out.split_at_mut(prefix.len());
    p.copy_from_slice(&prefix);
    d.copy_from_slice(digest);
    out
}

/// Whether `parents` are strictly ascending by their bytes (no duplicate), the one order a statement and a head accept.
pub(crate) fn strictly_ascending(parents: &[ContentId]) -> bool {
    parents.windows(2).all(|w| matches!(w, [a, b] if a < b))
}

/// The content id of an encoded statement.
pub fn content_id(statement: &[u8]) -> ContentId {
    *blake3::hash(statement).as_bytes()
}

/// The message a statement's signature covers: the statement label followed by the content id.
pub fn signed_message(id: &ContentId) -> [u8; SIGNED_LEN] {
    let mut msg = [0u8; SIGNED_LEN];
    let (label, tail) = msg.split_at_mut(labels::STATEMENT.len());
    label.copy_from_slice(labels::STATEMENT.as_bytes());
    tail.copy_from_slice(id);
    msg
}

/// Encode the statement of `fields` into `out` and return its length.
///
/// # Errors
/// [`StatementError`] for a topic over [`MAX_TOPIC`] bytes, more than [`MAX_PARENTS`] parents, parents not strictly
/// ascending, or a reserved flag bit.
pub fn encode(fields: &Fields<'_>, out: &mut [u8; STATEMENT_MAX]) -> Result<usize, StatementError> {
    if fields.topic.len() > MAX_TOPIC {
        return Err(StatementError::TopicTooLong);
    }
    if fields.parents.len() > MAX_PARENTS {
        return Err(StatementError::TooManyParents);
    }
    if !strictly_ascending(fields.parents) {
        return Err(StatementError::ParentsNotAscending);
    }
    if fields.flags & !FLAG_ISB != 0 {
        return Err(StatementError::ReservedFlags);
    }
    write(fields, out).map_err(|_| StatementError::BufferTooSmall)
}

fn write(f: &Fields<'_>, out: &mut [u8]) -> Result<usize, pinc_wire::WireError> {
    let mut enc = Encoder::new(out);
    let mut keys = enc.ordered_map(9)?;
    keys.key(&mut enc, "seq")?;
    enc.unsigned(f.seq)?;
    keys.key(&mut enc, "body")?;
    enc.tag_cid(&body_cid(f.body))?;
    keys.key(&mut enc, "kind")?;
    enc.text(KIND)?;
    keys.key(&mut enc, "time")?;
    enc.array(2)?;
    enc.unsigned(f.time.wall)?;
    enc.unsigned(u64::from(f.time.counter))?;
    keys.key(&mut enc, "flags")?;
    enc.unsigned(u64::from(f.flags))?;
    keys.key(&mut enc, "topic")?;
    enc.bytes(f.topic)?;
    keys.key(&mut enc, "origin")?;
    let mut origin = [f.origin_alg.tag(); 33];
    if let Some((_, id)) = origin.split_first_mut() {
        id.copy_from_slice(f.origin);
    }
    enc.bytes(&origin)?;
    keys.key(&mut enc, "parents")?;
    enc.array(f.parents.len() as u64)?;
    for p in f.parents {
        enc.tag_cid(&cid(p))?;
    }
    keys.key(&mut enc, "incarnation")?;
    enc.unsigned(f.incarnation)?;
    Ok(enc.written().len())
}

#[cfg(test)]
mod tests;
