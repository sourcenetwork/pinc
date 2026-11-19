//! Reading a message body back: which message it is and whether its bytes are exactly that message.
//!
//! A body is the byte stream the payload registry generates (see [`crate::suite::crypto::payload`]). Its first block
//! names the message; the creator is then `Registry::creator_of`, and the whole body can be compared with what the
//! registry would generate. Invariant: nothing here trusts a length or an id from the wire before the registry has
//! confirmed the message exists.

use crate::suite::crypto::payload::{HEADER_LEN, MAGIC};
use crate::suite::crypto::{MsgId, PayloadError, Registry};

/// How a body compares with the message it claims to be.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Every byte of the whole message.
    Whole,
    /// A correct prefix of the message, shorter than it.
    Partial,
    /// Bytes that are not the message (changed, extended or of another message).
    Corrupt,
}

/// The message a body starts with: its first block header, with block index 0.
pub fn message_id(body: &[u8]) -> Option<MsgId> {
    let head = body.get(..HEADER_LEN)?;
    let (magic, rest) = head.split_at(MAGIC.len());
    if magic != MAGIC {
        return None;
    }
    let (id, idx) = rest.split_at(8);
    let mut b = [0u8; 8];
    b.copy_from_slice(id);
    (idx == [0, 0, 0, 0]).then_some(MsgId(u64::from_le_bytes(b)))
}

/// Compares `body` with the start of message `msg`.
pub fn verify(reg: &Registry, msg: MsgId, body: &[u8]) -> Verdict {
    let mut expect = vec![0u8; body.len()];
    if reg.fill(msg, 0, &mut expect).is_err() || expect != body {
        return Verdict::Corrupt;
    }
    match reg.fill(msg, body.len() as u64, &mut [0u8; 1]) {
        Err(PayloadError::OutOfRange) => Verdict::Whole,
        _ => Verdict::Partial,
    }
}

/// The bytes of message `msg`, which has `len` bytes.
pub fn render(reg: &Registry, msg: MsgId, len: u64) -> Vec<u8> {
    let mut out = vec![0u8; usize::try_from(len).unwrap_or(0)];
    // a message this node just created: the range is in bounds by construction
    let _ = reg.fill(msg, 0, &mut out);
    out
}
