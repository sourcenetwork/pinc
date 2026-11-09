//! The message format.
//!
//! A message is `len3 | [venc(len ref) ref venc(n)] | venc(cnt) | parts`, where `len3` is the body length in three
//! big-endian bytes, the bracketed header is only in the first message of the initiator, and `cnt == 0` ends the
//! exchange. `venc` is the workspace varint of `vinc-wire`.
//!
//! A part is `tag | lo | hi | body`. The tag's low seven bits are the kind; the high bit ([`tag::INF`]) says the upper
//! bound is infinity and is omitted. A bound is `cpl venc(len) suffix`: the shared prefix length with the previous
//! bound in the message (capped at 255), then the rest. The previous bound starts empty in every message. Item
//! lists are `venc(len) item` each, so items have any length.
//!
//! Invariants: every decoder here reads from borrowed bytes, checks bounds before it reads, and reports a [`Reason`]
//! instead of panicking; the decoders never allocate.

#[cfg(feature = "alloc")]
use alloc::vec::Vec;

use vinc_wire::Reader;
#[cfg(feature = "alloc")]
use vinc_wire::varint;

use crate::error::Reason;
#[cfg(feature = "alloc")]
use crate::limits::FRAME_MAX;

/// A differing range splits into this many sub-ranges.
pub const SPLIT: usize = 16;
/// The initiator sends a differing range of at most this many items as ids (or, in the exact pass, as items).
pub const ALEAF: usize = 32;
/// The responder sends a differing range of at most this many items in full.
pub const BLEAF: usize = 6;
/// The responder streams its whole list when the initiator has fewer than `1 / COLD_RATIO` of its items.
pub const COLD_RATIO: u64 = 10;

/// The part kinds.
pub mod tag {
    /// A range with its fingerprint.
    pub const FP: u8 = 1;
    /// A range with the 8-byte ids of the sender's items in it.
    pub const IDS: u8 = 2;
    /// A range with the sender's items in it.
    pub const FULL: u8 = 3;
    /// The answer to an ids or items part: a bitmap of which of the asker's items the answerer has, then the
    /// answerer's extra items.
    pub const REPLY: u8 = 4;
    /// A chunk of a cold or tiny side's whole list; the chunk with an infinite upper bound is the last.
    pub const COLD: u8 = 5;
    /// The initiator's final check: the fingerprint of the whole set it computed for the responder.
    pub const CHECK: u8 = 6;
    /// The responder's answer to a check that disagrees.
    pub const MISS: u8 = 7;
    /// The tag bit that marks an infinite upper bound.
    pub const INF: u8 = 0x80;
}

/// The body of a framed message, checked against its three-byte length.
///
/// # Errors
/// [`Reason::Truncated`] if there is no length, [`Reason::Frame`] if it disagrees with the bytes.
pub fn frame_body(msg: &[u8]) -> Result<&[u8], Reason> {
    let (len, body) = msg.split_first_chunk::<3>().ok_or(Reason::Truncated)?;
    let n = (usize::from(len[0]) << 16) | (usize::from(len[1]) << 8) | usize::from(len[2]);
    if n == body.len() { Ok(body) } else { Err(Reason::Frame) }
}

/// The body length a three-byte header announces, for a host that cuts a byte stream into messages.
pub const fn frame_len(header: [u8; 3]) -> usize {
    (header[0] as usize) << 16 | (header[1] as usize) << 8 | header[2] as usize
}

#[cfg(feature = "alloc")]
/// The three-byte header of a body of `len` bytes, or `None` if the body is longer than a frame can carry.
#[allow(clippy::cast_possible_truncation, reason = "each byte is masked")]
pub(crate) const fn frame_header(len: usize) -> Option<[u8; 3]> {
    if len > FRAME_MAX {
        return None;
    }
    Some([(len >> 16) as u8, (len >> 8) as u8, len as u8])
}

/// The set reference in the first message of an initiator.
///
/// # Errors
/// A [`Reason`] if the message is not a well formed first message.
pub fn first_set_ref(msg: &[u8]) -> Result<&[u8], Reason> {
    let mut r = Reader::new(frame_body(msg)?);
    let n = count(&mut r)?;
    r.read_bytes(n).map_err(|_| Reason::Truncated)
}

/// A varint as a `usize`.
///
/// # Errors
/// [`Reason::Truncated`] for a bad varint, [`Reason::Count`] if it does not fit.
pub fn count(r: &mut Reader<'_>) -> Result<usize, Reason> {
    let v = r.read_varint().map_err(|_| Reason::Truncated)?;
    usize::try_from(v).map_err(|_| Reason::Count)
}

/// The shared prefix length of `a` and `b`.
pub fn common_prefix(a: &[u8], b: &[u8]) -> usize {
    a.iter().zip(b).take_while(|(x, y)| x == y).count()
}

#[cfg(feature = "alloc")]
/// The items of an item list, read one at a time from the message.
pub(crate) struct Items<'r, 'm> {
    r: &'r mut Reader<'m>,
    left: usize,
    max_item: usize,
}

#[cfg(feature = "alloc")]
impl<'r, 'm> Items<'r, 'm> {
    /// The item list that starts at `r`: a count, then that many `venc(len) item`.
    pub(crate) fn read(r: &'r mut Reader<'m>, max_item: usize) -> Result<Self, Reason> {
        let left = count(r)?;
        Ok(Self { r, left, max_item })
    }

    /// How many items remain.
    pub(crate) const fn left(&self) -> usize {
        self.left
    }

    /// The next item, or `None` at the end.
    pub(crate) fn next_item(&mut self) -> Result<Option<&'m [u8]>, Reason> {
        if self.left == 0 {
            return Ok(None);
        }
        self.left -= 1;
        let n = count(self.r)?;
        if n > self.max_item {
            return Err(Reason::Item);
        }
        self.r.read_bytes(n).map(Some).map_err(|_| Reason::Truncated)
    }
}

/// Append `v` as a varint.
///
/// # Errors
/// [`Reason::Count`] if `v` is 2^63 or more.
#[cfg(feature = "alloc")]
pub fn put_varint(buf: &mut Vec<u8>, v: usize) -> Result<(), Reason> {
    let mut tmp = [0u8; varint::MAX_LEN];
    let n = varint::encode(v as u64, &mut tmp).map_err(|_| Reason::Count)?;
    buf.extend_from_slice(tmp.get(..n).unwrap_or_default());
    Ok(())
}

/// Append the bound `b` as `cpl venc(len) suffix` against `last`, the previous bound of the message, and make `b` the
/// new `last`. The shared prefix length is capped at 255.
///
/// # Errors
/// [`Reason::Count`] if the length does not encode.
#[cfg(feature = "alloc")]
pub fn put_bound(buf: &mut Vec<u8>, last: &mut Vec<u8>, b: &[u8]) -> Result<(), Reason> {
    let c = u8::try_from(common_prefix(last, b)).unwrap_or(u8::MAX);
    let c_len = usize::from(c);
    buf.push(c);
    put_varint(buf, b.len() - c_len)?;
    buf.extend_from_slice(b.get(c_len..).unwrap_or_default());
    last.clear();
    last.extend_from_slice(b);
    Ok(())
}

/// Read one bound against `last`, the previous bound of the message, into `last`. The bound is at most `max` bytes.
///
/// # Errors
/// [`Reason::Bound`] if the shared prefix is longer than `last` or the bound longer than `max`, [`Reason::Truncated`]
/// if the message ends inside it.
#[cfg(feature = "alloc")]
pub fn read_bound(last: &mut Vec<u8>, r: &mut Reader<'_>, max: usize) -> Result<(), Reason> {
    let c = usize::from(r.read_u8().map_err(|_| Reason::Truncated)?);
    let n = count(r)?;
    if c > last.len() || c.saturating_add(n) > max {
        return Err(Reason::Bound);
    }
    let suffix = r.read_bytes(n).map_err(|_| Reason::Truncated)?;
    last.truncate(c);
    last.extend_from_slice(suffix);
    Ok(())
}
