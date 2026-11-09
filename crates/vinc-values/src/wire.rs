//! The value wire: the request, the group frame and the two range-proof extension frames.
//!
//! # Formats
//!
//! All integers are big-endian; `sid` is a `vinc-wire` varint.
//!
//! | Frame | Where | Fields |
//! |---|---|---|
//! | REQ | first bytes of a request stream | `1`, root (32), count (1), then count times offset (8), length (8) |
//! | GROUP | response stream | `2`, offset (8), length (4), proof length (2), follows (1), proof, data |
//! | PROOF (`0x4f`) | extension frame | sid, group log (1), start (8), length (4), value length (8), parents |
//! | `PROOF_REQ` (`0x49`) | extension frame | sid, from (8), upto (8) |
//!
//! The proof of a GROUP is the BLAKE3 parent pairs (64 bytes each) that the previous group of the same range leaves
//! open, so the stream of a range is exactly the range encoding of `vinc-dag` with a 16-byte header before every group
//! and its pairs. `follows` is 0 for the first group of a range (its proof is the whole path from the root) and 1 for
//! every later group. A PROOF carries only the parent pairs of a range of at most 16 groups, in pre-order, so a
//! receiver can verify any one group of the range out of order.
//!
//! # Invariants
//!
//! Parsing is strict: an unknown type, a count over [`MAX_REQ_RANGES`], a flag other than 0 or 1, a proof that is not a
//! whole number of pairs and trailing bytes in a fixed-size body are all refused with a [`WireError`]. Parsing borrows
//! from the input and never copies; encoding checks the room first and writes nothing on failure. Nothing panics.

use vinc_dag::tree::PARENT_LEN;
use vinc_wire::{Reader, WireError, Writer};

use crate::knobs::{MAX_REQ_RANGES, WT_PMAX};
use crate::span::Span;

/// The type byte of a REQ.
pub const T_REQ: u8 = 1;
/// The type byte of a GROUP.
pub const T_GROUP: u8 = 2;
/// The size of a REQ without its ranges.
pub const REQ_FIXED: usize = 34;
/// The size of a GROUP header.
pub const GROUP_HDR: usize = 16;
/// The size of a REQ with the most ranges.
pub const REQ_MAX: usize = REQ_FIXED + 16 * MAX_REQ_RANGES;
/// The size of the fixed part of a PROOF body after the stream id.
const PROOF_FIXED: usize = 1 + 8 + 4 + 8;
/// The most bytes the head of a PROOF body takes: a 9-byte id and the fixed part.
const PROOF_HEAD_MAX: usize = 9 + PROOF_FIXED;
/// The largest PROOF body: the largest head and the largest proof.
pub const PROOF_BODY_MAX: usize = PROOF_HEAD_MAX + WT_PMAX;

/// A parsed REQ, borrowing its bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Req<'a> {
    root: &'a [u8; 32],
    ranges: &'a [u8],
}

impl<'a> Req<'a> {
    /// Parse a REQ from the start of `buf`; returns it and the bytes it took.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if `buf` ends early, [`WireError::Unexpected`] for a wrong type or too many ranges.
    pub fn parse(buf: &'a [u8]) -> Result<(Self, usize), WireError> {
        let mut r = Reader::new(buf);
        if r.read_u8()? != T_REQ {
            return Err(WireError::Unexpected("not a request"));
        }
        let root = r
            .read_bytes(32)?
            .first_chunk::<32>()
            .ok_or(WireError::Truncated { needed: 32 })?;
        let count = usize::from(r.read_u8()?);
        if count > MAX_REQ_RANGES {
            return Err(WireError::Unexpected("too many ranges"));
        }
        let ranges = r.read_bytes(16 * count)?;
        Ok((Self { root, ranges }, REQ_FIXED + 16 * count))
    }

    /// How many bytes a REQ whose first [`REQ_FIXED`] bytes are `head` takes in all.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if `head` is shorter than [`REQ_FIXED`], [`WireError::Unexpected`] for a bad type or count.
    pub fn total_len(head: &[u8]) -> Result<usize, WireError> {
        let h = head.first_chunk::<REQ_FIXED>().ok_or(WireError::Truncated {
            needed: REQ_FIXED.saturating_sub(head.len()),
        })?;
        let count = usize::from(h[REQ_FIXED - 1]);
        if h[0] != T_REQ || count > MAX_REQ_RANGES {
            return Err(WireError::Unexpected("bad request header"));
        }
        Ok(REQ_FIXED + 16 * count)
    }

    /// The root of the requested value.
    pub const fn root(&self) -> &'a [u8; 32] {
        self.root
    }

    /// The number of ranges.
    pub const fn count(&self) -> usize {
        self.ranges.len() / 16
    }

    /// The requested ranges, in order.
    pub fn ranges(&self) -> impl Iterator<Item = Span> + 'a {
        self.ranges.as_chunks::<16>().0.iter().map(|c| {
            let (a, b) = c.split_at(8);
            Span {
                off: be64(a),
                len: be64(b),
            }
        })
    }

    /// Encode a REQ of `root` and `ranges` into `out`; returns the bytes written.
    ///
    /// # Errors
    /// [`WireError::Unexpected`] for more than [`MAX_REQ_RANGES`] ranges, [`WireError::BufferTooSmall`] if `out` is short.
    pub fn encode(root: &[u8; 32], ranges: &[Span], out: &mut [u8]) -> Result<usize, WireError> {
        let count = u8::try_from(ranges.len())
            .ok()
            .filter(|&c| usize::from(c) <= MAX_REQ_RANGES)
            .ok_or(WireError::Unexpected("too many ranges"))?;
        let mut w = Writer::new(out);
        w.ensure(REQ_FIXED + 16 * ranges.len())?;
        w.put_u8(T_REQ)?;
        w.put_slice(root)?;
        w.put_u8(count)?;
        for s in ranges {
            w.put_u64(s.off)?;
            w.put_u64(s.len)?;
        }
        Ok(w.written().len())
    }
}

/// A GROUP header: where the group sits and how long its proof and data are.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GroupHeader {
    /// The byte offset of the group in the value.
    pub off: u64,
    /// The data length in bytes.
    pub len: u32,
    /// The proof length in bytes; a whole number of 64-byte pairs.
    pub plen: u16,
    /// Whether the proof continues the previous group of the range.
    pub follows: bool,
}

impl GroupHeader {
    /// Parse the header at the start of `buf`.
    ///
    /// # Errors
    /// [`WireError::Truncated`] if `buf` is under 16 bytes, [`WireError::Unexpected`] for a wrong type, a flag other
    /// than 0 or 1, a proof that is not whole pairs or an empty group.
    pub fn parse(buf: &[u8]) -> Result<Self, WireError> {
        let h = buf.first_chunk::<GROUP_HDR>().ok_or(WireError::Truncated {
            needed: GROUP_HDR.saturating_sub(buf.len()),
        })?;
        let mut r = Reader::new(h);
        if r.read_u8()? != T_GROUP {
            return Err(WireError::Unexpected("not a group"));
        }
        let off = r.read_u64()?;
        let len = r.read_u32()?;
        let plen = r.read_u16()?;
        let follows = match r.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err(WireError::Unexpected("bad follows flag")),
        };
        if len == 0 || usize::from(plen) % PARENT_LEN != 0 {
            return Err(WireError::Unexpected("bad group lengths"));
        }
        Ok(Self {
            off,
            len,
            plen,
            follows,
        })
    }

    /// The 16 header bytes.
    pub fn encode(&self) -> [u8; GROUP_HDR] {
        let mut out = [0u8; GROUP_HDR];
        let mut w = Writer::new(&mut out);
        // The buffer is exactly GROUP_HDR bytes, so these writes cannot fail.
        let _ = w.put_u8(T_GROUP);
        let _ = w.put_u64(self.off);
        let _ = w.put_u32(self.len);
        let _ = w.put_u16(self.plen);
        let _ = w.put_u8(u8::from(self.follows));
        out
    }
}

/// A parsed PROOF extension frame body, borrowing its proof.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofFrame<'a> {
    /// The stream the proof is for.
    pub sid: u64,
    /// The group-size log the proof was made with.
    pub glog: u8,
    /// The value offset of the first group covered.
    pub start: u64,
    /// The bytes of the value covered.
    pub wn: u32,
    /// The value length.
    pub ln: u64,
    /// The parent pairs of the range, in pre-order.
    pub proof: &'a [u8],
}

impl<'a> ProofFrame<'a> {
    /// Parse a PROOF body.
    ///
    /// # Errors
    /// [`WireError`] for a truncated body, a proof that is not whole pairs or is over the largest size.
    pub fn parse(body: &'a [u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(body);
        let sid = r.read_varint()?;
        let glog = r.read_u8()?;
        let start = r.read_u64()?;
        let wn = r.read_u32()?;
        let ln = r.read_u64()?;
        let proof = r.read_bytes(r.remaining())?;
        if proof.len() % PARENT_LEN != 0 || proof.len() > WT_PMAX {
            return Err(WireError::Unexpected("bad proof length"));
        }
        Ok(Self {
            sid,
            glog,
            start,
            wn,
            ln,
            proof,
        })
    }

    /// Write the fixed part of a PROOF body (everything before the proof) into `out`; returns its length.
    ///
    /// # Errors
    /// [`WireError`] if `out` is short or `sid` does not fit a varint; `out` is untouched then.
    pub fn write_head(sid: u64, glog: u8, start: u64, wn: u32, ln: u64, out: &mut [u8]) -> Result<usize, WireError> {
        put_whole(out, |w| {
            w.put_varint(sid)?;
            w.put_u8(glog)?;
            w.put_u64(start)?;
            w.put_u32(wn)?;
            w.put_u64(ln)
        })
    }
}

/// A parsed `PROOF_REQ` extension frame body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProofReq {
    /// The stream the proofs are asked for.
    pub sid: u64,
    /// The value offset to start from.
    pub from: u64,
    /// The value offset to cover up to.
    pub upto: u64,
}

impl ProofReq {
    /// Parse a `PROOF_REQ` body, which must be exactly its fields.
    ///
    /// # Errors
    /// [`WireError`] for a truncated body or trailing bytes.
    pub fn parse(body: &[u8]) -> Result<Self, WireError> {
        let mut r = Reader::new(body);
        let sid = r.read_varint()?;
        let from = r.read_u64()?;
        let upto = r.read_u64()?;
        if !r.is_empty() {
            return Err(WireError::Unexpected("trailing bytes"));
        }
        Ok(Self { sid, from, upto })
    }

    /// Encode the body into `out`; returns the bytes written.
    ///
    /// # Errors
    /// [`WireError`] if `out` is short or `sid` does not fit a varint; `out` is untouched then.
    pub fn encode(&self, out: &mut [u8]) -> Result<usize, WireError> {
        put_whole(out, |w| {
            w.put_varint(self.sid)?;
            w.put_u64(self.from)?;
            w.put_u64(self.upto)
        })
    }
}

/// Build a frame head of at most [`PROOF_HEAD_MAX`] bytes with `fill`, then copy it to `out` whole: `out` is untouched when
/// `fill` fails or the head does not fit.
fn put_whole(out: &mut [u8], fill: impl FnOnce(&mut Writer<'_>) -> Result<(), WireError>) -> Result<usize, WireError> {
    let mut head = [0u8; PROOF_HEAD_MAX];
    let mut w = Writer::new(&mut head);
    fill(&mut w)?;
    let bytes = w.written();
    Writer::new(out).put_slice(bytes)?;
    Ok(bytes.len())
}

/// A big-endian `u64` from the first 8 bytes of `b`; 0 if `b` is shorter (callers pass exact slices).
fn be64(b: &[u8]) -> u64 {
    b.first_chunk::<8>().map_or(0, |a| u64::from_be_bytes(*a))
}
