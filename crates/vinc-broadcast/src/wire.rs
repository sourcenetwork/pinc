//! The frames and the message head of the topic broadcast.
//!
//! A frame is `len32 | type | topic_len | topic | rest`, the hub stream codec of `vinc-membership`. A message frame
//! (PUB, FAN, FANP, MSG, `MEMBER_PUSH`) carries `head | body` as its rest. The head is
//! `mid8 origin32 alg1 [public_key] signature isb1 blen4 ts12`: the public key is present for every algorithm whose
//! node id is not the key itself, and `ts` is a hybrid logical clock (`wall8 counter4`).
//!
//! Invariants: [`Head::parse`] never panics and never reads outside its input; `blen` must equal the number of body
//! bytes that follow, so a frame cannot carry a body its head does not describe.

use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN};
use vinc_membership::NodeId;
use vinc_wire::Reader;
use vinc_wire::hlc::Hlc;

/// Frame type numbers. The membership types (1 to 4, 12 to 14) are not repeated here.
pub mod ty {
    /// A publisher hands a message to a hub; the hub mirrors it to the other hubs.
    pub const PUB: u8 = 5;
    /// A hub acknowledges a PUB or FANP: the message is in its log.
    pub const PACK: u8 = 6;
    /// A message pushed to a subscriber, or mirrored between hubs.
    pub const MSG: u8 = 7;
    /// Subscribe to a topic from a point in time.
    pub const SUB: u8 = 8;
    /// Unsubscribe.
    pub const UNSUB: u8 = 9;
    /// The ids a node holds.
    pub const HAVE: u8 = 10;
    /// Ask for the messages behind some ids.
    pub const GET: u8 = 11;
    /// The replay floor, carried by the membership hub stream.
    pub use vinc_membership::codec::ty::FLOOR;
    /// A publish handed to a non-primary hub with no mirroring.
    pub const FAN: u8 = 15;
    /// A publish handed to the primary hub with no mirroring (acknowledged).
    pub const FANP: u8 = 16;
    /// A message pushed straight to a subscriber over a member session.
    pub const MEMBER_PUSH: u8 = 17;
    /// The subscribers of a topic, replicated by the hubs, `version` being the hub's incarnation (8 bytes) and the
    /// list's number (4): `0 | version | count | ids` (the whole list), `1 | version | count | added ids | count |
    /// removed ids` (the change from the version before), or `2` from a member (send me the whole list).
    pub const SUBS: u8 = 18;
    /// A hub tells a member its held subscriptions of a topic are live again.
    pub const RESTORED: u8 = 19;
    /// A member's adjacency record: the peers it holds sessions with, signed, sent to the hubs and mirrored between
    /// them. The topic is empty.
    pub const ADJ: u8 = 20;
}

/// The length of a message id.
pub const MID_LEN: usize = 8;
/// The length of the encoded timestamp.
pub const TS_LEN: usize = 12;
/// The longest head: a hybrid key and signature.
pub const MAX_HEAD: usize = MID_LEN + 32 + 1 + MAX_PUBLIC_KEY_LEN + MAX_SIGNATURE_LEN + 1 + 4 + TS_LEN;

/// Bytes are not a well-formed head or frame, named by the reason.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Malformed(pub &'static str);

/// A frame would not fit its buffer or the format.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TooLong;

impl core::fmt::Display for Malformed {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "malformed message: {}", self.0)
    }
}

impl core::error::Error for Malformed {}

impl core::fmt::Display for TooLong {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("the frame is larger than its buffer or the format allows")
    }
}

impl core::error::Error for TooLong {}

impl From<vinc_wire::WireError> for Malformed {
    fn from(_: vinc_wire::WireError) -> Self {
        Self("message cut short")
    }
}

// vertexia: every message of a non-Ed25519 origin carries its public key (up to 1984 bytes); a per-peer key cache
// keyed by node id would drop it from all but the first.
/// The signed head of a message, borrowed from the frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Head<'a> {
    /// The message id.
    pub mid: [u8; MID_LEN],
    /// The origin: its node id.
    pub origin: &'a NodeId,
    /// The origin's signature algorithm.
    pub alg: IdentityAlg,
    /// The origin's public key; empty for Ed25519, whose node id is the key.
    pub pk: &'a [u8],
    /// The signature over the topic, the id and the hash of the body.
    pub sig: &'a [u8],
    /// The body is bytes rather than a stream slice.
    pub isb: bool,
    /// The origin's timestamp.
    pub ts: Hlc,
}

impl<'a> Head<'a> {
    /// Parse the head at the start of `rest` and return it with the body that follows.
    ///
    /// # Errors
    /// [`Malformed`] for an unknown algorithm, a reserved flag, a body whose length differs from `blen`. The size limit
    /// is the node's configuration, checked by the caller.
    pub fn parse(rest: &'a [u8]) -> Result<(Self, &'a [u8]), Malformed> {
        let mut r = Reader::new(rest);
        let mid = r.read_array::<MID_LEN>()?;
        let origin = <&NodeId>::try_from(r.read_bytes(32)?).map_err(|_| Malformed("origin"))?;
        let alg = IdentityAlg::from_tag(r.read_u8()?).ok_or(Malformed("algorithm"))?;
        let pk = if alg == IdentityAlg::Ed25519 {
            &[][..]
        } else {
            r.read_bytes(alg.public_key_len())?
        };
        let sig = r.read_bytes(alg.signature_len())?;
        let isb = match r.read_u8()? {
            0 => false,
            1 => true,
            _ => return Err(Malformed("body flag")),
        };
        let blen = usize::try_from(r.read_u32()?).map_err(|_| Malformed("body length"))?;
        let ts = Hlc::new(r.read_u64()?, r.read_u32()?);
        let n = r.remaining();
        let body = r.read_bytes(n)?;
        if body.len() != blen {
            return Err(Malformed("body length"));
        }
        Ok((
            Self {
                mid,
                origin,
                alg,
                pk,
                sig,
                isb,
                ts,
            },
            body,
        ))
    }

    /// The encoded length of this head.
    pub fn len(&self) -> usize {
        MID_LEN + 32 + 1 + self.pk.len() + self.sig.len() + 1 + 4 + TS_LEN
    }

    /// Whether the head is empty (it never is).
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Append the head, with `blen` the length of the body that follows, to `out`.
    pub fn write(&self, blen: u32, out: &mut impl Extend<u8>) {
        out.extend(self.mid);
        out.extend(*self.origin);
        out.extend([self.alg.tag()]);
        out.extend(self.pk.iter().copied());
        out.extend(self.sig.iter().copied());
        out.extend([u8::from(self.isb)]);
        out.extend(blen.to_be_bytes());
        out.extend(self.ts.wall.to_be_bytes());
        out.extend(self.ts.counter.to_be_bytes());
    }
}

/// Encode the timestamp the way the head and the floors carry it.
pub fn put_ts(out: &mut impl Extend<u8>, ts: Hlc) {
    out.extend(ts.wall.to_be_bytes());
    out.extend(ts.counter.to_be_bytes());
}

/// Decode a timestamp from the first [`TS_LEN`] bytes of `b`.
pub fn get_ts(b: &[u8]) -> Option<Hlc> {
    let mut r = Reader::new(b);
    Some(Hlc::new(r.read_u64().ok()?, r.read_u32().ok()?))
}

/// Read a big-endian `u64` from the start of `b`.
pub fn get_u64(b: &[u8]) -> Option<u64> {
    Reader::new(b).read_u64().ok()
}

#[cfg(feature = "alloc")]
/// Build `len32 | ty | topic_len | topic | parts...` in `out`, which is cleared first and never grows: a frame that
/// does not fit `out`'s capacity is refused.
///
/// # Errors
/// [`TooLong`] for a topic over 255 bytes or a frame over the capacity of `out`.
pub fn build(out: &mut alloc::vec::Vec<u8>, ty: u8, topic: &[u8], parts: &[&[u8]]) -> Result<(), TooLong> {
    let tl = u8::try_from(topic.len()).map_err(|_| TooLong)?;
    let body = 2 + topic.len() + parts.iter().map(|p| p.len()).sum::<usize>();
    if 4 + body > out.capacity() || topic.len() > crate::consts::MAX_TOPIC {
        return Err(TooLong);
    }
    out.clear();
    out.extend_from_slice(&u32::try_from(body).map_err(|_| TooLong)?.to_be_bytes());
    out.push(ty);
    out.push(tl);
    out.extend_from_slice(topic);
    for p in parts {
        out.extend_from_slice(p);
    }
    Ok(())
}
