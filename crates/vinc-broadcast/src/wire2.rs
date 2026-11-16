//! The version 2 message head: the fields of a statement, then the key and the signature.
//!
//! The head is `ver2 alg1 flags1 np1 origin32 inc8 seq8 wall8 counter4 blen4 parents(32 * np) [public_key]
//! signature`, big endian. The topic is in the frame, as for the version 1 head ([`crate::wire::Head`]), and the
//! body follows the head. The public key is present for every algorithm whose node id is not the key itself.
//!
//! Invariants: [`Head2::parse`] never panics and never reads outside its input; `blen` must equal the number of body
//! bytes that follow, the flags carry no reserved bit, and the parents are at most [`MAX_PARENTS`] and strictly
//! ascending, so two heads of one statement are the same bytes.

use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN};
use vinc_membership::NodeId;
use vinc_wire::Reader;
use vinc_wire::hlc::Hlc;

use crate::auth::message_id;
use crate::statement::{ContentId, FLAG_ISB, Fields, MAX_PARENTS};
use crate::wire::{MID_LEN, Malformed, TooLong};

/// The version byte.
pub const VERSION: u8 = 2;
/// The length of the head without the parents, the key and the signature.
const FIXED_LEN: usize = 1 + 1 + 1 + 1 + 32 + 8 + 8 + 8 + 4 + 4;
/// The longest head: eight parents, a hybrid key and signature.
pub const MAX_HEAD2: usize = FIXED_LEN + 32 * MAX_PARENTS + MAX_PUBLIC_KEY_LEN + MAX_SIGNATURE_LEN;

/// The version 2 head of a message, borrowed from the frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Head2<'a> {
    /// The origin's signature algorithm.
    pub alg: IdentityAlg,
    /// The body is bytes rather than a stream slice.
    pub isb: bool,
    /// The origin: its node id.
    pub origin: &'a NodeId,
    /// The origin's incarnation.
    pub incarnation: u64,
    /// The sequence number within the incarnation.
    pub seq: u64,
    /// The origin's timestamp.
    pub ts: Hlc,
    /// The content ids of the parents, strictly ascending.
    pub parents: &'a [ContentId],
    /// The origin's public key; empty for Ed25519, whose node id is the key.
    pub pk: &'a [u8],
    /// The signature over the statement's content id.
    pub sig: &'a [u8],
}

impl<'a> Head2<'a> {
    /// Parse the head at the start of `bytes` and return it with its length; the body is the rest.
    ///
    /// # Errors
    /// [`Malformed`] for another version, an unknown algorithm, a reserved flag, more than [`MAX_PARENTS`] parents
    /// or parents not strictly ascending, a cut head, or a body whose length differs from `blen`.
    pub fn parse(bytes: &'a [u8]) -> Result<(Self, usize), Malformed> {
        let mut r = Reader::new(bytes);
        if r.read_u8()? != VERSION {
            return Err(Malformed("version"));
        }
        let alg = IdentityAlg::from_tag(r.read_u8()?).ok_or(Malformed("algorithm"))?;
        let flags = r.read_u8()?;
        if flags & !FLAG_ISB != 0 {
            return Err(Malformed("flags"));
        }
        let np = usize::from(r.read_u8()?);
        if np > MAX_PARENTS {
            return Err(Malformed("parents"));
        }
        let origin = <&NodeId>::try_from(r.read_bytes(32)?).map_err(|_| Malformed("origin"))?;
        let incarnation = r.read_u64()?;
        let seq = r.read_u64()?;
        let ts = Hlc::new(r.read_u64()?, r.read_u32()?);
        let blen = usize::try_from(r.read_u32()?).map_err(|_| Malformed("body length"))?;
        let (parents, _) = r.read_bytes(32 * np)?.as_chunks::<32>();
        if !parents.windows(2).all(|w| matches!(w, [a, b] if a < b)) {
            return Err(Malformed("parents"));
        }
        let pk = if alg == IdentityAlg::Ed25519 {
            &[][..]
        } else {
            r.read_bytes(alg.public_key_len())?
        };
        let sig = r.read_bytes(alg.signature_len())?;
        let len = bytes.len() - r.remaining();
        if r.remaining() != blen {
            return Err(Malformed("body length"));
        }
        Ok((
            Self {
                alg,
                isb: flags == FLAG_ISB,
                origin,
                incarnation,
                seq,
                ts,
                parents,
                pk,
                sig,
            },
            len,
        ))
    }

    /// The encoded length of this head.
    pub fn len(&self) -> usize {
        FIXED_LEN + 32 * self.parents.len() + self.pk.len() + self.sig.len()
    }

    /// Whether the head is empty (it never is).
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Append the head, with `blen` the length of the body that follows, to `out`.
    ///
    /// # Errors
    /// [`TooLong`] for more than [`MAX_PARENTS`] parents; nothing is written then.
    pub fn write(&self, blen: u32, out: &mut impl Extend<u8>) -> Result<(), TooLong> {
        let np = u8::try_from(self.parents.len())
            .ok()
            .filter(|n| usize::from(*n) <= MAX_PARENTS)
            .ok_or(TooLong)?;
        out.extend([VERSION, self.alg.tag(), u8::from(self.isb), np]);
        out.extend(*self.origin);
        out.extend(self.incarnation.to_be_bytes());
        out.extend(self.seq.to_be_bytes());
        out.extend(self.ts.wall.to_be_bytes());
        out.extend(self.ts.counter.to_be_bytes());
        out.extend(blen.to_be_bytes());
        out.extend(self.parents.iter().flatten().copied());
        out.extend(self.pk.iter().copied());
        out.extend(self.sig.iter().copied());
        Ok(())
    }

    /// The id of this message on `topic`, the same function as the version 1 head's.
    pub fn mid(&self, topic: &[u8]) -> [u8; MID_LEN] {
        message_id(self.origin, self.incarnation, self.seq, topic)
    }

    /// The fields of this head's statement, given the topic of the frame and the hash of the body.
    pub fn statement_fields<'b>(&'b self, topic: &'b [u8], body_hash: &'b [u8; 32]) -> Fields<'b> {
        Fields {
            origin_alg: self.alg,
            origin: self.origin,
            incarnation: self.incarnation,
            seq: self.seq,
            topic,
            time: self.ts,
            flags: u8::from(self.isb),
            parents: self.parents,
            body: body_hash,
        }
    }
}

#[cfg(test)]
mod tests;
