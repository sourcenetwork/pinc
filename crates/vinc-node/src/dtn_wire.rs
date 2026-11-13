//! The frames of a bundle transfer on a delay-tolerant stream.
//!
//! One bidirectional stream carries one transfer: the holder opens it and writes OFFER; the receiver answers with WANT
//! for the symbols it lacks; the holder answers each WANT with DATA, whose proof stream the receiver checks against
//! the signed root; when the bundle is whole and custody is accepted the receiver writes ACK, or REFUSE if it cannot
//! take the bundle. Every frame is `type(1) | length(4, big endian) | body`.
//!
//! Invariants: a frame announcing a body over [`BODY_MAX`] is a protocol break; a parser takes a frame only when it
//! is whole and never reads past it.

use alloc::vec::Vec;

/// The holder offers a bundle: `copies(2) | offer(8) | signed head`.
pub(crate) const OFFER: u8 = 1;
/// The receiver asks for symbols: `first(8) | end(8)`.
pub(crate) const WANT: u8 = 2;
/// The holder sends symbols: `first(8) | end(8) | proof stream`.
pub(crate) const DATA: u8 = 3;
/// The receiver took custody, or the destination received the bundle: an encoded custody acknowledgement.
pub(crate) const ACK: u8 = 4;
/// The receiver cannot take the bundle: `reason(1)`.
pub(crate) const REFUSE: u8 = 5;

/// The longest frame body: a data run, its proof and a few hundred bytes of framing.
pub(crate) const BODY_MAX: usize = 1 << 20;
/// The bytes of a frame header.
pub(crate) const HDR: usize = 5;

/// Why a receiver refused a bundle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Refusal {
    /// The head or the offer is malformed, or its signature does not verify.
    Malformed = 1,
    /// The bundle is expired.
    Expired = 2,
    /// The store has no room without evicting custody.
    NoRoom = 3,
    /// The symbols sent did not verify against the root.
    BadProof = 4,
    /// The decoded bundle does not hash to the root.
    Inconsistent = 5,
    /// The bundle is for this node and this node cannot open it.
    CannotOpen = 6,
    /// The node holds no key to sign an acknowledgement with.
    NoSigner = 7,
    /// A table of this node is full.
    Busy = 8,
}

impl Refusal {
    /// The refusal that reports a feed error other than a failed proof (which costs only the symbol) to the holder:
    /// an expired bundle is [`Refusal::Expired`], anything else is [`Refusal::BadProof`].
    pub(crate) fn for_feed(e: vinc_dtn::DtnError) -> Self {
        match e {
            vinc_dtn::DtnError::Expired => Self::Expired,
            _ => Self::BadProof,
        }
    }
}

/// Start a frame of type `ty` in `out` (cleared first); [`finish`] writes its length.
pub(crate) fn start(out: &mut Vec<u8>, ty: u8) {
    out.clear();
    out.push(ty);
    out.extend_from_slice(&[0; 4]);
}

/// Write the body length into the header of the frame in `out`.
pub(crate) fn finish(out: &mut [u8]) {
    let n = u32::try_from(out.len().saturating_sub(HDR)).unwrap_or(u32::MAX);
    if let Some(len) = out.get_mut(1..HDR) {
        len.copy_from_slice(&n.to_be_bytes());
    }
}

/// The frame at the front of `inb`: its type and total length, `None` if it is not whole yet.
///
/// # Errors
/// `()` if the frame announces a body over [`BODY_MAX`].
#[allow(clippy::many_single_char_names, reason = "the five header bytes")]
pub(crate) fn next(inb: &[u8]) -> Result<Option<(u8, usize)>, ()> {
    let Some(head) = inb.first_chunk::<HDR>() else {
        return Ok(None);
    };
    let [ty, a, b, c, d] = *head;
    let n = usize::try_from(u32::from_be_bytes([a, b, c, d])).map_err(|_| ())?;
    if n > BODY_MAX {
        return Err(());
    }
    Ok((inb.len() >= HDR + n).then_some((ty, HDR + n)))
}

/// A big-endian `u64` at the front of `b`, and the rest.
pub(crate) fn take_u64(b: &[u8]) -> Option<(u64, &[u8])> {
    let (head, rest) = b.split_first_chunk::<8>()?;
    Some((u64::from_be_bytes(*head), rest))
}

/// A big-endian `u16` at the front of `b`, and the rest.
pub(crate) fn take_u16(b: &[u8]) -> Option<(u16, &[u8])> {
    let (head, rest) = b.split_first_chunk::<2>()?;
    Some((u16::from_be_bytes(*head), rest))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_frame_round_trips_and_waits_for_its_end() {
        let mut out = Vec::new();
        start(&mut out, WANT);
        out.extend_from_slice(&7u64.to_be_bytes());
        out.extend_from_slice(&9u64.to_be_bytes());
        finish(&mut out);
        assert_eq!(next(&out), Ok(Some((WANT, out.len()))));
        assert_eq!(next(out.get(..out.len() - 1).unwrap_or_default()), Ok(None));
        let body = out.get(HDR..).unwrap_or_default();
        let first = take_u64(body).map(|(a, rest)| (a, take_u64(rest).map(|x| x.0)));
        assert_eq!(first, Some((7, Some(9))));
    }

    #[test]
    fn a_frame_over_the_cap_is_a_break() {
        let mut out = alloc::vec![DATA];
        out.extend_from_slice(&u32::try_from(BODY_MAX + 1).unwrap_or(u32::MAX).to_be_bytes());
        assert_eq!(next(&out), Err(()));
    }
}
