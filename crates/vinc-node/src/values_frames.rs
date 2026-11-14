//! The pieces of the values layer that read and rewrite what the endpoint holds: the runs of a stream stored beyond a
//! hole, what of them is new since the last look, and the stream id at the head of a range-proof frame.
//!
//! A frame names a stream by the endpoint's stream id, which both ends share; the layer names it by its own handle,
//! local to the node. The head of the body is rewritten between the two.
//!
//! Invariants: nothing here allocates; a run list holds at most [`AHEAD_RUNS`] runs and what does not fit is left to
//! the in-order parse.

use vinc_core::SessionId;
use vinc_transport::stream::StreamId;
use vinc_wire::varint;

use crate::ep::Ep;

/// The runs of bytes beyond a hole that are remembered per stream, so only what is new is reported.
pub(crate) const AHEAD_RUNS: usize = 8;
/// The widest extension body (a range proof) once its stream id is replaced.
pub(crate) const EXT_MAX: usize = vinc_core::EXT_BODY_MAX + 16;

/// The stream id at the head of an extension body (a range proof or its request).
pub(crate) fn head_sid(body: &[u8]) -> Option<u64> {
    varint::decode(body).ok().map(|(v, _)| v)
}

/// `body` with the stream id at its head replaced by `sid`, written to `out`: the length. The layer names a stream by
/// its own handle and the wire by the endpoint's stream id, which both ends share.
pub(crate) fn with_sid(body: &[u8], sid: u64, out: &mut [u8; EXT_MAX]) -> Option<usize> {
    let (_, used) = varint::decode(body).ok()?;
    let head = varint::encode(sid, out).ok()?;
    let rest = body.get(used..)?;
    out.get_mut(head..head + rest.len())?.copy_from_slice(rest);
    Some(head + rest.len())
}

/// The head of a range-proof body as the trace test of the proofs reads it: the same functions on a buffer of
/// `EXT_MAX` bytes, with their results in public types.
#[cfg(feature = "trace")]
pub mod probe {
    use super::{EXT_MAX, head_sid, with_sid};

    /// The size of the buffer `with_sid` writes to.
    pub const BUF: usize = EXT_MAX;

    /// `head_sid`.
    pub fn head(body: &[u8]) -> Option<u64> {
        head_sid(body)
    }

    /// `with_sid` into a fresh buffer: the bytes written.
    pub fn with(body: &[u8], sid: u64) -> Option<alloc::vec::Vec<u8>> {
        let mut out = [0u8; EXT_MAX];
        let n = with_sid(body, sid, &mut out)?;
        out.get(..n).map(<[u8]>::to_vec)
    }
}

/// The contiguous end of the stored bytes of a stream from `base`, and the runs stored beyond the first hole (at most
/// [`AHEAD_RUNS`]), with how many.
pub(crate) fn stored_runs<E: Ep>(
    ep: &E,
    session: SessionId,
    stream: StreamId,
    base: u64,
) -> (u64, [(u64, u64); AHEAD_RUNS], usize) {
    let (mut contig, mut from, mut n) = (base, base, 0);
    let mut runs = [(0u64, 0u64); AHEAD_RUNS];
    for _ in 0..=AHEAD_RUNS {
        let Some(r) = ep.stored_after(session, stream, from) else {
            break;
        };
        if r.start <= contig {
            contig = r.end;
        } else if let Some(d) = runs.get_mut(n) {
            *d = (r.start, r.end);
            n += 1;
        }
        from = r.end;
    }
    (contig, runs, n)
}

/// The parts of `now` that `old` does not cover, written to `out`: how many. Both are ascending and disjoint; a part
/// that does not fit `out` is left for the in-order parse.
pub(crate) fn new_parts(now: &[(u64, u64)], old: &[(u64, u64); AHEAD_RUNS], out: &mut [(u64, u64)]) -> usize {
    let mut k = 0;
    for (a, b) in now {
        let mut cur = *a;
        for (oa, ob) in old.iter().filter(|(oa, ob)| ob > oa) {
            if *ob <= cur {
                continue;
            }
            if oa >= b {
                break;
            }
            if *oa > cur
                && let Some(d) = out.get_mut(k)
            {
                *d = (cur, *oa);
                k += 1;
            }
            cur = cur.max(*ob);
        }
        if cur < *b
            && let Some(d) = out.get_mut(k)
        {
            *d = (cur, *b);
            k += 1;
        }
    }
    k
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing)]
mod tests {
    use super::*;

    #[test]
    fn the_stream_id_at_the_head_of_a_body_is_replaced_whatever_its_width() {
        let mut out = [0u8; EXT_MAX];
        for (old, new) in [
            (3u64, 4_000_000_000u64),
            (4_000_000_000, 3),
            (63, 64),
            (u64::from(u32::MAX), 1 << 40),
        ] {
            let mut body = [0u8; 12];
            let n = varint::encode(old, &mut body).unwrap();
            body[n..n + 5].copy_from_slice(b"hello");
            let body = &body[..n + 5];
            assert_eq!(head_sid(body), Some(old));
            let len = with_sid(body, new, &mut out).unwrap();
            assert_eq!(head_sid(&out[..len]), Some(new));
            assert!(out[..len].ends_with(b"hello"));
        }
        assert_eq!(head_sid(&[]), None);
        assert_eq!(with_sid(&[], 1, &mut out), None);
    }

    #[test]
    fn only_what_the_last_look_did_not_cover_is_new() {
        let mut old = [(0u64, 0u64); AHEAD_RUNS];
        old[0] = (100, 200);
        old[1] = (300, 400);
        let mut out = [(0u64, 0u64); 16];
        // The first run grew at both ends, the second is unchanged, a third is wholly new.
        let n = new_parts(&[(50, 250), (300, 400), (500, 600)], &old, &mut out);
        assert_eq!(&out[..n], [(50, 100), (200, 250), (500, 600)]);
        // Nothing changed: nothing is new.
        let n = new_parts(&[(100, 200), (300, 400)], &old, &mut out);
        assert_eq!(n, 0);
        // A run that bridges two old ones reports the gap between them only.
        let n = new_parts(&[(100, 400)], &old, &mut out);
        assert_eq!(&out[..n], [(200, 300)]);
        // A short output keeps what fits.
        let mut small = [(0u64, 0u64); 1];
        assert_eq!(new_parts(&[(0, 10), (20, 30)], &[(0, 0); AHEAD_RUNS], &mut small), 1);
    }
}
