//! The registry of extension frame types: every type at or above [`EXTENSION_BASE`] that a
//! crate of this library sends, in one place.
//!
//! Each assigned type or range is a constant here and an entry of [`ASSIGNED`]; a crate that sends or matches an
//! extension frame names the constant and never writes the number. A new type is taken by adding a constant and an
//! entry. Invariant: no two entries overlap and none lies below the base, checked when the crate compiles, so a
//! duplicate or a stray value cannot be built.

use super::EXTENSION_BASE;

/// A sub-session open: the parent session carries the ids of a session opened over it.
pub const SUB_SESSION_OPEN: u64 = 0x40;
/// The first of three types the transport tests use for opaque payloads; no node sends them.
pub const TEST_FIRST: u64 = 0x41;
/// The last type of the transport tests' range.
pub const TEST_LAST: u64 = 0x43;
/// `REACH_OUT`, a request to a peer to send punching candidates toward an address (hole punching in `vinc-connect`).
/// Reserved: the connect crate takes this type when it implements the frame.
pub const REACH_OUT: u64 = 0x44;
/// A range-proof request for a value range.
pub const PROOF_REQ: u64 = 0x49;
/// A range proof answering a [`PROOF_REQ`].
pub const PROOF: u64 = 0x4f;

/// Every assigned type as an inclusive range `(first, last)`; a single type has `first == last`.
pub const ASSIGNED: [(u64, u64); 5] = [
    (SUB_SESSION_OPEN, SUB_SESSION_OPEN),
    (TEST_FIRST, TEST_LAST),
    (REACH_OUT, REACH_OUT),
    (PROOF_REQ, PROOF_REQ),
    (PROOF, PROOF),
];

/// Whether the ranges are well formed, at or above the base, and pairwise disjoint.
#[allow(clippy::indexing_slicing, reason = "indexes are bounded by the loop conditions")]
const fn unique(r: &[(u64, u64)]) -> bool {
    let mut i = 0;
    while i < r.len() {
        if r[i].0 > r[i].1 || r[i].0 < EXTENSION_BASE {
            return false;
        }
        let mut j = i + 1;
        while j < r.len() {
            if r[i].0 <= r[j].1 && r[j].0 <= r[i].1 {
                return false;
            }
            j += 1;
        }
        i += 1;
    }
    true
}

const _: () = assert!(
    unique(&ASSIGNED),
    "extension frame types overlap or fall below the base"
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_check_rejects_a_duplicate_an_overlap_and_a_stray_type() {
        assert!(unique(&ASSIGNED));
        assert!(!unique(&[(0x50, 0x50), (0x50, 0x50)]));
        assert!(!unique(&[(0x50, 0x55), (0x55, 0x58)]));
        assert!(!unique(&[(0x50, 0x58), (0x52, 0x53)]));
        assert!(!unique(&[(0x3f, 0x3f)]));
        assert!(!unique(&[(0x52, 0x51)]));
        assert!(unique(&[(0x50, 0x54), (0x55, 0x55)]));
    }
}
