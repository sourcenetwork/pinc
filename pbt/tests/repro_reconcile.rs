//! Reproductions of `pinc-reconcile` bugs found by the properties of `reconcile_session.rs`. Each test fails on the
//! unmodified code.

#![allow(clippy::unwrap_used, clippy::indexing_slicing)]

use pinc_reconcile::wire::{put_bound, put_parts, put_varint};
use pinc_reconcile::{Initiator, Limits, MemIndex, Step};

/// A framed responder message of item parts (`tag | lo | [hi] | venc(n) items`), each with an infinite upper bound.
fn items_message(parts: &[(&[u8], &[&[u8]])]) -> Vec<u8> {
    let mut body = Vec::new();
    put_parts(&mut body, parts.len(), false).unwrap();
    let mut last = Vec::new();
    for (lo, items) in parts {
        body.push(3 | 0x80); // tag::FULL | tag::INF
        put_bound(&mut body, &mut last, lo).unwrap();
        put_varint(&mut body, items.len()).unwrap();
        for it in *items {
            put_varint(&mut body, it.len()).unwrap();
            body.extend_from_slice(it);
        }
    }
    let n = body.len();
    let mut m = vec![(n >> 16) as u8, (n >> 8) as u8, n as u8];
    m.extend_from_slice(&body);
    m
}

/// The initiator over the 40 one-byte items `[0]..[39]`: more than one leaf, so its first message is a split and it
/// sends no leaf (no final check follows).
fn started() -> (Initiator, MemIndex) {
    let items: Vec<[u8; 1]> = (0u8..40).map(|i| [i]).collect();
    let a = MemIndex::from_sorted(items.iter().map(<[u8; 1]>::as_slice)).unwrap();
    let mut init = Initiator::new(Limits::default());
    let mut out = Vec::new();
    init.start(&a, b"set", &mut out).unwrap();
    (init, a)
}

/// Expected: `Report::missing_here` is "The items the peer has and the initiator lacks"; the crate says "The
/// initiator learns the exact difference" and "a finished session is exact". Whatever set the peer holds, an item
/// the initiator holds is never in `missing_here`.
///
/// Actual: one well-formed responder message, an items part for the range `[20], +inf)` that lists the item `[0]`,
/// ends the session (`Step::Last`) with a report whose `missing_here` is `[[0]]`, an item the initiator holds, and
/// whose `missing_there` is `[20]..[39]`. No set of the peer has that difference with the initiator's set.
///
/// Suspected fault: `crates/pinc-reconcile/src/core.rs:848-855` (the initiator's `tag::FULL | tag::COLD` arm) merges
/// the peer's items with its own items of `a..b` without checking that they lie in the part's range `[lo, hi)`, so
/// an item below `lo` sorts before all of the initiator's items of the range and is pushed as `Theirs`. The same
/// holds for a reply's extras (`core.rs:883-886`, pushed to `here` unchecked). The final check does not catch it:
/// it runs only when the initiator itself sent a leaf (`session.rs`, `close`, `core.leafed`), and when it does run,
/// the verdict comes from the same peer.
///
/// Who can trigger it: the peer of a reconcile session (an authenticated member that answers as the responder).
#[test]
fn a_responder_item_outside_its_part_range_is_reported_missing_although_held() {
    let (mut init, a) = started();
    let mut out = Vec::new();
    let step = init.handle(&a, &items_message(&[(&[20], &[&[0]])]), &mut out).unwrap();
    assert_eq!(step, Step::Last);
    let rep = init.report().expect("the session finished");
    let here: Vec<&[u8]> = rep.missing_here().collect();
    assert!(
        !here.contains(&&[0u8][..]),
        "missing_here lists [0], which the initiator holds: {here:?}"
    );
}

/// Expected: as above; also `Report::here_count` is "How many items `missing_here` yields" of a difference, a set,
/// so no item is listed twice.
///
/// Actual: one responder message with two items parts over the same range `[], +inf)`, each listing the item `[200]`,
/// ends the session with `missing_here = [[200], [200]]` and every item of the initiator twice in `missing_there`
/// (`there_count() == 80` for a set of 40).
///
/// Suspected fault: as above (`core.rs:848-855`): nothing checks that the parts of a message cover disjoint ranges,
/// or that a range was asked about, so a range answered twice is reported twice.
///
/// Who can trigger it: the peer of a reconcile session.
#[test]
fn a_range_answered_twice_lists_every_item_of_it_twice() {
    let (mut init, a) = started();
    let mut out = Vec::new();
    let parts: [(&[u8], &[&[u8]]); 2] = [(&[], &[&[200]]), (&[], &[&[200]])];
    let step = init.handle(&a, &items_message(&parts), &mut out).unwrap();
    assert_eq!(step, Step::Last);
    let rep = init.report().expect("the session finished");
    assert_eq!(rep.here_count(), 1, "missing_here lists an item twice");
    assert_eq!(rep.there_count(), 40, "missing_there lists the initiator's items twice");
}
