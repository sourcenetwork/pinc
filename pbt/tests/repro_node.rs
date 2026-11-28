//! Reproducing tests of bugs the `node_*` properties found in `pinc-node`. Each fails on the unmodified code.

mod node_harness;

use std::collections::BTreeSet;

use node_harness::{Peer, Seen, build, exchange, node_id, node_opens, peer_opens, peer_report};
use pinc_reconcile::{Initiator, Limits, MemIndex, Responder};

/// Item `i` of `len` bytes: distinct by its first two bytes.
fn item(i: usize, len: usize) -> Vec<u8> {
    let mut v = (i as u16).to_be_bytes().to_vec();
    v.extend((2..len).map(|j| (j as u8).wrapping_mul(37) ^ (i as u8)));
    v
}

/// The smallest message limit for items of 16 bytes (`Limits::min_message`, 154 bytes).
fn limits() -> Limits {
    let base = Limits {
        max_item: 16,
        ..Limits::default()
    };
    Limits {
        max_message: base.min_message(),
        ..base
    }
}

/// The node refuses an honest peer's first message when the set reference is long: an initiator that holds 17 items
/// of 16 bytes and names a set of 16 bytes, at the smallest message limit, writes a first message body of 169 bytes,
/// and the node answering it resets the stream with the protocol error.
///
/// Expected: `pinc_reconcile::Limits::max_message`: "A difference of any size is spread over as many messages as it
/// needs, as long as the limit is at least `min_message`", and the pinc-node crate doc: "A round larger than one
/// message is spread over as many messages as it needs, each within `Limits::max_message`, so a valid difference
/// never fails for its size". Both sides use the same limits; the peer's report should name its 17 items.
///
/// Actual: the node resets the round's stream with code 1 (protocol) on the first message.
///
/// Suspected fault: the node reads a message body as at most `limits.max_message` (`next_message`,
/// crates/pinc-node/src/reconcile.rs:139-148, called from `resp_readable` at about line 630), while the library bounds
/// only the parts by the limit and adds the set reference, the item count and the part count on top (`Core::finish`,
/// crates/pinc-reconcile/src/core.rs:498-511); the library's own reader allows `frame_cap` = the limit plus two items
/// plus 36 bytes (core.rs:481-485). The two places that must agree on the longest body do not call one function.
///
/// Who: any honest peer with the same `SetsApp::limits`, whenever the set reference plus the framing pushes a full
/// message over the limit; the round never completes, however often it is retried.
#[test]
fn an_honest_first_message_with_a_long_set_reference_is_refused_by_the_node() {
    let set_ref = [0x5a; 16];
    let peer_items: Vec<Vec<u8>> = (0..17).map(|i| item(i, 16)).collect();
    let idx = MemIndex::from_sorted(peer_items.iter().map(Vec::as_slice)).unwrap();
    let mut node = build(&set_ref, &[], limits());
    let mut seen = Seen::default();
    let mut init = Initiator::new(limits());
    let (s, x) = peer_opens(&mut node, node_id(0x22), &mut init, &idx, &set_ref, &mut seen).unwrap();
    let mut peer = Peer::Init(init);
    exchange(&mut node, s, x, &mut peer, &idx, &mut seen);
    eprintln!("max_message {}, the peer's longest body {}", limits().max_message, seen.peer_body);
    assert!(seen.node_reset.is_none(), "the node reset the round's stream with code {:?}", seen.node_reset);
    let Peer::Init(init) = &peer else { return };
    let want: BTreeSet<Vec<u8>> = peer_items.into_iter().collect();
    assert_eq!(peer_report(init), Some((BTreeSet::new(), want)));
}

/// A round the node starts fails when the honest responder's reply is one byte over the message limit: items of 16
/// bytes, a set reference of 1 byte, the smallest message limit, 55 items of which the node holds those with
/// `i % 3 != 2` and the peer those with `i % 3 != 1`. The responder writes a reply body of 155 bytes for a limit of 154.
///
/// Expected: as in `an_honest_first_message_with_a_long_set_reference_is_refused_by_the_node`, and `Node::sets_start`:
/// "The exact difference comes out of `Node::poll_event` as `NodeEvent::ReconcileDone`".
///
/// Actual: the node ends the round with `ReconcileFailed { reason: Protocol }`.
///
/// Suspected fault: the same pair, read from the initiator's side: `next_message` called from `round_readable`
/// (crates/pinc-node/src/reconcile.rs:528-535) refuses a body over `max_message`, which the responder's `Core::finish`
/// (crates/pinc-reconcile/src/core.rs:498-511) writes when it adds the part count to parts that fill the limit.
///
/// Who: any honest peer with the same limits, for a difference that happens to fill a reply; no attacker needed.
#[test]
fn an_honest_reply_one_byte_over_the_limit_fails_the_round_the_node_started() {
    let all: Vec<Vec<u8>> = (0..55).map(|i| item(i, 16)).collect();
    let pick = |skip: usize| -> Vec<Vec<u8>> {
        all.iter().enumerate().filter(|(i, _)| i % 3 != skip).map(|p| p.1.clone()).collect()
    };
    let (node_items, peer_items) = (pick(2), pick(1));
    let idx = MemIndex::from_sorted(peer_items.iter().map(Vec::as_slice)).unwrap();
    let mut node = build(b"s", &node_items, limits());
    let (s, x) = node_opens(&mut node, node_id(0x22), b"s").unwrap();
    let mut seen = Seen::default();
    let mut peer = Peer::Resp(Responder::new(limits()));
    exchange(&mut node, s, x, &mut peer, &idx, &mut seen);
    eprintln!(
        "max_message {}, longest bodies: node {}, peer {}",
        limits().max_message,
        seen.node_body,
        seen.peer_body
    );
    let only = |a: &[Vec<u8>], b: &[Vec<u8>]| -> BTreeSet<Vec<u8>> { a.iter().filter(|x| !b.contains(x)).cloned().collect() };
    let want = (only(&peer_items, &node_items), only(&node_items, &peer_items));
    assert!(matches!(seen.outcome, Some(Ok(_))), "the round ended {:?}", seen.outcome);
    assert_eq!(seen.outcome, Some(Ok(want)));
}

/// A round the node starts fails when the honest peer's reply arrives faster than the node reads it: the node holds
/// no item, the peer 40 items of 16 bytes, at the smallest message limit (154 bytes). The peer answers with the whole
/// list, in messages each within the limit, and the node reads more than twice a message at once.
///
/// Expected: as in `an_honest_reply_one_byte_over_the_limit_fails_the_round_the_node_started`: `ReconcileDone`, with
/// the peer's 40 items as `missing_here`. Nothing in the protocol asks a peer to wait between its messages, and the
/// transport hands a reader up to a 16 KiB chunk at once (pinc-transport stream/recv.rs `read_chunk`).
///
/// Actual: `ReconcileFailed { reason: Protocol }`, every message within the limit.
///
/// Suspected fault: `round_readable` (crates/pinc-node/src/reconcile.rs:520-524) drains the stream with
/// `drain_stream(.., cap * 2)`, and `drain_stream` (crates/pinc-node/src/io.rs:509-534) sets `over` as soon as the
/// readable chunk is longer than the room left, which the round takes as a protocol failure. The bound is meant to
/// stop a peer from piling bytes into the node's buffer, but it leaves the excess unread on the stream instead of
/// failing; reading at most the room and the rest after the messages in hand are handled would keep the bound and the
/// round. `resp_readable` (about line 623) has the same pattern for the responder side.
///
/// Who: any honest peer with the same limits whose messages arrive together (one datagram carries several of them).
/// The node's own responder writes a cold list back to back too (reconcile.rs:667-676), so two nodes of this library
/// with a small limit fail the same way.
#[test]
fn an_honest_reply_that_arrives_at_once_fails_the_round_the_node_started() {
    let peer_items: Vec<Vec<u8>> = (0..40).map(|i| item(i, 16)).collect();
    let idx = MemIndex::from_sorted(peer_items.iter().map(Vec::as_slice)).unwrap();
    let mut node = build(b"s", &[], limits());
    let (s, x) = node_opens(&mut node, node_id(0x22), b"s").unwrap();
    let mut seen = Seen::default();
    let mut peer = Peer::Resp(Responder::new(limits()));
    exchange(&mut node, s, x, &mut peer, &idx, &mut seen);
    eprintln!(
        "max_message {}, longest bodies: node {}, peer {}",
        limits().max_message,
        seen.node_body,
        seen.peer_body
    );
    assert!(seen.peer_body <= limits().max_message, "the peer wrote a message over the limit: not this bug");
    assert!(matches!(seen.outcome, Some(Ok(_))), "the round ended {:?}", seen.outcome);
    assert_eq!(seen.outcome, Some(Ok((peer_items.into_iter().collect(), BTreeSet::new()))));
}
