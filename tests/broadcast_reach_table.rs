//! The hub's adjacency table (pinc#86): it changes only for a record that verifies, a full table fails closed, a
//! released member's tombstone makes room once no log holds its messages, a revoked member is forgotten, an older
//! record is taken only from its member, the components are worked out once per check, and a lost mirror between
//! hubs is repaired by the refresh.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::expect_used)]

#[path = "broadcast_common.rs"]
mod common;
#[path = "broadcast_reach_support.rs"]
mod support;

use common::{Net, SEC, ty};
use support::{T, adj, ask, capture, room, sends, session};
use pinc_broadcast::consts::{LOG_WINDOW, RECORD_TTL, REFRESH};
use pinc_broadcast::{Limits, ReachStats};
use pinc_crypto::IdentityAlg;

/// A hub and `members` members, the hub's table holding `bytes` bytes ([`room`]).
fn small(members: usize, bytes: usize) -> Net {
    let limits = Limits {
        reach_bytes: bytes,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&vec![IdentityAlg::Ed25519; members + 1], 1, SEC, limits);
    for i in 1..=members {
        net.attach(i);
    }
    net
}

/// Hub 0's table, without the count of signatures it checked: a record that fails its check is counted there.
fn table(net: &Net) -> ReachStats {
    ReachStats {
        verified: 0,
        ..net.nodes[0].t.reach_stats()
    }
}

/// Keep node `i`'s records from reaching any hub (`true`) or let them through again.
fn mute(net: &mut Net, i: usize, on: bool) {
    net.filter = None;
    if on {
        net.filter = Some(Box::new(move |from, _, b: &mut Vec<u8>| {
            !(from == i && b.get(4) == Some(&ty::ADJ))
        }));
    }
}

#[test]
fn a_record_whose_signature_fails_changes_nothing_even_with_the_table_full() {
    let mut net = small(3, room(2));
    adj(&mut net, 1, &[]);
    adj(&mut net, 2, &[]);
    // Node 2's record expires: the full table holds a tombstone, the one record room could once be made from.
    mute(&mut net, 2, true);
    net.advance(RECORD_TTL + REFRESH + SEC);
    mute(&mut net, 2, false);
    let before = table(&net);
    assert_eq!((before.records, before.live), (2, 1));

    // A newcomer's record with a flipped signature bit: nothing is evicted, refused, counted or closed.
    let mut bad = capture(&mut net, 3, &[]);
    *bad.last_mut().unwrap() ^= 1;
    ask(&mut net, 0, 3, ty::ADJ, &bad);
    assert_eq!(table(&net), before);

    // A newer record of a member that holds one, badly signed: the member keeps its old record.
    let mut newer = capture(&mut net, 1, &[2]);
    *newer.last_mut().unwrap() ^= 1;
    ask(&mut net, 0, 1, ty::ADJ, &newer);
    assert_eq!(table(&net), before);
}

#[test]
fn a_full_table_refuses_a_newcomer_and_every_node_without_a_record_is_then_alone() {
    let mut net = small(5, room(2));
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 1, 2, true);
    for i in 1..=5 {
        net.subscribe(i, T);
    }
    assert!(
        sends(&mut net, 4, 5, b"open"),
        "unscoped members hear each other while the table has room"
    );

    // Member 3 is scoped, but the table is full: its record is refused, and the table closes.
    adj(&mut net, 3, &[]);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!((stats.records, stats.refused, stats.closed), (2, 1, true));
    assert!(stats.bytes > 0, "the kept records are counted");
    assert!(
        !sends(&mut net, 3, 4, b"refused to unscoped") && !sends(&mut net, 4, 3, b"unscoped to refused"),
        "the refused member is alone, never unscoped"
    );
    assert!(!sends(&mut net, 3, 1, b"refused to a component"));
    assert!(
        !sends(&mut net, 4, 5, b"closed"),
        "a closed table counts every node without a record as alone"
    );
    assert!(
        sends(&mut net, 1, 2, b"within"),
        "a component with records keeps its reach"
    );
}

#[test]
fn a_released_member_s_tombstone_goes_once_no_log_holds_its_messages_and_frees_its_slot() {
    let mut net = small(3, room(2));
    adj(&mut net, 1, &[]);
    adj(&mut net, 2, &[]);
    net.subscribe(1, T);
    net.subscribe(2, T);
    net.publish(2, T, b"logged");

    // Member 2 is gone for good: cut off, and released by membership.
    let id = net.id(2);
    net.link(2, 0, false);
    let n = &mut net.nodes[0];
    n.t.release(&mut n.h, &id);
    net.advance(RECORD_TTL + REFRESH + SEC);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.records, stats.dropped),
        (2, 0),
        "a tombstone while the log holds its message"
    );

    net.advance(LOG_WINDOW);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!((stats.records, stats.dropped), (1, 1), "dropped once the log let it go");
    adj(&mut net, 3, &[]);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.records, stats.refused, stats.closed),
        (2, 0, false),
        "its slot is free"
    );
}

#[test]
fn a_revoked_member_s_record_is_forgotten_and_not_taken_again() {
    let mut net = small(2, room(8));
    adj(&mut net, 1, &[2]);
    adj(&mut net, 2, &[1]);
    assert!(net.nodes[0].t.same_component(&net.id(1), &net.id(2)));
    let id = net.id(2);
    net.nodes[0].t.revoke(&id);
    assert_eq!(net.nodes[0].t.reach_stats().records, 1);
    assert!(!net.nodes[0].t.same_component(&net.id(1), &net.id(2)));
    net.advance(REFRESH + SEC);
    assert_eq!(
        net.nodes[0].t.reach_stats().records,
        1,
        "its refresh is refused while it is revoked"
    );
}

#[test]
fn a_tombstone_takes_an_older_record_from_its_member_but_not_from_a_hub_mirror() {
    // Hubs 0 and 1, member 2. Its first record (naming 3) is kept back; the second names nobody.
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    let old = capture(&mut net, 2, &[3]);
    adj(&mut net, 2, &[]);
    mute(&mut net, 2, true);
    net.advance(RECORD_TTL + REFRESH + SEC);
    assert_eq!(net.nodes[0].t.reach_stats().live, 0, "expired at hub 0");

    // The older record (as after the member's incarnation went back) handed over by hub 1: a replay, refused.
    ask(&mut net, 0, 1, ty::ADJ, &old);
    assert_eq!(net.nodes[0].t.reach_stats().live, 0);
    // From the member itself: its word, placed again.
    ask(&mut net, 0, 2, ty::ADJ, &old);
    assert_eq!(net.nodes[0].t.reach_stats().live, 1);
}

#[test]
fn records_that_arrive_between_two_checks_are_worked_out_once() {
    let mut net = small(2, room(8));
    adj(&mut net, 1, &[2]);
    adj(&mut net, 2, &[1]);
    assert!(net.nodes[0].t.same_component(&net.id(1), &net.id(2)));
    let r0 = net.nodes[0].t.reach_stats().rebuilds;
    for k in 0..50 {
        adj(&mut net, 1, if k % 2 == 0 { &[] } else { &[2] });
    }
    assert_eq!(
        net.nodes[0].t.reach_stats().rebuilds,
        r0,
        "nothing was checked meanwhile"
    );
    assert!(net.nodes[0].t.same_component(&net.id(1), &net.id(2)));
    assert_eq!(
        net.nodes[0].t.reach_stats().rebuilds,
        r0 + 1,
        "one rebuild for 50 records"
    );

    // A refresh names the same peers: nothing to work out.
    net.advance(REFRESH + SEC);
    assert!(net.nodes[0].t.same_component(&net.id(1), &net.id(2)));
    assert_eq!(net.nodes[0].t.reach_stats().rebuilds, r0 + 1);
}

#[test]
fn a_lost_hub_to_hub_mirror_is_repaired_by_the_refresh() {
    // Hubs 0 and 1; member 2 uses hub 0 only, member 3 hub 1 only. They hold a session.
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    net.set_primary(3, 1);
    net.link(2, 1, false);
    net.link(3, 0, false);
    // Hub 0's mirrors to hub 1 are lost.
    let lost = std::rc::Rc::new(std::cell::Cell::new(true));
    let l = lost.clone();
    net.filter = Some(Box::new(move |from, to, b: &mut Vec<u8>| {
        !(l.get() && from == 0 && to == 1 && b.get(4) == Some(&ty::ADJ))
    }));
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 2, 3, true);
    assert!(net.nodes[0].t.same_component(&net.id(2), &net.id(3)));
    assert!(
        !net.nodes[1].t.same_component(&net.id(2), &net.id(3)),
        "hub 1 never heard member 2's record"
    );
    lost.set(false);
    net.advance(REFRESH + SEC);
    assert!(
        net.nodes[1].t.same_component(&net.id(2), &net.id(3)),
        "the refresh is mirrored again"
    );
}
