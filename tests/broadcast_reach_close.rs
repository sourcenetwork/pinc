//! A hub's adjacency table that closes says so, and opens again (vinc#86, review of #137): each refused record and
//! the closing are reported, the table opens once no refused node waits for a record (each got one once room was made), and a refused
//! node that never got a record keeps it closed. Also what a record costs: its peers and its signature, and a refresh
//! with the same bytes is not verified again.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::expect_used)]

#[path = "broadcast_common.rs"]
mod common;
#[path = "broadcast_reach_support.rs"]
mod support;

use common::{Ev, Net, SEC, ty};
use support::{T, adj, ask, capture, sends};
use vinc_broadcast::Limits;
use vinc_broadcast::consts::{LOG_WINDOW, RECORD_TTL, REFRESH};
use vinc_crypto::IdentityAlg;

/// A hub and `members` members, the hub's table holding at most `max` records; every member subscribes.
fn small(members: usize, max: usize) -> Net {
    let limits = Limits {
        max_reach: max,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&vec![IdentityAlg::Ed25519; members + 1], 1, SEC, limits);
    for i in 1..=members {
        net.attach(i);
    }
    for i in 1..=members {
        net.subscribe(i, T);
    }
    net
}

/// The reach events the hub reported, in order.
fn reach_events(net: &Net) -> Vec<Ev> {
    net.nodes[0]
        .h
        .events
        .iter()
        .filter(|e| matches!(e, Ev::ReachRefused(_) | Ev::ReachClosed | Ev::ReachOpened))
        .cloned()
        .collect()
}

/// Keep node `i`'s records from reaching the hub (`true`) or let them through again.
fn mute(net: &mut Net, i: usize, on: bool) {
    net.filter = None;
    if on {
        net.filter = Some(Box::new(move |from, _, b: &mut Vec<u8>| {
            !(from == i && b.get(4) == Some(&ty::ADJ))
        }));
    }
}

/// Member `i` leaves for good: cut off from the hub and released by membership.
fn release(net: &mut Net, i: usize) {
    let id = net.id(i);
    net.link(i, 0, false);
    let n = &mut net.nodes[0];
    n.t.release(&mut n.h, &id);
}

/// Records 1 and 2 fill a table of two; member 2 publishes, so the log holds a message of it.
fn full(members: usize) -> Net {
    let mut net = small(members, 2);
    adj(&mut net, 1, &[]);
    adj(&mut net, 2, &[]);
    net.publish(2, T, b"logged");
    net
}

#[test]
fn the_hub_reports_each_refused_record_and_the_closing_once() {
    let mut net = full(4);
    assert_eq!(reach_events(&net), Vec::<Ev>::new());
    adj(&mut net, 3, &[]);
    let (id3, id4) = (net.id(3), net.id(4));
    assert_eq!(reach_events(&net), vec![Ev::ReachRefused(id3), Ev::ReachClosed]);
    adj(&mut net, 4, &[]);
    assert_eq!(
        reach_events(&net),
        vec![Ev::ReachRefused(id3), Ev::ReachClosed, Ev::ReachRefused(id4)],
        "a second refusal is reported, the table closes once"
    );
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.closed, stats.refused, stats.waiting, stats.stuck),
        (true, 2, 2, false)
    );
}

#[test]
fn a_closed_table_opens_once_it_has_room_and_every_refused_node_has_a_record() {
    let mut net = full(5);
    adj(&mut net, 3, &[]);
    assert!(net.nodes[0].t.reach_stats().closed);
    assert!(!sends(&mut net, 4, 5, b"closed"), "closed: the unscoped are alone");

    // Member 2 leaves; its tombstone goes once the log let its message go, which makes room.
    release(&mut net, 2);
    net.advance(RECORD_TTL + REFRESH + SEC);
    assert!(
        net.nodes[0].t.reach_stats().closed,
        "no room while the log holds 2's message"
    );
    net.advance(LOG_WINDOW);
    // Member 3's next refresh takes the free slot; the sweep after it opens the table.
    net.advance(2 * REFRESH + SEC);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.closed, stats.records, stats.waiting, stats.reopened),
        (false, 2, 0, 1)
    );
    assert_eq!(reach_events(&net).last(), Some(&Ev::ReachOpened));
    assert!(
        sends(&mut net, 4, 5, b"open"),
        "open again: the unscoped hear each other"
    );
    assert!(
        !sends(&mut net, 3, 4, b"scoped to unscoped"),
        "the refused member got a record: scoped, alone"
    );
}

#[test]
fn a_refused_node_without_a_record_keeps_the_table_closed_until_it_is_released() {
    let mut net = full(5);
    adj(&mut net, 3, &[]);
    // Member 3's refreshes stop reaching the hub: it waits with no record.
    mute(&mut net, 3, true);
    release(&mut net, 2);
    net.advance(RECORD_TTL + REFRESH + SEC + LOG_WINDOW + 2 * REFRESH);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.closed, stats.records, stats.waiting),
        (true, 1, 1),
        "room, but a refused node waits"
    );
    assert!(
        !sends(&mut net, 3, 4, b"refused to unscoped"),
        "the refused member is never unscoped"
    );

    // Released for good; once the log let its message go, no refused node waits any more.
    release(&mut net, 3);
    net.advance(REFRESH + SEC);
    assert!(
        net.nodes[0].t.reach_stats().closed,
        "the log still holds a message of 3"
    );
    net.advance(LOG_WINDOW + REFRESH + SEC);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!((stats.closed, stats.waiting, stats.reopened), (false, 0, 1));
    assert_eq!(reach_events(&net).last(), Some(&Ev::ReachOpened));
}

#[test]
fn a_record_costs_its_peers_and_its_signature_and_a_refresh_is_not_verified_again() {
    let mut net = small(3, 8);
    adj(&mut net, 1, &[2, 3]);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        stats.bytes,
        2 * 32 + 64,
        "two peers and an Ed25519 signature; the frame is not kept"
    );

    // The same record, byte for byte, a hundred times: heard again, never verified again.
    let same = capture(&mut net, 2, &[1]);
    ask(&mut net, 0, 2, ty::ADJ, &same);
    let checked = net.nodes[0].t.reach_stats().verified;
    for _ in 0..100 {
        ask(&mut net, 0, 2, ty::ADJ, &same);
    }
    assert_eq!(net.nodes[0].t.reach_stats().verified, checked);

    // The same sequence with another signature: refused on its bytes, the table unchanged.
    let before = net.nodes[0].t.reach_stats();
    let mut other = same.clone();
    *other.last_mut().unwrap() ^= 1;
    ask(&mut net, 0, 2, ty::ADJ, &other);
    assert_eq!(net.nodes[0].t.reach_stats(), before);
}
