//! A hub's adjacency table that closes says so, and opens again (pinc#86, review of #137): each refused record and
//! the closing are reported, the table opens once no refused node waits for a record (each got one once room was made), and a refused
//! node that never got a record keeps it closed. Also what a record costs: its peers and its signature, and a refresh
//! with the same bytes is not verified again.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::expect_used)]

#[path = "broadcast_common.rs"]
mod common;
#[path = "broadcast_reach_support.rs"]
mod support;

use common::{Ev, Net, SEC, ty};
use pinc_broadcast::Limits;
use pinc_broadcast::consts::{LOG_WINDOW, REACH_RECORD_BASE, RECORD_TTL, REFRESH};
use pinc_crypto::IdentityAlg;
use support::{T, adj, ask, capture, room, sends};

/// A hub and `members` members, the hub's table holding `bytes` bytes ([`room`]); every member subscribes.
fn small(members: usize, bytes: usize) -> Net {
    let limits = Limits {
        reach_bytes: bytes,
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
    let mut net = small(members, room(2));
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
    let mut net = small(3, room(8));
    adj(&mut net, 1, &[2, 3]);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        stats.bytes,
        REACH_RECORD_BASE + 2 * 32 + 64,
        "its fixed share, two peers and an Ed25519 signature; the frame is not kept"
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

/// A record of `peers` peers and an Ed25519 signature, as the hub charges it.
const fn cost(peers: usize) -> usize {
    REACH_RECORD_BASE + 32 * peers + 64
}

#[test]
fn the_bound_is_bytes_a_newcomer_that_does_not_fit_them_is_refused_and_the_table_closes() {
    // Room for two records of no peers; member 1 names three peers, so the second record does not fit.
    let mut net = small(4, 2 * cost(0));
    adj(&mut net, 1, &[2, 3, 4]);
    adj(&mut net, 2, &[]);
    let id2 = net.id(2);
    assert_eq!(reach_events(&net), vec![Ev::ReachRefused(id2), Ev::ReachClosed]);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.records, stats.bytes, stats.refused, stats.closed),
        (1, cost(3), 1, true),
        "one record, charged by its bytes, fills the table"
    );
    assert!(
        !sends(&mut net, 2, 3, b"refused to unscoped"),
        "the refused member is alone"
    );
}

#[test]
fn a_record_that_outgrows_the_bytes_leaves_a_tombstone_and_its_next_record_that_fits_takes_its_place() {
    // Members 1 and 2 hold a session; the table has room for one more peer beyond their records.
    let budget = 2 * cost(1) + 32;
    let mut net = small(5, budget);
    adj(&mut net, 1, &[2]);
    adj(&mut net, 2, &[1]);
    let (id1, id2) = (net.id(1), net.id(2));
    assert!(net.nodes[0].t.same_component(&id1, &id2));
    assert!(sends(&mut net, 1, 2, b"linked"));

    // Member 1 drops 2 and names three others: 64 bytes more than the room left. Refused, and member 1 is left a
    // tombstone: the record it outgrew no longer links it to 2. The table stays open: member 1 has a record.
    adj(&mut net, 1, &[3, 4, 5]);
    assert_eq!(reach_events(&net), vec![Ev::ReachRefused(id1)]);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.records, stats.live, stats.bytes, stats.refused, stats.closed),
        (2, 1, REACH_RECORD_BASE + cost(1), 1, false)
    );
    assert!(stats.bytes <= budget);
    assert!(
        !net.nodes[0].t.same_component(&id1, &id2),
        "the outgrown record's edge is gone"
    );
    assert!(!sends(&mut net, 1, 2, b"split"), "member 1 is alone");

    // Member 2 drops 1 too: its record shrinks, and member 1's next refresh fits exactly.
    adj(&mut net, 2, &[]);
    net.advance(REFRESH + SEC);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.live, stats.bytes, stats.closed),
        (2, budget, false),
        "taken once it fits"
    );
}

#[test]
fn a_record_a_member_outgrew_does_not_come_back_from_another_hubs_mirror() {
    // Hubs 0 and 1, members 2 to 6. Hub 0 is handed every record here, so what it holds does not depend on hub 1.
    let budget = 2 * cost(1) + 32;
    let limits = Limits {
        reach_bytes: budget,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 7], 2, SEC, limits);
    for i in 2..7 {
        net.attach(i);
    }
    let (id2, id3) = (net.id(2), net.id(3));
    let old = capture(&mut net, 2, &[3]);
    ask(&mut net, 0, 2, ty::ADJ, &old);
    let other = capture(&mut net, 3, &[2]);
    ask(&mut net, 0, 3, ty::ADJ, &other);
    assert!(net.nodes[0].t.same_component(&id2, &id3));

    // Member 2 drops 3 and names three others: its newer record does not fit and leaves it a tombstone.
    let newer = capture(&mut net, 2, &[4, 5, 6]);
    ask(&mut net, 0, 2, ty::ADJ, &newer);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!((stats.records, stats.live, stats.refused), (2, 1, 1));
    assert!(!net.nodes[0].t.same_component(&id2, &id3));

    // A copy of the record it outgrew, still on its way from hub 1 when the newer one was refused: it would fit, and
    // it is older than what the hub refused, so it is not taken.
    ask(&mut net, 0, 1, ty::ADJ, &old);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.records, stats.live),
        (2, 1),
        "the record member 2 outgrew came back from a mirror"
    );
    assert!(
        !net.nodes[0].t.same_component(&id2, &id3),
        "the outgrown record links member 2 to a peer it dropped"
    );
    // The refused record again, from the member: still too large, and nothing else changed.
    ask(&mut net, 0, 2, ty::ADJ, &newer);
    assert_eq!(net.nodes[0].t.reach_stats().live, 1);
}

#[test]
fn the_charge_follows_the_records_through_expiry_release_and_revocation() {
    let mut net = small(3, room(3));
    adj(&mut net, 1, &[2]);
    adj(&mut net, 2, &[1, 3]);
    adj(&mut net, 3, &[]);
    assert_eq!(net.nodes[0].t.reach_stats().bytes, cost(1) + cost(2) + cost(0));

    // Member 3 is revoked: its record and its charge go.
    let id3 = net.id(3);
    net.nodes[0].t.revoke(&id3);
    assert_eq!(net.nodes[0].t.reach_stats().bytes, cost(1) + cost(2));

    // Member 2 publishes and leaves: its record expires to a tombstone, then goes once the log is clear of it.
    net.publish(2, T, b"logged");
    release(&mut net, 2);
    net.advance(RECORD_TTL + REFRESH + SEC);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!((stats.records, stats.bytes), (2, cost(1) + REACH_RECORD_BASE));
    net.advance(LOG_WINDOW + REFRESH);
    assert_eq!(net.nodes[0].t.reach_stats().bytes, cost(1));
}
