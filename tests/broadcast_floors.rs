//! Replay floors: a restarted member learns from the hubs what an earlier life already delivered (`REPLAY_FLOOR`,
//! `ORIGIN_FLOOR`, `FLOOR_AUTH`), holds messages until it knows (`FLOOR_HOLD`, at most 256), gives up after 15 s, and a node
//! no hub ever sent to keeps everything (`FRESH_KEEP`).
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::assert_is_empty,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

use common::{Net, SEC, ty};
use vinc_broadcast::consts::{FHOLD_MAX, ORIGIN_MAX};
use vinc_broadcast::{HoldWhy, Reject, Trace};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"floor";

/// Hubs 0 and 1, publisher 2, subscriber 3.
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    net.subscribe(3, T);
    net
}

fn rejected_old(net: &mut Net, i: usize) -> usize {
    let mut n = 0;
    while let Some(t) = net.nodes[i].t.poll_trace() {
        n += usize::from(matches!(t, Trace::Rejected { why: Reject::Old, .. }));
    }
    n
}

#[test]
fn a_restarted_member_does_not_redeliver_what_its_earlier_life_delivered_and_gets_what_it_missed() {
    let mut net = world();
    let m1 = net.publish(2, T, b"delivered before the restart");
    net.run_until(5 * SEC);
    assert_eq!(net.delivered(3), vec![m1]);
    // The member goes away; a message is published meanwhile.
    net.cut_from_hubs(3, false);
    net.run_until(50 * SEC);
    let m2 = net.publish(2, T, b"missed");
    net.run_until(100 * SEC);
    // A new life: the hubs report their floors when it attaches, and replay the log from the floor.
    net.restart(3, 100 * SEC);
    net.cut_from_hubs(3, true);
    net.set_primary(3, 0);
    net.subscribe(3, T);
    net.attach(3);
    net.run_until(110 * SEC);
    assert_eq!(
        net.delivered(3),
        vec![m2],
        "only the message the earlier life never saw"
    );
    assert!(
        rejected_old(&mut net, 3) >= 1,
        "the old copy was recognised and dropped"
    );
}

/// A replay gives the restarted member every message the hub's log holds since its floor, oldest first, not only
/// the newest 256 (vinc#510): the log holds up to 2,048 and the member's stream paces what it takes.
#[test]
fn a_replay_gives_every_message_the_log_holds_since_the_floor() {
    let mut net = world();
    let m1 = net.publish(2, T, b"delivered before the restart");
    net.run_until(5 * SEC);
    assert_eq!(net.delivered(3), vec![m1]);
    net.cut_from_hubs(3, false);
    let missed: Vec<[u8; 8]> = (0..600u32)
        .map(|k| {
            let m = net.publish(2, T, &k.to_be_bytes());
            net.advance(SEC / 1000);
            m
        })
        .collect();
    net.restart(3, 20 * SEC);
    net.cut_from_hubs(3, true);
    net.set_primary(3, 0);
    net.subscribe(3, T);
    net.attach(3);
    net.run_until(25 * SEC);
    assert_eq!(
        net.delivered(3).len(),
        missed.len(),
        "the replay left messages the log holds unsent"
    );
    assert_eq!(net.delivered(3), missed, "in the order they were logged");
}

#[test]
fn messages_arriving_before_every_hub_reported_are_held_and_released_in_order() {
    let mut net = world();
    net.restart(3, 10 * SEC);
    net.set_primary(3, 0);
    net.link(3, 1, false);
    net.attach_to(3, 0);
    net.subscribe(3, T);
    let a = net.publish(2, T, b"a");
    let b = net.publish(2, T, b"b");
    net.run_until(12 * SEC);
    assert!(net.delivered(3).is_empty(), "held until hub 1 reports its floor");
    net.link(3, 1, true);
    net.attach_to(3, 1);
    net.run_until(13 * SEC);
    assert_eq!(net.delivered(3), vec![a, b]);
}

#[test]
fn a_node_no_hub_ever_sent_to_keeps_messages_whose_origin_clock_is_far_behind() {
    let mut net = world();
    // The publisher's clock is an hour behind: its timestamps look older than the new node's start.
    net.nodes[2].h.skew_ms = -3_600_000;
    net.restart(3, 10 * SEC);
    net.set_primary(3, 0);
    net.subscribe(3, T);
    net.attach(3);
    let m = net.publish(2, T, b"from the past");
    net.run_until(12 * SEC);
    assert_eq!(
        net.delivered(3),
        vec![m],
        "FRESH_KEEP: nothing can be a duplicate of an earlier life"
    );
}

#[test]
fn an_origin_is_judged_by_its_own_floor_not_by_the_local_clock() {
    let mut net = world();
    net.nodes[2].h.skew_ms = -3_600_000;
    let m1 = net.publish(2, T, b"first life");
    net.run_until(5 * SEC);
    assert_eq!(net.delivered(3), vec![m1]);
    net.restart(3, 20 * SEC);
    net.set_primary(3, 0);
    net.subscribe(3, T);
    net.attach(3);
    net.run_until(25 * SEC);
    // The hub's floor for this origin is the timestamp of m1; a later message of the same origin is newer, though
    // the local clock says an hour older than the start.
    let m2 = net.publish(2, T, b"second life");
    net.run_until(30 * SEC);
    assert_eq!(net.delivered(3), vec![m2]);
}

#[test]
fn the_wait_for_the_floors_ends_15s_after_the_start_and_not_before() {
    let mut net = world();
    net.restart(3, 10 * SEC);
    net.set_primary(3, 0);
    net.subscribe(3, T);
    // Hub 1 never reports (it is cut off), so the gathering cannot complete.
    net.link(3, 1, false);
    net.attach(3);
    let m = net.publish(2, T, b"x");
    net.run_until(25 * SEC);
    assert!(
        net.delivered(3).is_empty(),
        "exactly 15 s after the start the wait goes on"
    );
    net.run_until(25 * SEC + 1);
    assert_eq!(
        net.delivered(3),
        vec![m],
        "just after 15 s the held message is offered and delivered"
    );
}

#[test]
fn at_most_256_messages_are_held_for_the_floors() {
    let mut net = world();
    net.restart(3, 10 * SEC);
    net.set_primary(3, 0);
    net.subscribe(3, T);
    net.link(3, 1, false);
    net.attach(3);
    for i in 0..FHOLD_MAX + 4 {
        net.publish(2, T, &u32::try_from(i).unwrap().to_be_bytes());
    }
    net.run_until(24 * SEC);
    let mut held = 0;
    while let Some(t) = net.nodes[3].t.poll_trace() {
        held += usize::from(matches!(
            t,
            Trace::Held {
                why: HoldWhy::Floor,
                ..
            }
        ));
    }
    assert_eq!(held, FHOLD_MAX, "the four beyond the cap were not held");
}

#[test]
fn the_floor_frame_names_the_newest_sent_and_whether_the_hub_ever_sent() {
    let mut net = world();
    let known = net.id(3);
    let stranger = net.id(2);
    let mut body = [0u8; 4096];
    // Before any push: no history, the floor is the hub's start, an empty origin list.
    let n = net.nodes[0].t.floor(&known, &mut body);
    assert_eq!(n, 12 + 1 + 2);
    assert_eq!(body[12], 0, "no history yet");
    assert_eq!(&body[13..15], &[1, 0]);
    net.publish(2, T, b"x");
    let n = net.nodes[0].t.floor(&known, &mut body);
    assert_eq!(n, 12 + 1 + 2 + 8 + 12, "one origin listed");
    assert_eq!(body[12], 1, "history");
    assert_eq!(body[14], 1);
    assert_eq!(&body[15..23], &stranger[..8]);
    // A member does not report floors.
    assert_eq!(net.nodes[3].t.floor(&known, &mut body), 0);
}

#[test]
fn a_floor_frame_that_is_cut_short_is_ignored() {
    let mut net = world();
    net.restart(3, 10 * SEC);
    let hub = net.id(0);
    for len in 0..13 {
        let now = net.now;
        let n = &mut net.nodes[3];
        n.t.frame(&mut n.h, now, &hub, ty::FLOOR, &[], &vec![0; len]);
    }
    // Still gathering: a message is held, not delivered.
    net.set_primary(3, 0);
    net.subscribe(3, T);
    net.publish(2, T, b"x");
    net.run_until(11 * SEC);
    assert!(net.delivered(3).is_empty());
}

#[test]
fn the_per_origin_floor_lists_128_origins_and_no_more() {
    // Hub 0, subscriber 1, then one publisher per origin.
    let build = |origins: usize| {
        let mut net = Net::new(IdentityAlg::Ed25519, 1, 1 + origins, SEC);
        net.subscribe(1, T);
        for i in 0..origins {
            net.publish(2 + i, T, &[i as u8]);
        }
        net
    };
    let sub = |net: &Net| net.id(1);
    let mut body = [0u8; 4096];

    let mut net = build(ORIGIN_MAX);
    let me = sub(&net);
    let n = net.nodes[0].t.floor(&me, &mut body);
    assert_eq!(n, 12 + 1 + 2 + ORIGIN_MAX * 20, "every origin is listed at the cap");
    assert_eq!(&body[13..15], &[1, ORIGIN_MAX as u8]);

    let mut net = build(ORIGIN_MAX + 1);
    let me = sub(&net);
    let n = net.nodes[0].t.floor(&me, &mut body);
    assert_eq!(
        n,
        12 + 1 + 1,
        "one origin past the cap: no per-origin list, only the overall floor"
    );
    assert_eq!(body[12], 1, "history is still reported");
    assert_eq!(body[13], 0);
}
