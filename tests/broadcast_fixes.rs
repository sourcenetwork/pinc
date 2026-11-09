//! Regressions for the findings of the model checks of `vinc-broadcast`: each test fails on the code as it was before
//! the fix (see `proofs/tla/BroadcastNode_*.cfg`).
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

use std::cell::RefCell;
use std::rc::Rc;

use common::{Ev, Net, SEC, ty};
use vinc_broadcast::consts::HELD_MAX;
use vinc_broadcast::{Limits, Reject, Trace};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"fix";

fn checks(net: &Net, i: usize) -> Vec<u32> {
    net.events(i)
        .iter()
        .filter_map(|e| if let Ev::Acp { id, .. } = e { Some(*id) } else { None })
        .collect()
}

fn answer(net: &mut Net, i: usize, id: u32, allow: bool) {
    let now = net.now;
    let n = &mut net.nodes[i];
    n.t.acp_answer(&mut n.h, now, id, allow);
    net.pump();
}

/// A subscriber that is not answered asks for a message when the held set is full and gets it again from the gap
/// repair; before the fix it marked the message seen and dropped it for good.
#[test]
fn a_message_that_found_the_held_set_full_is_repaired_not_lost() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.nodes[2].auto_acp = None;
    net.subscribe(2, T);
    let total = HELD_MAX + 6;
    let mut sent = Vec::new();
    for i in 0..total {
        sent.push(net.publish(1, T, &u32::try_from(i).unwrap().to_be_bytes()));
    }
    let ids = checks(&net, 2);
    assert_eq!(ids.len(), 1);
    answer(&mut net, 2, ids[0], true);
    assert_eq!(net.delivered(2).len(), HELD_MAX);
    // The periodic check (every 20 s) asks the hub for the ids the node lacks; the verdict (30 s) still holds.
    net.advance(25 * SEC);
    let mut got = net.delivered(2);
    got.sort_unstable();
    got.dedup();
    sent.sort_unstable();
    assert_eq!(got, sent, "every message arrives once");
    assert_eq!(net.delivered(2).len(), total);
}

#[test]
fn a_full_held_set_is_reported_as_a_rejection() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.nodes[2].auto_acp = None;
    net.subscribe(2, T);
    for i in 0..=HELD_MAX {
        net.publish(1, T, &u32::try_from(i).unwrap().to_be_bytes());
    }
    let mut full = 0;
    while let Some(t) = net.nodes[2].t.poll_trace() {
        if matches!(
            t,
            Trace::Rejected {
                why: Reject::HeldFull,
                ..
            }
        ) {
            full += 1;
        }
    }
    assert_eq!(full, 1);
}

/// The same message held twice (a copy that arrives after the dedupe set forgot the first, while the answer is still
/// out) is delivered once.
#[test]
fn a_copy_that_arrives_after_the_dedupe_window_waits_once() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.nodes[2].auto_acp = None;
    net.subscribe(2, T);
    let seen: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
    let tap = Rc::clone(&seen);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if to == 2 && bytes.get(4) == Some(&ty::MSG) {
            tap.borrow_mut().push(bytes.clone());
        }
        true
    }));
    let m = net.publish(1, T, b"once");
    let frame = seen.borrow()[0].clone();
    let ids = checks(&net, 2);
    // Past the 600 s the id is forgotten; a relay hands the same message over again.
    net.advance(601 * SEC);
    let (ty_byte, tl) = (frame[4], usize::from(frame[5]));
    let _ = ty_byte;
    let (topic, rest) = (&frame[6..6 + tl], &frame[6 + tl..]);
    let (now, from) = (net.now, net.id(1));
    {
        let n = &mut net.nodes[2];
        n.h.tick(now);
        n.t.frame(&mut n.h, now, &from, ty::MEMBER_PUSH, topic, rest);
    }
    net.pump();
    answer(&mut net, 2, ids[0], true);
    let got: Vec<_> = net.delivered(2).into_iter().filter(|x| *x == m).collect();
    assert_eq!(got.len(), 1);
}

/// A hub acknowledges a publish only after it stored it: with no room for the topic the publisher hears no PACK and
/// gives up instead of believing the message is safe.
#[test]
fn a_hub_without_room_for_the_topic_does_not_acknowledge() {
    let limits = Limits {
        max_topics: 1,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 3], 1, SEC, limits);
    for i in 1..3 {
        net.attach(i);
    }
    // The subscriber's topic takes the hub's only slot.
    net.subscribe(2, b"taken");
    let m = net.publish(1, b"full", b"x");
    net.advance(100 * SEC);
    let acked = net.events(1).contains(&Ev::Acked(m));
    let gave_up = net.events(1).contains(&Ev::GaveUp(m));
    assert!(!acked, "the hub did not store it");
    assert!(gave_up);
}

/// A message the subscriber received over a member session (the fallback) must not move the point a re-subscription
/// asks the hub log back from: an older message the hub logged while the subscriber was cut off is still repaired.
#[test]
fn a_fallback_message_does_not_hide_an_older_missed_one_from_the_repair() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    net.publish(1, T, b"warm up");
    net.run_until(2 * SEC);
    assert_eq!(net.nodes[1].t.known_subscribers(T).len(), 1);
    net.link(2, 0, false);
    net.run_until(3 * SEC);
    let missed = net.publish(1, T, b"missed");
    net.run_until(18 * SEC);
    net.cut_from_hubs(1, false);
    net.run_until(20 * SEC);
    let pushed = net.publish(1, T, b"fallback");
    assert!(
        net.delivered(2).contains(&pushed),
        "the fallback reached the subscriber"
    );
    net.run_until(30 * SEC);
    net.link(2, 0, true);
    let hub = net.id(0);
    let now = net.now;
    {
        let n = &mut net.nodes[2];
        n.h.tick(now);
        n.t.resubscribe(&mut n.h, now, &hub);
    }
    net.pump();
    net.run_until(60 * SEC);
    assert!(
        net.delivered(2).contains(&missed),
        "the hub still logs it, so the repair brings it"
    );
}

/// A hub whose log evicts at once (a tiny ring) must remember each id once: a second record of the same id at the
/// same instant halved what the dedupe set could hold, and a replay of an early message was stored again.
#[test]
fn log_eviction_does_not_spend_a_second_dedupe_record_per_id() {
    let limits = Limits {
        max_body: 16,
        log_bytes: 16 + vinc_broadcast::wire::MAX_HEAD,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 2], 1, SEC, limits);
    net.attach(1);
    let first: Rc<RefCell<Option<Vec<u8>>>> = Rc::default();
    let tap = Rc::clone(&first);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if to == 0 && bytes.get(4) == Some(&ty::FANP) && tap.borrow().is_none() {
            *tap.borrow_mut() = Some(bytes.clone());
        }
        true
    }));
    for i in 0..4500u32 {
        net.publish(1, T, &i.to_be_bytes());
    }
    net.filter = None;
    while net.nodes[0].t.poll_trace().is_some() {}
    let frame = first.borrow().clone().unwrap();
    let tl = usize::from(frame[5]);
    let (topic, rest) = (&frame[6..6 + tl], &frame[6 + tl..]);
    let (now, from) = (net.now, net.id(1));
    {
        let n = &mut net.nodes[0];
        n.h.tick(now);
        n.t.frame(&mut n.h, now, &from, ty::FANP, topic, rest);
    }
    let mut dup = false;
    while let Some(t) = net.nodes[0].t.poll_trace() {
        dup |= matches!(
            t,
            Trace::Rejected {
                why: Reject::Duplicate,
                ..
            }
        );
    }
    assert!(dup, "the first message is still remembered");
}

/// A message the hub's push lost, older than 15 s before the next one that arrived, must still be asked for when a
/// link flap skips the periodic check and the re-subscription follows: the re-subscription goes back to the last
/// check that was sent.
#[test]
fn a_swallowed_message_is_repaired_after_a_flap_that_skips_the_check() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    for k in 0..5u64 {
        net.run_until((10 + 20 * k) * SEC);
        net.publish(1, T, &[k as u8]);
    }
    // The checks ran at 21, 41, ... 101 s. The push of the message at 102 s is swallowed.
    net.run_until(102 * SEC);
    net.filter = Some(Box::new(|_, to, bytes| !(to == 2 && bytes.get(4) == Some(&ty::MSG))));
    let missed = net.publish(1, T, b"swallowed");
    net.filter = None;
    net.run_until(118 * SEC);
    let later = net.publish(1, T, b"later");
    assert!(net.delivered(2).contains(&later) && !net.delivered(2).contains(&missed));
    // The link drops before the check at 121 s and returns at 130 s, when membership asks to subscribe again.
    net.run_until(119 * SEC);
    net.link(2, 0, false);
    net.run_until(130 * SEC);
    net.link(2, 0, true);
    let hub = net.id(0);
    let now = net.now;
    {
        let n = &mut net.nodes[2];
        n.h.tick(now);
        n.t.resubscribe(&mut n.h, now, &hub);
    }
    net.pump();
    assert!(
        net.delivered(2).contains(&missed),
        "the re-subscription asks back to the last check"
    );
}
