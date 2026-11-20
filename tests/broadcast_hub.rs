//! The hub log and its pushes: the 120 s window, the 2048-entry cap, the byte ring, mirroring, the hub-to-hub id
//! exchange every 5 s over [-30 s, -1 s], and the dedupe set (600 s, bounded).
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

use std::cell::RefCell;
use std::rc::Rc;

use common::{Ev, Net, SEC, ty};
use pinc_broadcast::consts::{DEFAULT_MAX_BODY, LOG_CAP, SUB_WAIT_MAX, TABLE_MAX};
use pinc_broadcast::{Reject, SubRefusal, Trace};
use pinc_crypto::IdentityAlg;
use pinc_membership::NodeId;

const T: &[u8] = b"log";

fn two_hubs() -> Net {
    // Hubs 0 and 1, publisher 2.
    Net::new(IdentityAlg::Ed25519, 2, 1, SEC)
}

#[test]
fn a_message_stays_in_the_log_for_120s_and_not_a_nanosecond_longer() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1, SEC);
    net.publish(1, T, b"x");
    net.run_until(SEC + 120 * SEC);
    assert_eq!(net.nodes[0].t.log_len(T), 1, "present at exactly 120 s");
    net.run_until(SEC + 120 * SEC + 1);
    assert_eq!(net.nodes[0].t.log_len(T), 0, "gone just after");
}

#[test]
fn the_log_holds_at_most_2048_messages_and_drops_the_oldest() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let mids: Vec<[u8; 8]> = (0..=LOG_CAP).map(|i| net.publish(1, T, &i.to_be_bytes())).collect();
    assert_eq!(net.nodes[0].t.log_len(T), LOG_CAP);
    // Ask the hub for the first and the last message by id, as a gap repair would.
    let (hub, asker) = (net.id(0), net.id(2));
    let served = |net: &mut Net, mid: [u8; 8]| {
        let now = net.now;
        let n = &mut net.nodes[0];
        n.h.out.clear();
        n.t.frame(&mut n.h, now, &asker, ty::GET, T, &mid);
        n.h.out.iter().filter(|o| o.to == asker).count()
    };
    let _ = hub;
    assert_eq!(served(&mut net, mids[0]), 0, "the oldest was evicted");
    assert_eq!(served(&mut net, mids[1]), 1);
    assert_eq!(served(&mut net, mids[LOG_CAP]), 1);
}

#[test]
fn the_log_is_bounded_in_bytes_as_well() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1, SEC);
    let big = vec![7u8; DEFAULT_MAX_BODY];
    // 4 MiB of ring holds at most 64 full-size bodies however many entries are allowed.
    for _ in 0..200 {
        net.publish(1, T, &big);
    }
    let n = net.nodes[0].t.log_len(T);
    assert!(n > 0 && n <= 64, "{n}");
}

#[test]
fn the_hub_pushes_to_subscribers_and_never_back_to_the_sender_or_origin() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    net.subscribe(1, T);
    net.subscribe(2, T);
    net.publish(1, T, b"x");
    assert!(net.delivered(1).is_empty(), "the origin is not pushed its own message");
    assert_eq!(net.delivered(2).len(), 1);
    assert!(net.delivered(3).is_empty(), "a non-subscriber gets nothing");
    assert_eq!(net.count_between(0, 1, ty::MSG), 0);
}

#[test]
fn a_hub_mirrors_a_pub_to_the_other_hubs_and_a_mirrored_copy_is_not_mirrored_again() {
    let mut net = Net::new(IdentityAlg::Ed25519, 3, 1, SEC);
    net.link(3, 1, false);
    net.link(3, 2, false);
    net.publish(3, T, b"x");
    assert_eq!(net.count_between(0, 1, ty::MSG), 1);
    assert_eq!(net.count_between(0, 2, ty::MSG), 1);
    assert_eq!(net.count_between(1, 2, ty::MSG) + net.count_between(1, 0, ty::MSG), 0);
    assert_eq!(net.count_between(2, 1, ty::MSG) + net.count_between(2, 0, ty::MSG), 0);
}

#[test]
fn hub_to_hub_have_runs_every_5s() {
    let mut net = two_hubs();
    net.publish(2, T, b"x");
    let at = |net: &Net| -> Vec<u64> {
        net.log
            .iter()
            .filter(|(_, f, t, y, _)| *f == 0 && *t == 1 && *y == ty::HAVE)
            .map(|l| l.0)
            .collect()
    };
    // The message is logged at 1 s; it enters the [-30, -1] window 1 s later. The exchange fires at 1, 6, 11 ...
    net.run_until(SEC + 15 * SEC);
    let times = at(&net);
    assert!(!times.is_empty());
    for w in times.windows(2) {
        assert_eq!(w[1] - w[0], 5 * SEC, "{times:?}");
    }
}

/// Publish at `at` into a hub whose mirror to hub 1 is cut, heal at `heal`, and return when hub 0 first names the
/// message to hub 1. Hubs start at 100 s, so their id exchange ticks at 100, 105, 110, ... s.
fn first_have(at: u64, heal: u64) -> Option<u64> {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 1, 100 * SEC);
    net.link(2, 1, false);
    net.link(0, 1, false);
    net.run_until(at);
    net.publish(2, T, b"x");
    net.run_until(heal);
    net.link(0, 1, true);
    net.run_until(heal + 60 * SEC);
    net.log
        .iter()
        .find(|l| l.1 == 0 && l.2 == 1 && l.3 == ty::HAVE)
        .map(|l| l.0)
}

#[test]
fn the_id_exchange_names_a_message_only_once_it_is_older_than_1s() {
    // Published at a tick: the next tick sees it 5 s old.
    assert_eq!(first_have(100 * SEC, 100 * SEC), Some(105 * SEC));
    // Published 1 s before a tick: that tick sees it exactly 1 s old, which is outside [-30 s, -1 s).
    assert_eq!(first_have(104 * SEC, 104 * SEC), Some(110 * SEC));
    // 1 ns more than 1 s old is inside.
    assert_eq!(first_have(104 * SEC - 1, 104 * SEC), Some(105 * SEC));
}

#[test]
fn the_id_exchange_stops_naming_a_message_older_than_30s() {
    // Exactly 30 s old at the tick of 135 s: still inside; 1 ns older: outside, and later ticks are older still.
    assert_eq!(first_have(105 * SEC, 135 * SEC - 1), Some(135 * SEC));
    assert_eq!(first_have(105 * SEC - 1, 135 * SEC - 1), None);
}

#[test]
fn a_message_older_than_30s_is_no_longer_announced_between_hubs() {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 1, SEC);
    net.link(2, 1, false);
    net.link(0, 1, false);
    net.publish(2, T, b"x");
    net.run_until(SEC + 36 * SEC);
    net.link(0, 1, true);
    net.run_until(SEC + 120 * SEC);
    assert_eq!(net.count_between(0, 1, ty::HAVE), 0, "the window [-30, -1] has passed");
    assert_eq!(net.nodes[1].t.log_len(T), 0);
}

#[test]
fn a_dedupe_entry_lasts_600s_and_not_a_nanosecond_longer() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    let mid = net.publish(1, T, b"x");
    assert_eq!(net.delivered(2), vec![mid]);
    let stored: std::rc::Rc<std::cell::RefCell<Option<Vec<u8>>>> = std::rc::Rc::default();
    let s2 = stored.clone();
    net.filter = Some(Box::new(move |_, to, b| {
        if to == 2 && b[4] == ty::MSG {
            *s2.borrow_mut() = Some(b.clone());
        }
        true
    }));
    let mid2 = net.publish(1, T, b"y");
    let frame = stored.borrow().clone().unwrap();
    net.filter = None;
    assert_eq!(net.delivered(2), vec![mid, mid2]);
    let replay = |net: &mut Net, at: u64| {
        net.run_until(at);
        let hub = net.id(0);
        let now = net.now;
        let n = &mut net.nodes[2];
        n.t.frame(&mut n.h, now, &hub, ty::MSG, T, &frame[6 + T.len()..]);
        net.pump();
    };
    // Exactly 600 s after the subscriber first saw it (at 1 s): still a duplicate.
    replay(&mut net, SEC + 600 * SEC);
    assert_eq!(net.delivered(2).len(), 2, "still remembered at 600 s");
    replay(&mut net, SEC + 600 * SEC + 1);
    assert_eq!(net.delivered(2).len(), 3, "forgotten just after");
}

#[test]
fn a_full_dedupe_set_refuses_new_ids_instead_of_growing() {
    use pinc_broadcast::consts::SEEN_CAP;
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    let mut full = 0;
    let mut drain = |net: &mut Net| {
        while let Some(t) = net.nodes[2].t.poll_trace() {
            full += usize::from(matches!(
                t,
                Trace::Rejected {
                    why: Reject::SeenFull,
                    ..
                }
            ));
        }
    };
    for i in 0..SEEN_CAP + 5 {
        net.publish(1, T, &i.to_be_bytes());
        if i % 512 == 0 {
            drain(&mut net);
        }
    }
    drain(&mut net);
    assert_eq!(net.delivered(2).len(), SEEN_CAP);
    assert_eq!(full, 5);
}

/// The topic `n` of a member's run of topics: distinct names, so a hub's table entry per topic is one each.
fn topic(n: usize) -> Vec<u8> {
    format!("topic/{n}").into_bytes()
}

/// A hub whose topic table is full drops a member's SUB for a new topic and tells nobody (#695): the member's join
/// returned `Ok`, and no event of the hub, of the topic, ever reaches the member's application. The fix answers with
/// a notice, so the member is told about the topic even though it never hears `Subscribed`: every topic the member
/// joined ends up named in its events, whatever event carries the telling.
#[test]
fn a_join_the_hub_cannot_hold_is_never_left_untold() {
    let limits = pinc_broadcast::Limits {
        max_topics: 31,
        ..pinc_broadcast::Limits::default()
    };
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 3], 1, SEC, limits);
    // Member 1 fills the hub's table: 31 topics, one entry each.
    for n in 0..31 {
        net.subscribe(1, &topic(n));
    }
    net.run_until(SEC + 2 * SEC);
    let got = net.subscribed(1);
    assert_eq!(got.len(), 31, "the member's own topics end in Subscribed");
    // Member 2 joins a 32nd topic: the hub's table is full of member 1's.
    net.subscribe(2, &topic(31));
    net.run_until(SEC + 30 * SEC);
    assert!(
        net.told_about(2, &topic(31)),
        "the hub tells the member it cannot hold the topic"
    );
}

/// The same at the defaults: two followers join 64 and 65 distinct topics, 129 at a hub that holds 128. Every topic
/// either follower joined is named in that follower's events.
#[test]
fn the_same_at_the_defaults_with_two_followers() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    for n in 0..64 {
        net.subscribe(1, &topic(n));
    }
    for n in 0..65 {
        net.subscribe(2, &topic(100 + n));
    }
    net.run_until(SEC + 30 * SEC);
    for n in 0..64 {
        assert!(net.told_about(1, &topic(n)), "member 1 told about {n}");
    }
    for n in 0..65 {
        assert!(net.told_about(2, &topic(100 + n)), "member 2 told about {}", 100 + n);
    }
}

/// A node id no network node has: the `n`th of the nodes a test hands a hub frames from. It is not in the host's
/// `reach`, so a hub's sends to it fail cheaply.
fn fake(n: usize) -> NodeId {
    let mut id = [0xFF; 32];
    id[30..].copy_from_slice(&(n as u16).to_be_bytes());
    id
}

/// A SUB for `topic` from `from` handed to hub 0 as a frame.
fn sub_from(net: &mut Net, from: &NodeId, topic: &[u8]) {
    let now = net.now;
    let n = &mut net.nodes[0];
    n.t.frame(&mut n.h, now, from, ty::SUB, topic, &[0u8; 8]);
}

/// A SUBS frame of kind 3 (the hub-full notice) in `bytes`.
fn is_notice(bytes: &[u8]) -> bool {
    let tl = usize::from(bytes[5]);
    bytes[4] == ty::SUBS && bytes.get(6 + tl) == Some(&3)
}

fn notices_to(net: &Net, to: &NodeId) -> usize {
    net.nodes[0].h.out.iter().filter(|o| o.to == *to && is_notice(&o.bytes)).count()
}

/// A hub whose topic has `TABLE_MAX` subscribers answers a new member's SUB with the notice and counts it; a
/// subscriber it holds is not refused, and a place freed by an unsubscribe is taken.
#[test]
fn a_hub_at_the_subscriber_cap_answers_a_new_member_with_the_notice() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1, SEC);
    for n in 0..TABLE_MAX {
        sub_from(&mut net, &fake(n), T);
    }
    assert_eq!(net.nodes[0].t.subscriber_count(T), TABLE_MAX);
    let newcomer = fake(TABLE_MAX);
    // The two nodes whose frames are looked at are reachable, so the host records what is sent to them.
    net.nodes[0].h.reach.insert(newcomer);
    net.nodes[0].h.reach.insert(fake(0));
    net.nodes[0].h.out.clear();
    sub_from(&mut net, &newcomer, T);
    assert_eq!(notices_to(&net, &newcomer), 1);
    assert_eq!(net.nodes[0].t.subscriber_count(T), TABLE_MAX);
    assert_eq!(net.nodes[0].t.reject_stats().sub_refused(SubRefusal::Subscribers), 1);
    assert_eq!(net.nodes[0].t.reject_stats().sub_refused(SubRefusal::Topics), 0);
    net.nodes[0].h.out.clear();
    sub_from(&mut net, &fake(0), T);
    assert_eq!(notices_to(&net, &fake(0)), 0, "a subscriber the hub holds is not refused");
    assert_eq!(net.nodes[0].t.reject_stats().sub_refused(SubRefusal::Subscribers), 1);
    let now = net.now;
    let n = &mut net.nodes[0];
    n.t.frame(&mut n.h, now, &fake(0), ty::UNSUB, T, &[]);
    n.h.out.clear();
    sub_from(&mut net, &newcomer, T);
    assert_eq!(notices_to(&net, &newcomer), 0, "the freed place is taken");
    assert_eq!(net.nodes[0].t.subscriber_count(T), TABLE_MAX);
}

/// A member the hub refused is told once, asks again at 2, 4, 8, 16, 32 and 64 s and then every 64 s, one notice
/// answering each ask, and ends in `Subscribed` once the hub has room; a topic it leaves is asked about no more.
#[test]
fn a_refused_join_asks_again_on_a_bounded_backoff_and_ends_in_joined() {
    const U: &[u8] = b"other";
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1, SEC);
    for n in 0..TABLE_MAX {
        sub_from(&mut net, &fake(n), T);
        sub_from(&mut net, &fake(n), U);
    }
    assert!(net.id(1) < fake(0), "the cut list names the member");
    let seen = Rc::new(RefCell::new(Vec::<(usize, usize, Vec<u8>, u8)>::new()));
    let s = Rc::clone(&seen);
    net.filter = Some(Box::new(move |from, to, bytes| {
        // Every frame, so the entries pair with the network's own log one to one.
        let tl = bytes.get(5).map_or(0, |t| usize::from(*t));
        let topic = bytes.get(6..6 + tl).unwrap_or_default().to_vec();
        let kind = bytes.get(4).copied().unwrap_or(0);
        s.borrow_mut().push((from, to, topic, kind));
        true
    }));
    let base = net.log.len();
    let t0 = net.now;
    net.subscribe(1, T);
    net.subscribe(1, U);
    net.run_until(t0 + 10 * SEC);
    net.unsubscribe(1, U);
    net.run_until(t0 + 200 * SEC);
    assert_eq!(net.events(1).iter().filter(|e| matches!(e, Ev::HubFull { .. })).count(), 2, "one per topic");
    assert!(net.subscribed(1).is_empty());
    let (log, seen_now) = (&net.log[base..], seen.borrow().clone());
    assert_eq!(log.len(), seen_now.len());
    let mut times = Vec::new();
    let (mut asks_u, mut notices_t, mut notices_u) = (0, 0, 0);
    for (l, f) in log.iter().zip(&seen_now) {
        match (f.0, f.2.as_slice(), f.3) {
            (1, t, ty::SUB) if t == T => times.push(l.0),
            (1, t, ty::SUB) if t == U => asks_u += 1,
            (0, t, ty::SUBS) if t == T => notices_t += 1,
            (0, t, ty::SUBS) if t == U => notices_u += 1,
            _ => {}
        }
    }
    let want: Vec<u64> = [0, 2, 6, 14, 30, 62, 126, 190].iter().map(|s| t0 + s * SEC).collect();
    let secs = |v: &[u64]| v.iter().map(|t| (t - t0) / 1_000_000).collect::<Vec<_>>();
    assert_eq!(secs(&times), secs(&want));
    assert!(times.windows(3).all(|w| w[1] - w[0] <= w[2] - w[1]), "gaps never shrink");
    assert!(times.windows(2).all(|w| w[1] - w[0] <= SUB_WAIT_MAX), "gaps stay within the cap");
    assert_eq!(notices_t, times.len(), "a notice for each ask");
    assert_eq!(asks_u, 3, "U asked at 0, 2 and 6 s and not after the unsubscribe");
    assert_eq!(notices_u, 3);
    // Room frees up: the next ask is taken.
    let now = net.now;
    let n = &mut net.nodes[0];
    n.t.frame(&mut n.h, now, &fake(0), ty::UNSUB, T, &[]);
    net.run_until(now + SUB_WAIT_MAX + SEC);
    assert_eq!(net.subscribed(1), [T.to_vec()]);
    let asked = net.count_between(1, 0, ty::SUB);
    net.run_until(net.now + 200 * SEC);
    assert_eq!(net.count_between(1, 0, ty::SUB), asked, "no ask once the hub holds it");
}
