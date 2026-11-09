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

use common::{Net, SEC, ty};
use vinc_broadcast::consts::{DEFAULT_MAX_BODY, LOG_CAP};
use vinc_broadcast::{Reject, Trace};
use vinc_crypto::IdentityAlg;

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
    use vinc_broadcast::consts::SEEN_CAP;
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
