//! The access-control hold: messages from an origin nobody has answered for are held (at most 64) and one check is
//! asked per origin; an allow delivers what was held, a deny drops it; the verdict is trusted for 30 s of local time.
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

use common::{Ev, Net, SEC};
use vinc_broadcast::consts::HELD_MAX;
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"acp";

/// Hub 0, publishers 1 and 2, subscriber 3 who answers access checks by hand.
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    net.nodes[3].auto_acp = None;
    net.subscribe(3, T);
    net
}

fn checks(net: &Net) -> Vec<(u32, [u8; 32])> {
    net.events(3)
        .iter()
        .filter_map(|e| {
            if let Ev::Acp { id, origin, .. } = e {
                Some((*id, *origin))
            } else {
                None
            }
        })
        .collect()
}

fn answer(net: &mut Net, id: u32, allow: bool) {
    let now = net.now;
    let n = &mut net.nodes[3];
    n.t.acp_answer(&mut n.h, now, id, allow);
    net.pump();
}

#[test]
fn a_message_waits_for_the_answer_and_is_delivered_on_allow() {
    let mut net = world();
    let m = net.publish(1, T, b"x");
    assert!(net.delivered(3).is_empty());
    let c = checks(&net);
    assert_eq!(c.len(), 1);
    assert_eq!(c[0].1, net.id(1));
    answer(&mut net, c[0].0, true);
    assert_eq!(net.delivered(3), vec![m]);
}

#[test]
fn a_deny_drops_what_was_held() {
    let mut net = world();
    net.publish(1, T, b"x");
    let c = checks(&net);
    answer(&mut net, c[0].0, false);
    assert!(net.delivered(3).is_empty());
}

#[test]
fn one_check_is_asked_per_origin_however_many_messages_wait() {
    let mut net = world();
    for i in 0..5u8 {
        net.publish(1, T, &[i]);
    }
    net.publish(2, T, b"other");
    let c = checks(&net);
    assert_eq!(c.len(), 2);
    assert_ne!(c[0].1, c[1].1);
}

#[test]
fn only_the_answered_origin_is_released() {
    let mut net = world();
    let a = net.publish(1, T, b"from 1");
    let b = net.publish(2, T, b"from 2");
    let c = checks(&net);
    let for1 = c.iter().find(|x| x.1 == net.id(1)).unwrap().0;
    let for2 = c.iter().find(|x| x.1 == net.id(2)).unwrap().0;
    answer(&mut net, for1, true);
    assert_eq!(net.delivered(3), vec![a]);
    answer(&mut net, for2, true);
    assert_eq!(net.delivered(3), vec![a, b]);
}

#[test]
fn at_most_64_messages_are_held() {
    let mut net = world();
    for i in 0..HELD_MAX + 6 {
        net.publish(1, T, &u32::try_from(i).unwrap().to_be_bytes());
    }
    let c = checks(&net);
    assert_eq!(c.len(), 1);
    assert_eq!(net.delivered(3).len(), 0);
    // The answer delivers the 64 held, and with room again the node asks the hub for the six it refused (vinc#510).
    answer(&mut net, c[0].0, true);
    assert_eq!(net.delivered(3).len(), HELD_MAX + 6);
}

#[test]
fn a_verdict_is_trusted_for_30s_and_not_a_nanosecond_longer() {
    let mut net = world();
    net.publish(1, T, b"first");
    let c = checks(&net);
    let t0 = net.now;
    answer(&mut net, c[0].0, true);
    // Exactly 30 s after the answer the verdict still holds: delivered at once, no new check.
    net.run_until(t0 + 30 * SEC);
    let m = net.publish(1, T, b"inside");
    assert!(net.delivered(3).contains(&m));
    assert_eq!(checks(&net).len(), 1);
    // One nanosecond later it has lapsed: the message is held and a new check is asked.
    net.run_until(t0 + 30 * SEC + 1);
    let m2 = net.publish(1, T, b"outside");
    assert!(!net.delivered(3).contains(&m2));
    assert_eq!(checks(&net).len(), 2);
}

#[test]
fn a_deny_is_remembered_too() {
    let mut net = world();
    net.publish(1, T, b"first");
    let c = checks(&net);
    answer(&mut net, c[0].0, false);
    let m = net.publish(1, T, b"second");
    assert!(!net.delivered(3).contains(&m));
    assert_eq!(checks(&net).len(), 1, "no new check inside the 30 s");
}

#[test]
fn an_answer_for_an_unknown_check_is_ignored() {
    let mut net = world();
    answer(&mut net, 999, true);
    assert!(net.delivered(3).is_empty());
}
