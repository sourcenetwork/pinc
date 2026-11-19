//! The member-to-member fallback: while no hub is reachable a publisher sends the message over member sessions to
//! the subscribers of the topic that the view lists, paced and bounded, and receivers dedupe by id.
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

use common::{Ev, Net, SEC, ty};
use pinc_broadcast::consts::FALLBACK_BATCH;
use pinc_crypto::IdentityAlg;

const T: &[u8] = b"cloud";

/// Hub 0; publisher 1; subscribers 2 and 3; bystander 4. The publisher published once through the hub, so it was told
/// the subscribers.
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 4, SEC);
    net.subscribe(2, T);
    net.subscribe(3, T);
    net.publish(1, T, b"warm up");
    net.run_until(2 * SEC);
    assert_eq!(net.nodes[1].t.known_subscribers(T).len(), 2);
    net
}

fn fallback_targets(net: &Net, i: usize) -> Vec<[u8; 32]> {
    net.events(i)
        .iter()
        .filter_map(|e| {
            if let Ev::Fallback { to, .. } = e {
                Some(*to)
            } else {
                None
            }
        })
        .collect()
}

#[test]
fn with_every_hub_cut_off_the_message_goes_straight_to_the_subscribers_and_only_them() {
    let mut net = world();
    for i in 1..=4 {
        net.cut_from_hubs(i, false);
    }
    let m = net.publish(1, T, b"late");
    // Delivered at once, with no hub in the path.
    assert!(net.delivered(2).contains(&m));
    assert!(net.delivered(3).contains(&m));
    assert!(net.delivered(4).is_empty(), "the bystander is not a subscriber");
    let mut got = fallback_targets(&net, 1);
    got.sort_unstable();
    let mut want = vec![net.id(2), net.id(3)];
    want.sort_unstable();
    assert_eq!(got, want);
    assert_eq!(net.count(ty::MEMBER_PUSH), 2);
}

#[test]
fn the_fallback_does_not_fire_while_a_hub_is_reachable() {
    let mut net = world();
    // The subscribers are cut off, but the publisher still reaches the hub.
    net.cut_from_hubs(2, false);
    net.cut_from_hubs(3, false);
    net.publish(1, T, b"x");
    net.run_until(60 * SEC);
    assert_eq!(net.count(ty::MEMBER_PUSH), 0);
    assert!(fallback_targets(&net, 1).is_empty());
}

#[test]
fn one_reachable_hub_among_several_is_enough_to_hold_the_fallback_back() {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 3, SEC);
    net.subscribe(3, T);
    net.publish(2, T, b"warm up");
    net.run_until(2 * SEC);
    net.link(2, 0, false);
    net.publish(2, T, b"x");
    assert_eq!(net.count(ty::MEMBER_PUSH), 0, "hub 1 is up");
}

#[test]
fn a_subscriber_that_left_the_view_is_not_pushed_to() {
    let mut net = world();
    for i in 1..=4 {
        net.cut_from_hubs(i, false);
    }
    let gone = net.id(3);
    net.nodes[1].h.view.remove(&gone);
    net.publish(1, T, b"x");
    assert_eq!(fallback_targets(&net, 1), vec![net.id(2)]);
}

#[test]
fn receivers_dedupe_by_id_when_the_hub_path_returns() {
    let mut net = world();
    for i in 1..=4 {
        net.cut_from_hubs(i, false);
    }
    let m = net.publish(1, T, b"late");
    for i in 1..=4 {
        net.cut_from_hubs(i, true);
    }
    net.run_until(40 * SEC);
    assert_eq!(net.delivered(2).iter().filter(|x| **x == m).count(), 1);
    assert_eq!(net.delivered(3).iter().filter(|x| **x == m).count(), 1);
    assert_eq!(net.nodes[1].t.pending_len(), 0, "the hub acknowledged on a retry");
}

#[test]
fn the_fallback_stops_once_the_hub_acknowledges_and_never_repeats_to_a_served_subscriber() {
    let mut net = world();
    for i in 1..=4 {
        net.cut_from_hubs(i, false);
    }
    net.publish(1, T, b"late");
    net.run_until(30 * SEC);
    assert_eq!(
        net.count(ty::MEMBER_PUSH),
        2,
        "each subscriber once, however many retries"
    );
}

#[test]
fn it_is_paced_a_batch_per_retry() {
    let subs = 2 * FALLBACK_BATCH + 3;
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1 + subs, SEC);
    for i in 2..2 + subs {
        net.subscribe(i, T);
    }
    net.publish(1, T, b"warm up");
    net.run_until(2 * SEC);
    for i in 1..2 + subs {
        net.cut_from_hubs(i, false);
    }
    let t0 = net.now;
    net.publish(1, T, b"late");
    let sent_at: Vec<u64> = net.log.iter().filter(|l| l.3 == ty::MEMBER_PUSH).map(|l| l.0).collect();
    assert_eq!(sent_at.len(), FALLBACK_BATCH, "one batch at publish");
    net.run_until(t0 + 3 * SEC);
    assert_eq!(
        net.count(ty::MEMBER_PUSH),
        2 * FALLBACK_BATCH,
        "the next batch 3 s later"
    );
    net.run_until(t0 + 6 * SEC);
    assert_eq!(net.count(ty::MEMBER_PUSH), subs);
    net.run_until(t0 + 30 * SEC);
    assert_eq!(net.count(ty::MEMBER_PUSH), subs, "never more than the subscriber set");
}

#[test]
fn a_subscriber_the_publisher_cannot_reach_is_tried_again_at_the_next_step() {
    let mut net = world();
    for i in 1..=4 {
        net.cut_from_hubs(i, false);
    }
    net.link(1, 3, false);
    let t0 = net.now;
    let m = net.publish(1, T, b"late");
    assert_eq!(fallback_targets(&net, 1), vec![net.id(2)]);
    net.link(1, 3, true);
    net.run_until(t0 + 3 * SEC);
    assert!(net.delivered(3).contains(&m));
    let mut got = fallback_targets(&net, 1);
    got.sort_unstable();
    let mut want = vec![net.id(2), net.id(3)];
    want.sort_unstable();
    assert_eq!(got, want);
}

#[test]
fn a_publisher_that_never_learned_the_subscribers_has_no_fallback() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    net.subscribe(2, T);
    net.cut_from_hubs(1, false);
    net.cut_from_hubs(2, false);
    net.publish(1, T, b"x");
    assert_eq!(net.count(ty::MEMBER_PUSH), 0);
}

#[test]
fn a_member_push_with_a_forged_body_is_rejected() {
    let mut net = world();
    for i in 1..=4 {
        net.cut_from_hubs(i, false);
    }
    net.filter = Some(Box::new(|_, _, b| {
        if b[4] == ty::MEMBER_PUSH {
            let last = b.len() - 1;
            b[last] ^= 1;
        }
        true
    }));
    net.publish(1, T, b"late");
    assert_eq!(net.delivered(2).len(), 1, "only the warm-up message");
}

/// A join hint is kept beside the list of a hub: node 4 subscribed while the publisher was cut off, so no hub list
/// the publisher holds names it; hinted, it is reached with every hub down, as well as the listed subscribers.
#[test]
fn a_hinted_node_is_reached_when_no_hub_is_though_a_hubs_list_was_held() {
    let mut net = world();
    net.cut_from_hubs(1, false);
    net.subscribe(4, T);
    for i in 2..=4 {
        net.cut_from_hubs(i, false);
    }
    let four = net.id(4);
    assert!(net.nodes[1].t.hint(T, &four));
    let m = net.publish(1, T, b"late");
    assert!(net.delivered(4).contains(&m), "the hinted node was not reached");
    assert!(net.delivered(2).contains(&m) && net.delivered(3).contains(&m));
}
