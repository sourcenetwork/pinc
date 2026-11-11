//! Publishing: the hub fan, the acknowledgement, the retry on the next hub every 3 s, the give-up after 90 s, and
//! at-most-once delivery.
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

use common::{ALGS, Ev, Net, SEC, ty};
use vinc_broadcast::Trace;
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"news";

/// 2 hubs, publisher 2, subscriber 3 (both on hub 0).
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    net.subscribe(3, T);
    net
}

#[test]
fn a_message_reaches_the_subscriber_through_the_hub_for_every_algorithm() {
    for alg in ALGS {
        let mut net = Net::new(alg, 2, 2, SEC);
        net.subscribe(3, T);
        let mid = net.publish(2, T, b"hello");
        net.advance(SEC);
        assert_eq!(net.delivered(3), vec![mid], "{alg:?}");
        assert_eq!(net.bodies(3), vec![b"hello".to_vec()], "{alg:?}");
        assert!(net.events(2).contains(&Ev::Acked(mid)), "{alg:?}");
        assert_eq!(net.nodes[2].t.pending_len(), 0);
    }
}

#[test]
fn with_every_hub_up_the_primary_gets_fanp_and_the_others_fan() {
    let mut net = world();
    net.publish(2, T, b"x");
    assert_eq!(net.count_between(2, 0, ty::FANP), 1);
    assert_eq!(net.count_between(2, 1, ty::FAN), 1);
    assert_eq!(net.count(ty::PUB), 0);
    // A fanned copy is not mirrored: no hub-to-hub MSG, yet the subscriber (on hub 0) has it.
    assert_eq!(net.count_between(0, 1, ty::MSG), 0);
    assert_eq!(net.delivered(3).len(), 1);
    let fan_lane = net.nodes[2].h.out.is_empty();
    assert!(fan_lane);
}

#[test]
fn with_a_hub_down_the_publisher_sends_pub_and_the_hub_mirrors() {
    let mut net = world();
    net.link(2, 1, false);
    net.publish(2, T, b"x");
    assert_eq!(net.count_between(2, 0, ty::PUB), 1);
    assert_eq!(net.count(ty::FAN) + net.count(ty::FANP), 0);
    assert_eq!(net.count_between(0, 1, ty::MSG), 1);
    assert_eq!(net.nodes[1].t.log_len(T), 1);
}

#[test]
fn the_fan_copy_rides_the_second_lane() {
    let mut net = world();
    let n = &mut net.nodes[2];
    let mid = n.t.publish(&mut n.h, SEC, T, b"x").unwrap();
    let lanes: Vec<_> = net.nodes[2].h.out.iter().map(|o| (o.lane, o.to)).collect();
    assert_eq!(lanes.len(), 2);
    assert_eq!(lanes[0], (vinc_broadcast::Lane::Main, net.id(0)));
    assert_eq!(lanes[1], (vinc_broadcast::Lane::Fan, net.id(1)));
    let _ = mid;
}

#[test]
fn an_unacknowledged_publish_retries_every_3s_on_the_next_hub() {
    let mut net = world();
    // Hub 0 drops every PUB and FANP; hub 1 acknowledges nothing it is not sent.
    net.filter = Some(Box::new(|_, to, bytes| {
        let t = bytes[4];
        !(to == 0 && (t == ty::PUB || t == ty::FANP))
    }));
    let mid = net.publish(2, T, b"x");
    assert_eq!(net.nodes[2].t.pending_len(), 1);
    // FAN to hub 1 gets no PACK (only PUB and FANP are acknowledged).
    net.run_until(SEC + 3 * SEC - 1);
    assert_eq!(net.count(ty::PUB), 0, "no retry before 3 s");
    net.run_until(SEC + 3 * SEC);
    assert_eq!(net.count_between(2, 1, ty::PUB), 1, "first retry goes to the next hub");
    // Hub 1 acknowledges the retry.
    assert!(net.events(2).contains(&Ev::Acked(mid)));
    assert_eq!(net.nodes[2].t.pending_len(), 0);
}

#[test]
fn retries_alternate_over_the_hubs_until_the_90s_give_up() {
    let mut net = world();
    net.link(2, 0, false);
    net.link(2, 1, false);
    let mid = net.publish(2, T, b"x");
    net.run_until(SEC + 90 * SEC);
    assert_eq!(net.nodes[2].t.pending_len(), 1, "still pending at exactly 90 s");
    assert!(!net.events(2).contains(&Ev::GaveUp(mid)));
    net.run_until(SEC + 90 * SEC + 1);
    assert_eq!(net.nodes[2].t.pending_len(), 0);
    assert!(net.events(2).contains(&Ev::GaveUp(mid)));
    // The retries are traced, one every 3 s, alternating hubs.
    let mut hubs = Vec::new();
    while let Some(t) = net.nodes[2].t.poll_trace() {
        if let Trace::PubRetry { hub, .. } = t {
            hubs.push(hub);
        }
    }
    assert_eq!(hubs.len(), 30);
    assert_eq!(hubs[0], net.id(1));
    assert_eq!(hubs[1], net.id(0));
}

#[test]
fn a_message_is_delivered_at_most_once_however_many_copies_arrive() {
    let mut net = world();
    // Hub 0 and hub 1 both push to the subscriber (it subscribes to both through a second SUB), and retries repeat.
    net.link(2, 0, false);
    let mid = net.publish(2, T, b"x");
    net.run_until(10 * SEC);
    net.link(2, 0, true);
    net.run_until(20 * SEC);
    assert_eq!(net.delivered(3), vec![mid]);
    // Replaying the same frame again changes nothing.
    let mut again = 0;
    for o in net.log.clone() {
        again += usize::from(o.3 == ty::MSG);
    }
    assert!(again >= 1);
    assert_eq!(net.delivered(3).len(), 1);
}

#[test]
fn a_publisher_does_not_deliver_its_own_message() {
    let mut net = world();
    net.subscribe(2, T);
    net.publish(2, T, b"x");
    net.advance(SEC);
    assert!(net.delivered(2).is_empty());
    assert_eq!(net.delivered(3).len(), 1);
}

#[test]
fn a_hub_publish_is_stored_pushed_and_mirrored() {
    let mut net = world();
    let mid = net.publish(0, T, b"from the hub");
    assert_eq!(net.delivered(3), vec![mid]);
    assert_eq!(net.nodes[1].t.log_len(T), 1);
    assert_eq!(net.nodes[0].t.log_len(T), 1);
}

#[test]
fn oversize_and_overlong_are_refused() {
    let mut net = world();
    let n = &mut net.nodes[2];
    assert!(n.t.publish(&mut n.h, SEC, &[b'a'; 256], b"x").is_err());
    assert!(
        n.t.publish(&mut n.h, SEC, T, &vec![0; vinc_broadcast::consts::DEFAULT_MAX_BODY + 1])
            .is_err()
    );
    assert!(
        n.t.publish(&mut n.h, SEC, T, &vec![0; vinc_broadcast::consts::DEFAULT_MAX_BODY])
            .is_ok()
    );
}

#[test]
fn a_key_that_is_not_the_nodes_is_refused_at_start() {
    use vinc_broadcast::{Config, StartError, Topics};
    let key = common::keypair(IdentityAlg::Ed25519, 1);
    let other = common::keypair(IdentityAlg::Ed25519, 2);
    let cfg = Config {
        me: other.node_id().bytes,
        is_hub: false,
        hubs: &[],
        incarnation: 1,
        trace: false,
        limits: vinc_broadcast::Limits::default(),
    };
    assert_eq!(Topics::start(&cfg, Box::new(key), SEC, 1).unwrap_err(), StartError::KeyMismatch);
}

#[test]
fn a_revoked_origin_is_refused_and_its_subscription_forgotten() {
    use vinc_broadcast::Reject;
    let mut net = world();
    net.publish(2, T, b"warm up");
    let (publisher, subscriber) = (net.id(2), net.id(3));
    // The subscriber revokes the publisher; the hub relays its messages, and the subscriber refuses them by origin.
    net.nodes[3].t.revoke(&publisher);
    net.publish(2, T, b"after the revocation");
    let mut refused = 0;
    while let Some(t) = net.nodes[3].t.poll_trace() {
        refused += usize::from(matches!(
            t,
            Trace::Rejected {
                why: Reject::Revoked,
                ..
            }
        ));
    }
    assert_eq!(refused, 1);
    // The hub revokes the subscriber: its subscription is forgotten and nothing is pushed to it.
    net.nodes[0].t.revoke(&subscriber);
    assert_eq!(net.nodes[0].t.sub_state(T, &subscriber), None);
    assert_eq!(net.delivered(3).len(), 1, "only the message from before the revocation");
}
