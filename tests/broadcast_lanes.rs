//! Which lane each broadcast frame takes: a frame that answers or pushes to a peer rides the reply lane (with no
//! session it is dropped, never queued behind a dial); a publish, a subscription and the mirror between hubs ride the
//! main lane (a dial may be started for them); the copy for a non-primary hub rides the fan lane.
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
use pinc_broadcast::Lane;
use pinc_crypto::IdentityAlg;

const T: &[u8] = b"news";

/// The lanes of the frames of type `t` from node `from` to node `to`.
fn lanes(net: &Net, from: usize, to: usize, t: u8) -> Vec<Lane> {
    net.lanes
        .iter()
        .filter(|l| l.0 == from && l.1 == to && l.2 == t)
        .map(|l| l.3)
        .collect()
}

/// 2 hubs, publisher 2, subscriber 3 (both on hub 0).
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 2, SEC);
    net.subscribe(3, T);
    net
}

#[test]
fn a_hub_push_and_an_acknowledgement_ride_the_reply_lane_and_a_subscription_the_main_lane() {
    let mut net = world();
    assert_eq!(
        lanes(&net, 3, 0, ty::SUB),
        vec![Lane::Main],
        "a subscription may dial the hub"
    );
    net.publish(2, T, b"x");
    net.advance(SEC);
    assert_eq!(
        lanes(&net, 2, 0, ty::FANP),
        vec![Lane::Main],
        "a publish may dial the hub"
    );
    assert_eq!(lanes(&net, 2, 1, ty::FAN), vec![Lane::Fan]);
    assert_eq!(
        lanes(&net, 0, 3, ty::MSG),
        vec![Lane::Reply],
        "a push never dials the subscriber"
    );
    assert_eq!(
        lanes(&net, 0, 2, ty::PACK),
        vec![Lane::Reply],
        "an acknowledgement never dials the publisher"
    );
}

#[test]
fn the_hub_mirror_rides_the_main_lane() {
    let mut net = world();
    net.link(2, 1, false);
    net.publish(2, T, b"x");
    net.advance(SEC);
    assert_eq!(lanes(&net, 2, 0, ty::PUB), vec![Lane::Main]);
    assert_eq!(
        lanes(&net, 0, 1, ty::MSG),
        vec![Lane::Main],
        "the mirror to the other hub may dial it"
    );
    assert_eq!(lanes(&net, 0, 3, ty::MSG), vec![Lane::Reply]);
}
