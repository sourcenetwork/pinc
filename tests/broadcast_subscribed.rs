//! A member is told once that a hub holds its subscription: when the hub's subscriber set first lists it, again only
//! after it left and joined again, and never for a topic it only publishes to.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::expect_used)]

#[path = "broadcast_common.rs"]
mod common;

use common::{Ev, Net, SEC};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"joined";

fn subscribed(net: &Net, member: usize) -> usize {
    net.events(member)
        .iter()
        .filter(|e| matches!(e, Ev::Subscribed { topic, .. } if topic == T))
        .count()
}

#[test]
fn a_subscriber_is_told_once_that_the_hub_holds_its_subscription() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    assert!(net.events(2).contains(&Ev::Subscribed {
        hub: net.id(0),
        topic: T.to_vec()
    }));
    net.subscribe(1, T);
    assert_eq!(subscribed(&net, 2), 1, "a later subscriber's set does not tell it again");
    assert_eq!(subscribed(&net, 1), 1);
}

#[test]
fn a_message_published_after_the_event_reaches_the_subscriber() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    assert_eq!(subscribed(&net, 2), 1);
    let m = net.publish(1, T, b"after");
    assert_eq!(net.delivered(2), vec![m]);
}

#[test]
fn a_member_that_left_and_joined_again_is_told_again() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    net.unsubscribe(2, T);
    net.subscribe(2, T);
    assert_eq!(subscribed(&net, 2), 2);
}

#[test]
fn a_publisher_that_never_subscribed_is_not_told() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    net.publish(1, T, b"hello");
    net.subscribe(2, b"other");
    assert_eq!(subscribed(&net, 1), 0);
}
