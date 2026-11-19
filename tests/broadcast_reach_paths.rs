//! The delivery paths under the scope (pinc#86): the catch-up of a subscriber that is behind, the repair after a
//! split heals, and the hub's own application, which is never scoped.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::expect_used)]

#[path = "broadcast_common.rs"]
mod common;
#[path = "broadcast_reach_support.rs"]
mod support;

use common::{Net, SEC};
use support::{T, adj, got, session};
use pinc_broadcast::consts::GAP_EVERY;
use pinc_crypto::IdentityAlg;

#[test]
fn a_subscriber_that_is_behind_catches_up_only_on_its_component() {
    // Hub 0; 1 - 2 hold a session, 3 is alone.
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 1, 2, true);
    adj(&mut net, 3, &[]);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    net.advance(SEC);
    // Subscriber 2's stream at the hub fills while both groups publish.
    let id = net.id(2);
    net.nodes[0].h.full.insert(id);
    let a = net.publish(1, T, b"from its peer");
    let b = net.publish(3, T, b"from outside");
    assert_eq!(net.nodes[0].t.behind_count(T), 1);
    net.nodes[0].h.full.remove(&id);
    let now = net.now;
    let n = &mut net.nodes[0];
    n.t.peer_writable(&mut n.h, now, &id);
    net.pump();
    assert!(got(&net, 2, a), "the catch-up brings its component's message");
    assert!(!got(&net, 2, b), "and not the other group's");
}

#[test]
fn after_a_heal_the_repair_brings_what_the_peer_published_during_the_split() {
    // The repair answers from the graph as it is now: once the session is back, the periodic gap check (which runs
    // while the topic had traffic within GAP_LIVE) offers what the peer published while they were apart within the
    // last GAP_SPAN, as a mesh's anti-entropy would.
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 1, 2, true);
    net.subscribe(1, T);
    net.subscribe(2, T);
    let before = net.publish(1, T, b"before the split");
    assert!(got(&net, 2, before));
    session(&mut net, &mut edges, 1, 2, false);
    let m = net.publish(1, T, b"during the split");
    assert!(!got(&net, 2, m), "apart: not pushed");
    session(&mut net, &mut edges, 1, 2, true);
    net.advance(GAP_EVERY + SEC);
    assert!(got(&net, 2, m), "the gap check repairs it");
}

#[test]
fn a_hub_s_own_application_hears_every_scoped_member_and_its_publishes_reach_them_all() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    adj(&mut net, 1, &[]);
    adj(&mut net, 2, &[]);
    for i in 0..=2 {
        net.subscribe(i, T);
    }
    let m = net.publish(1, T, b"from a scoped member");
    assert!(got(&net, 0, m), "the hub's application hears it");
    assert!(!got(&net, 2, m), "the other member is outside its component");
    let h = net.publish(0, T, b"from the hub");
    assert!(
        got(&net, 1, h) && got(&net, 2, h),
        "a hub's publish reaches every member"
    );
}
