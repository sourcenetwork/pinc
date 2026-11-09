//! A returning member gets its subscriptions back and is told: hold keeps them for the lease, restore makes them
//! live and informs the member, release forgets them; and the machine plugs into membership's broadcast trait.
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

use common::{Ev, Net, NodeHost, SEC, ty};
use vinc_broadcast::Topics;
use vinc_crypto::IdentityAlg;
use vinc_membership::{Broadcast, NodeId};

const T: &[u8] = b"back";

/// Hub 0, publisher 1, subscriber 2.
fn world() -> Net {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, T);
    net
}

fn hold(net: &mut Net, hub: usize, member: usize) {
    let m = net.id(member);
    let n = &mut net.nodes[hub];
    n.t.hold(&mut n.h, &m);
    net.pump();
}

fn restore(net: &mut Net, hub: usize, member: usize) {
    let m = net.id(member);
    let n = &mut net.nodes[hub];
    n.t.restore(&mut n.h, &m);
    net.pump();
}

#[test]
fn a_held_member_is_pushed_nothing_but_keeps_its_subscription() {
    let mut net = world();
    hold(&mut net, 0, 2);
    assert_eq!(net.nodes[0].t.sub_state(T, &net.id(2)), Some(false));
    net.publish(1, T, b"while down");
    assert!(net.delivered(2).is_empty());
    assert_eq!(net.count_between(0, 2, ty::MSG), 0);
}

#[test]
fn a_restore_makes_the_subscription_live_and_tells_the_member() {
    let mut net = world();
    hold(&mut net, 0, 2);
    restore(&mut net, 0, 2);
    assert_eq!(net.nodes[0].t.sub_state(T, &net.id(2)), Some(true));
    assert!(net.events(2).contains(&Ev::Restored {
        hub: net.id(0),
        topic: T.to_vec()
    }));
    assert_eq!(net.count_between(0, 2, ty::RESTORED), 1);
    let m = net.publish(1, T, b"after");
    assert_eq!(net.delivered(2), vec![m], "pushed again with no new SUB");
}

#[test]
fn the_messages_missed_while_held_are_repaired_when_membership_asks_to_resubscribe() {
    let mut net = world();
    hold(&mut net, 0, 2);
    let missed = net.publish(1, T, b"missed");
    restore(&mut net, 0, 2);
    // Membership tells the member the hub restored it: it subscribes again, and the gap is repaired.
    let (hub, now) = (net.id(0), net.now);
    let n = &mut net.nodes[2];
    n.t.resubscribe(&mut n.h, now, &hub);
    net.pump();
    assert_eq!(net.delivered(2), vec![missed]);
}

#[test]
fn a_restore_names_every_topic_the_member_held() {
    let mut net = world();
    net.subscribe(2, b"second");
    hold(&mut net, 0, 2);
    restore(&mut net, 0, 2);
    let topics: Vec<Vec<u8>> = net
        .events(2)
        .iter()
        .filter_map(|e| {
            if let Ev::Restored { topic, .. } = e {
                Some(topic.clone())
            } else {
                None
            }
        })
        .collect();
    assert_eq!(topics, vec![T.to_vec(), b"second".to_vec()]);
}

#[test]
fn restoring_a_member_that_was_not_held_says_nothing() {
    let mut net = world();
    restore(&mut net, 0, 2);
    assert_eq!(net.count(ty::RESTORED), 0);
}

#[test]
fn a_release_forgets_the_subscriptions() {
    let mut net = world();
    hold(&mut net, 0, 2);
    let m = net.id(2);
    let n = &mut net.nodes[0];
    n.t.release(&mut n.h, &m);
    assert_eq!(net.nodes[0].t.sub_state(T, &net.id(2)), None);
    restore(&mut net, 0, 2);
    assert_eq!(net.count(ty::RESTORED), 0);
    net.publish(1, T, b"x");
    assert!(net.delivered(2).is_empty());
}

#[test]
fn a_hold_and_a_release_tell_the_publishers_the_new_subscriber_set() {
    let mut net = world();
    net.publish(1, T, b"warm up");
    net.run_until(2 * SEC);
    assert_eq!(net.nodes[1].t.known_subscribers(T), &[net.id(2)]);
    hold(&mut net, 0, 2);
    assert!(
        net.nodes[1].t.known_subscribers(T).is_empty(),
        "a held member is no longer a target"
    );
    restore(&mut net, 0, 2);
    assert_eq!(net.nodes[1].t.known_subscribers(T), &[net.id(2)]);
    let m = net.id(2);
    let n = &mut net.nodes[0];
    n.t.release(&mut n.h, &m);
    net.pump();
    assert!(net.nodes[1].t.known_subscribers(T).is_empty());
}

/// The membership layer reaches the machine through its `Broadcast` trait; this host forwards each call.
struct Glue {
    t: Topics,
    h: NodeHost,
    now: u64,
}

impl Broadcast for Glue {
    fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize {
        self.t.floor(member, out)
    }
    fn frame(&mut self, from: &NodeId, ty: u8, topic: &[u8], rest: &[u8]) {
        self.t.frame(&mut self.h, self.now, from, ty, topic, rest);
    }
    fn hold(&mut self, member: &NodeId) {
        self.t.hold(&mut self.h, member);
    }
    fn restore(&mut self, member: &NodeId) {
        self.t.restore(&mut self.h, member);
    }
    fn release(&mut self, member: &NodeId) {
        self.t.release(&mut self.h, member);
    }
    fn resubscribe(&mut self, hub: &NodeId) {
        self.t.resubscribe(&mut self.h, self.now, hub);
    }
    fn primary_changed(&mut self, old: Option<&NodeId>, new: &NodeId) {
        self.t.primary_changed(&mut self.h, self.now, old, new);
    }
}

#[test]
fn the_machine_plugs_into_the_membership_broadcast_trait() {
    let mut net = world();
    let (hub_id, member) = (net.id(0), net.id(2));
    // Move the hub's machine behind the trait and drive it the way membership does.
    let hub = net.nodes.remove(0);
    let mut glue = Glue {
        t: hub.t,
        h: hub.h,
        now: net.now,
    };
    let mut body = [0u8; 4096];
    assert!(glue.floor(&member, &mut body) > 0);
    // A SUB frame arrives through `frame`, as membership passes frames it does not own.
    glue.frame(&member, ty::SUB, T, &0u64.to_be_bytes());
    assert_eq!(glue.t.sub_state(T, &member), Some(true));
    glue.hold(&member);
    assert_eq!(glue.t.sub_state(T, &member), Some(false));
    glue.restore(&member);
    assert_eq!(glue.t.sub_state(T, &member), Some(true));
    glue.release(&member);
    assert_eq!(glue.t.sub_state(T, &member), None);
    glue.primary_changed(None, &hub_id);
    assert_eq!(glue.t.primary(), Some(&hub_id));
}
