//! The steady path allocates nothing: once a topic's tables exist, a hub that verifies, logs and pushes a message, a
//! member that receives and delivers one, and a publisher that signs, sends and gets its acknowledgement make no
//! allocation, and neither does a timer pass over warm tables.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::cast_possible_truncation
)]

use vinc_broadcast::wire::ty;
use vinc_broadcast::{Config, Event, Host, Lane, Topics};
use vinc_crypto::{IdentityAlg, Keypair};
use vinc_membership::{Frame, NodeId};
use vinc_tests::measure;

vinc_tests::install_counting_allocator!();

const T: &[u8] = b"alloc";
const SEC: u64 = 1_000_000_000;

fn kp(alg: IdentityAlg, tag: u8) -> Keypair {
    Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap()
}

/// A host that counts what it is asked and keeps the frames it is told to keep.
#[derive(Default)]
struct Sink {
    sent: u64,
    delivered: u64,
    acked: u64,
    kept: Vec<Vec<u8>>,
    keep_to: Option<NodeId>,
    wall: u64,
}

impl Host for Sink {
    fn send(&mut self, peer: &NodeId, _lane: Lane, frame: &[u8]) -> bool {
        self.sent += 1;
        if self.keep_to == Some(*peer) {
            self.kept.push(frame.to_vec());
        }
        true
    }
    fn send_member(&mut self, _peer: &NodeId, _frame: &[u8]) -> bool {
        true
    }
    fn hub_up(&self, _hub: &NodeId) -> bool {
        true
    }
    fn in_view(&self, _member: &NodeId) -> bool {
        true
    }
    fn wall_ms(&self) -> u64 {
        self.wall
    }
    fn event(&mut self, event: Event<'_>) {
        match event {
            Event::Message { .. } => self.delivered += 1,
            Event::PublishAcked { .. } => self.acked += 1,
            _ => {}
        }
    }
}

struct World {
    hub: Topics,
    hub_h: Sink,
    member: Topics,
    member_h: Sink,
    publisher: Topics,
    pub_h: Sink,
    hub_id: NodeId,
    member_id: NodeId,
    pub_id: NodeId,
    now: u64,
}

fn world(alg: IdentityAlg) -> World {
    let (hk, mk, pk) = (kp(alg, 1), kp(alg, 2), kp(alg, 3));
    let (hub_id, member_id, pub_id) = (hk.node_id().bytes, mk.node_id().bytes, pk.node_id().bytes);
    let hubs = [hub_id];
    let cfg = |me, is_hub| Config {
        me,
        is_hub,
        hubs: &hubs,
        incarnation: 1 << 16,
        trace: false,
        limits: vinc_broadcast::Limits::default(),
        map_seed: 0x5eed,
    };
    let now = SEC;
    let wall = 1_700_000_000_000;
    let mut w = World {
        hub: Topics::start(&cfg(hub_id, true), Box::new(hk), now, wall).unwrap(),
        hub_h: Sink {
            wall,
            ..Sink::default()
        },
        member: Topics::start(&cfg(member_id, false), Box::new(mk), now, wall).unwrap(),
        member_h: Sink {
            wall,
            ..Sink::default()
        },
        publisher: Topics::start(&cfg(pub_id, false), Box::new(pk), now, wall).unwrap(),
        pub_h: Sink {
            wall,
            ..Sink::default()
        },
        hub_id,
        member_id,
        pub_id,
        now,
    };
    // Both members attach: the hub's floor reaches them, so they are not holding messages for it.
    let mut floor = [0u8; 4096];
    for who in [member_id, pub_id] {
        let n = w.hub.floor(&who, &mut floor);
        let (t, h) = if who == member_id {
            (&mut w.member, &mut w.member_h)
        } else {
            (&mut w.publisher, &mut w.pub_h)
        };
        t.frame(h, now, &hub_id, ty::FLOOR, &[], &floor[..n]);
        t.primary_changed(h, now, None, &hub_id);
    }
    w.member.subscribe(&mut w.member_h, now, T).unwrap();
    // The hub learns the subscriber from the SUB the member sent, and a second subscriber (a stand-in id).
    w.hub
        .frame(&mut w.hub_h, now, &member_id, ty::SUB, T, &(wall).to_be_bytes());
    w.hub
        .frame(&mut w.hub_h, now, &[9u8; 32], ty::SUB, T, &wall.to_be_bytes());
    // The member's access check is answered and stays valid for the whole run.
    w
}

/// The (type, topic, rest) of a frame the sink kept.
fn parts(frame: &[u8]) -> (u8, Vec<u8>, Vec<u8>) {
    let Ok(Some((Frame::Other(o), _))) = Frame::read(frame) else {
        unreachable!("not a topic frame");
    };
    (o.ty, o.topic.to_vec(), o.rest.to_vec())
}

/// Run the steady paths with `alg` and return the allocations of each: the hub, the member, and the publisher.
fn steady(alg: IdentityAlg, warm: usize, run: usize) -> [u64; 3] {
    // First, with no one counting: capture the frames a publisher sends the hub, and the frames the hub pushes.
    let mut w = world(alg);
    w.pub_h.keep_to = Some(w.hub_id);
    let mut mids = Vec::new();
    for i in 0..warm + run {
        let body = [i as u8; 100];
        mids.push(w.publisher.publish(&mut w.pub_h, w.now, T, &body).unwrap());
    }
    let publish_frames: Vec<(u8, Vec<u8>, Vec<u8>)> = w.pub_h.kept.iter().map(|f| parts(f)).collect();
    assert_eq!(publish_frames.len(), warm + run);
    w.hub_h.keep_to = Some(w.member_id);
    for (ty_, topic, rest) in &publish_frames {
        w.hub.frame(&mut w.hub_h, w.now, &w.pub_id, *ty_, topic, rest);
    }
    let pushed: Vec<(u8, Vec<u8>, Vec<u8>)> = w.hub_h.kept.iter().map(|f| parts(f)).collect();
    assert_eq!(pushed.len(), warm + run);

    // The hub, on fresh state: warm on the first frames, then count the rest. Each message is verified, logged,
    // pushed to two subscribers and acknowledged.
    let mut w = world(alg);
    let setup_sent = w.hub_h.sent;
    for (ty_, topic, rest) in publish_frames.iter().take(warm) {
        w.hub.frame(&mut w.hub_h, w.now, &w.pub_id, *ty_, topic, rest);
    }
    let hub_alloc = measure(|| {
        for (ty_, topic, rest) in publish_frames.iter().skip(warm) {
            w.hub.frame(&mut w.hub_h, w.now, &w.pub_id, *ty_, topic, rest);
        }
    })
    .count();
    assert_eq!(w.hub.log_len(T), warm + run);
    assert_eq!(
        (w.hub_h.sent - setup_sent) as usize,
        (warm + run) * 3 + 1,
        "two pushes and one acknowledgement each, and the subscriber set told once to the new publisher"
    );

    // The member: the first message raises the access check, which is answered; then the pushes are delivered.
    let (t0, topic0, rest0) = &pushed[0];
    w.member.frame(&mut w.member_h, w.now, &w.hub_id, *t0, topic0, rest0);
    w.member.acp_answer(&mut w.member_h, w.now, 1, true);
    assert_eq!(w.member_h.delivered, 1);
    for (ty_, topic, rest) in pushed.iter().take(warm).skip(1) {
        w.member.frame(&mut w.member_h, w.now, &w.hub_id, *ty_, topic, rest);
    }
    let member_alloc = measure(|| {
        for (ty_, topic, rest) in pushed.iter().skip(warm) {
            w.member.frame(&mut w.member_h, w.now, &w.hub_id, *ty_, topic, rest);
        }
    })
    .count();
    assert_eq!(w.member_h.delivered as usize, warm + run, "every message was delivered");

    // The publisher: sign, send, pend, and take the acknowledgement, over and over.
    for i in 0..4 {
        let m = w.publisher.publish(&mut w.pub_h, w.now, T, &[i; 100]).unwrap();
        w.publisher.frame(&mut w.pub_h, w.now, &w.hub_id, ty::PACK, &[], &m);
    }
    let acked = w.pub_h.acked;
    let publish_alloc = measure(|| {
        for i in 0..run {
            let m = w.publisher.publish(&mut w.pub_h, w.now, T, &[i as u8; 100]).unwrap();
            w.publisher.frame(&mut w.pub_h, w.now, &w.hub_id, ty::PACK, &[], &m);
        }
    })
    .count();
    assert_eq!((w.pub_h.acked - acked) as usize, run);
    assert_eq!(w.publisher.pending_len(), 0);
    [hub_alloc, member_alloc, publish_alloc]
}

#[test]
fn the_steady_path_allocates_nothing_with_ed25519() {
    assert_eq!(steady(IdentityAlg::Ed25519, 16, 64), [0, 0, 0]);
}

#[test]
fn the_steady_path_allocates_nothing_with_p256() {
    assert_eq!(steady(IdentityAlg::EcdsaP256, 16, 64), [0, 0, 0]);
}

#[test]
fn a_timer_pass_over_warm_tables_allocates_nothing() {
    let mut w = world(IdentityAlg::Ed25519);
    w.pub_h.keep_to = None;
    for i in 0..16u8 {
        w.publisher.publish(&mut w.pub_h, w.now, T, &[i; 10]).unwrap();
    }
    w.hub.on_timer(&mut w.hub_h, w.now);
    w.member.on_timer(&mut w.member_h, w.now);
    let n = measure(|| {
        for k in 1..=20u64 {
            let t = w.now + k * SEC;
            w.hub.on_timer(&mut w.hub_h, t);
            w.member.on_timer(&mut w.member_h, t);
            w.publisher.on_timer(&mut w.pub_h, t);
            let _ = (
                w.hub.poll_timeout(),
                w.member.poll_timeout(),
                w.publisher.poll_timeout(),
            );
        }
    })
    .count();
    assert_eq!(n, 0);
}

#[test]
fn the_steady_path_allocates_nothing_with_the_post_quantum_algorithms() {
    assert_eq!(steady(IdentityAlg::MlDsa65, 3, 6), [0, 0, 0]);
    assert_eq!(steady(IdentityAlg::Hybrid, 3, 6), [0, 0, 0]);
}
