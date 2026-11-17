//! The steady path allocates nothing: once a topic's tables exist, a hub that verifies, logs and pushes a message, a
//! member that receives and delivers one, and a publisher that signs, sends and gets its acknowledgement make no
//! allocation, and neither does a timer pass over warm tables.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::cast_possible_truncation
)]

use vinc_broadcast::envelope::EnvelopeRef;
use vinc_broadcast::wire::{Head, ty};
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

fn world(alg: IdentityAlg, keep_heads: bool) -> World {
    let (hk, mk, pk) = (kp(alg, 1), kp(alg, 2), kp(alg, 3));
    let (hub_id, member_id, pub_id) = (hk.node_id().bytes, mk.node_id().bytes, pk.node_id().bytes);
    let hubs = [hub_id];
    let cfg = |me, is_hub| Config {
        me,
        is_hub,
        hubs: &hubs,
        incarnation: 1 << 16,
        trace: false,
        limits: vinc_broadcast::Limits {
            keep_heads,
            ..vinc_broadcast::Limits::default()
        },
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
fn steady(alg: IdentityAlg, warm: usize, run: usize, keep_heads: bool) -> [u64; 3] {
    // First, with no one counting: capture the frames a publisher sends the hub, and the frames the hub pushes.
    let mut w = world(alg, keep_heads);
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
    let mut w = world(alg, keep_heads);
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
    assert_eq!(steady(IdentityAlg::Ed25519, 16, 64, false), [0, 0, 0]);
}

#[test]
fn the_steady_path_allocates_nothing_with_p256() {
    assert_eq!(steady(IdentityAlg::EcdsaP256, 16, 64, false), [0, 0, 0]);
}

#[test]
fn a_timer_pass_over_warm_tables_allocates_nothing() {
    let mut w = world(IdentityAlg::Ed25519, false);
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
    assert_eq!(steady(IdentityAlg::MlDsa65, 3, 6, false), [0, 0, 0]);
    assert_eq!(steady(IdentityAlg::Hybrid, 3, 6, false), [0, 0, 0]);
}

#[test]
fn the_steady_path_allocates_nothing_with_heads_kept() {
    assert_eq!(steady(IdentityAlg::Ed25519, 16, 64, true), [0, 0, 0]);
    assert_eq!(steady(IdentityAlg::EcdsaP256, 16, 64, true), [0, 0, 0]);
}

#[test]
fn an_envelope_is_built_in_one_allocation_and_verified_in_none() {
    for alg in [
        IdentityAlg::Ed25519,
        IdentityAlg::EcdsaP256,
        IdentityAlg::MlDsa65,
        IdentityAlg::Hybrid,
    ] {
        let mut w = world(alg, true);
        w.pub_h.keep_to = Some(w.hub_id);
        w.publisher.publish(&mut w.pub_h, w.now, T, &[7u8; 100]).unwrap();
        let (_, topic, rest) = parts(&w.pub_h.kept[0]);
        let (_, body) = Head::parse(&rest).unwrap();
        let head = &rest[..rest.len() - body.len()];
        let mut owned = None;
        let built = measure(|| owned = Some(EnvelopeRef::topic(&topic, head, body).into_owned())).count();
        assert_eq!(built, 1, "{alg:?} building");
        let owned = owned.unwrap();
        let mut verified = false;
        let checked = measure(|| verified = std::hint::black_box(&owned).verify().is_ok()).count();
        assert!(verified, "{alg:?} the envelope verifies");
        assert_eq!(checked, 0, "{alg:?} verifying");
    }
}

/// The frames the hub pushes to the member for `n` messages the publisher signs.
fn pushed_frames(alg: IdentityAlg, n: usize, keep_heads: bool) -> Vec<(u8, Vec<u8>, Vec<u8>)> {
    let mut w = world(alg, keep_heads);
    w.pub_h.keep_to = Some(w.hub_id);
    for i in 0..n {
        w.publisher.publish(&mut w.pub_h, w.now, T, &[i as u8; 100]).unwrap();
    }
    let sent: Vec<_> = w.pub_h.kept.iter().map(|f| parts(f)).collect();
    w.hub_h.keep_to = Some(w.member_id);
    for (ty_, topic, rest) in &sent {
        w.hub.frame(&mut w.hub_h, w.now, &w.pub_id, *ty_, topic, rest);
    }
    w.hub_h.kept.iter().map(|f| parts(f)).collect()
}

/// Two messages wait for one access answer, which releases both: the allocations of that, after one earlier message
/// went through the same steps so that the tables the check and its verdict use exist.
fn access_hold(alg: IdentityAlg, keep_heads: bool) -> u64 {
    let pushed = pushed_frames(alg, 3, keep_heads);
    let mut w = world(alg, keep_heads);
    let (t0, topic0, rest0) = &pushed[0];
    w.member.frame(&mut w.member_h, w.now, &w.hub_id, *t0, topic0, rest0);
    w.member.acp_answer(&mut w.member_h, w.now, 1, true);
    assert_eq!(w.member_h.delivered, 1);
    // The verdict lapsed: the next messages are held again.
    let later = w.now + 31 * SEC;
    let n = measure(|| {
        for (ty_, topic, rest) in &pushed[1..] {
            w.member.frame(&mut w.member_h, later, &w.hub_id, *ty_, topic, rest);
        }
        assert!(w.member.held_bytes() > 0, "both messages wait for the answer");
        w.member.acp_answer(&mut w.member_h, later, 2, true);
    })
    .count();
    assert_eq!(w.member_h.delivered, 3, "{alg:?} both held messages were delivered");
    assert_eq!(w.member.held_bytes(), 0);
    n
}

/// Two messages wait for the replay floors; the wait runs out and they are offered again, into the access hold: the
/// allocations of holding and releasing them.
fn floor_hold(alg: IdentityAlg, keep_heads: bool) -> u64 {
    let pushed = pushed_frames(alg, 2, keep_heads);
    let w = world(alg, keep_heads);
    let cfg = Config {
        me: w.member_id,
        is_hub: false,
        hubs: &[w.hub_id],
        incarnation: 1 << 16,
        trace: false,
        limits: vinc_broadcast::Limits {
            keep_heads,
            ..vinc_broadcast::Limits::default()
        },
    };
    let wall = 1_700_000_000_000;
    let mut m = Topics::start(&cfg, Box::new(kp(alg, 2)), w.now, wall).unwrap();
    let mut h = Sink {
        wall,
        ..Sink::default()
    };
    m.subscribe(&mut h, w.now, T).unwrap();
    let n = measure(|| {
        for (ty_, topic, rest) in &pushed {
            m.frame(&mut h, w.now, &w.hub_id, *ty_, topic, rest);
        }
        assert!(m.held_bytes() > 0, "both messages wait for the floors");
        m.on_timer(&mut h, w.now + 16 * SEC);
    })
    .count();
    // The offered messages now wait for the access answer (its first verdict makes the table that holds it).
    assert!(m.held_bytes() > 0);
    m.acp_answer(&mut h, w.now + 16 * SEC, 1, true);
    assert_eq!(h.delivered, 2, "{alg:?} both held messages were delivered");
    assert_eq!(m.held_bytes(), 0);
    n
}

#[test]
fn a_held_and_released_message_allocates_nothing() {
    for alg in [IdentityAlg::Ed25519, IdentityAlg::Hybrid] {
        for keep_heads in [false, true] {
            assert_eq!(
                access_hold(alg, keep_heads),
                0,
                "{alg:?} heads {keep_heads}: the access hold"
            );
            assert_eq!(
                floor_hold(alg, keep_heads),
                0,
                "{alg:?} heads {keep_heads}: the floor hold"
            );
        }
    }
}

/// The bytes a node requests at start, and the resident memory it grows by.
fn start_cost(limits: vinc_broadcast::Limits) -> (u64, i64) {
    let key = kp(IdentityAlg::Ed25519, 1);
    let cfg = Config {
        me: key.node_id().bytes,
        is_hub: false,
        hubs: &[],
        incarnation: 1 << 16,
        trace: false,
        limits,
    };
    let resident = || {
        let s = std::fs::read_to_string("/proc/self/statm").unwrap();
        s.split_whitespace().nth(1).unwrap().parse::<i64>().unwrap() * 4096
    };
    let r0 = resident();
    let mut started = None;
    let bytes = measure(|| started = Some(Topics::start(&cfg, Box::new(key), 0, 0).unwrap())).bytes;
    let grown = resident() - r0;
    drop(started);
    (bytes, grown)
}

/// The hold slots are one block made at start and left unwritten: the bytes it asks for are the slots', and the
/// resident memory does not grow by them.
#[test]
fn the_hold_slots_are_reserved_at_start_and_not_touched() {
    use vinc_broadcast::consts::{FHOLD_MAX, HELD_MAX};
    use vinc_broadcast::wire::MAX_HEAD;
    for keep_heads in [false, true] {
        let limits = |hold_bytes| vinc_broadcast::Limits {
            keep_heads,
            hold_bytes,
            ..vinc_broadcast::Limits::default()
        };
        let (full, grown) = start_cost(limits(None));
        let (empty, _) = start_cost(limits(Some(0)));
        let slot = 1 + 255 + if keep_heads { MAX_HEAD } else { 0 } + 65_536;
        // The slots and the stage that holds one entry while it is offered again.
        let reserved = ((HELD_MAX + FHOLD_MAX + 1) * slot) as u64;
        eprintln!("heads {keep_heads}: reserved {reserved} bytes, resident growth at start {grown}");
        assert_eq!(full - empty, reserved, "heads {keep_heads}");
        assert!(grown < 1 << 20, "heads {keep_heads}: the start touched {grown} bytes");
    }
    // The smallest configuration the limits allow: a body of one byte.
    let tiny = vinc_broadcast::Limits {
        max_body: 1,
        log_bytes: MAX_HEAD + 1,
        ..vinc_broadcast::Limits::default()
    };
    let (full, _) = start_cost(tiny);
    let (empty, _) = start_cost(vinc_broadcast::Limits {
        hold_bytes: Some(0),
        ..tiny
    });
    eprintln!("smallest: reserved {} bytes", full - empty);
    assert_eq!(full - empty, ((HELD_MAX + FHOLD_MAX + 1) * (1 + 255 + 1)) as u64);
}
