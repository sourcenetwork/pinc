//! A hub acknowledges a publish only for the message it stored under that id, told by the print of its signature,
//! also after the log let the message go: a retry is acknowledged without checking the signature again, another
//! message under a taken id is refused and its publisher gives up.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

use std::cell::{Cell, RefCell};
use std::hash::BuildHasher;
use std::rc::Rc;

use common::{Ev, Net, SEC, WALL0, keypair, ty};
use pinc_broadcast::wire::Head;
use pinc_broadcast::{Limits, Reject, Trace, auth};
use pinc_crypto::IdentityAlg;
use pinc_crypto::identity::MAX_SIGNATURE_LEN;
use pinc_wire::hlc::Hlc;
use rapidhash::quality::SeedableState;

const T: &[u8] = b"taken";
const ALG: IdentityAlg = IdentityAlg::Ed25519;

/// The head and body of a message signed by node `i` of a `Net` under the id `mid`, as a PUB frame carries them.
fn signed(i: usize, mid: [u8; 8], body: &[u8], ts: Hlc) -> Vec<u8> {
    let key = keypair(ALG, u8::try_from(i + 1).unwrap());
    let mut sig = [0u8; MAX_SIGNATURE_LEN];
    let n = auth::sign(&key, T, &mid, body, ts, true, &mut sig).unwrap();
    let id = key.node_id();
    let head = Head {
        mid,
        origin: &id.bytes,
        alg: ALG,
        pk: &[],
        sig: &sig[..n],
        isb: true,
        ts,
    };
    let mut rest = Vec::new();
    head.write(body.len() as u32, &mut rest);
    rest.extend_from_slice(body);
    rest
}

fn hub_gets(net: &mut Net, from: usize, rest: &[u8]) {
    hub_gets_as(net, from, ty::PUB, rest);
}

fn hub_gets_as(net: &mut Net, from: usize, t: u8, rest: &[u8]) {
    let (now, from) = (net.now, net.id(from));
    let n = &mut net.nodes[0];
    n.h.tick(now);
    n.t.frame(&mut n.h, now, &from, t, T, rest);
    net.pump();
}

fn rejects(net: &mut Net, i: usize) -> Vec<Reject> {
    let mut out = Vec::new();
    while let Some(t) = net.nodes[i].t.poll_trace() {
        if let Trace::Rejected { why, .. } = t {
            out.push(why);
        }
    }
    out
}

/// The head and body of a frame as a hub gets them.
fn rest_of(frame: &[u8]) -> Vec<u8> {
    frame[6 + T.len()..].to_vec()
}

/// The first publish of node `i` that reaches hub 0, kept as it was sent.
type Tap = Rc<RefCell<Option<Vec<u8>>>>;

fn tap_first(net: &mut Net, i: usize) -> Tap {
    let first = Tap::default();
    let tap = Rc::clone(&first);
    net.filter = Some(Box::new(move |from, to, bytes| {
        if from == i && to == 0 && matches!(bytes.get(4), Some(&ty::PUB | &ty::FANP)) {
            tap.borrow_mut().get_or_insert_with(|| bytes.clone());
        }
        true
    }));
    first
}

/// Two origins publish different messages under one id. The hub keeps the first and acknowledges only its publisher;
/// the second publisher is not told its message was stored and gives up. Before the fix the hub acknowledged by id.
#[test]
fn a_different_message_under_a_taken_id_is_refused_and_its_publisher_gives_up() {
    let mut net = Net::new(ALG, 1, 2, SEC);
    let hold = Rc::new(Cell::new(true));
    let gate = Rc::clone(&hold);
    net.filter = Some(Box::new(move |from, to, bytes| {
        // A publisher with every hub up sends a FANP; its retries are PUBs.
        !(gate.get() && from == 2 && to == 0 && matches!(bytes.get(4), Some(&ty::PUB | &ty::FANP)))
    }));
    let mid = net.publish(2, T, b"mine");
    let ts = Hlc::new(WALL0 + 1000, 0);
    hub_gets(&mut net, 1, &signed(1, mid, b"rival", ts));
    let _ = rejects(&mut net, 0);
    hold.set(false);
    net.run_until(100 * SEC);
    let why = rejects(&mut net, 0);
    assert!(
        why.contains(&Reject::IdTaken),
        "the hub refuses the second message: {why:?}"
    );
    assert!(
        !net.events(2).contains(&Ev::Acked(mid)),
        "the second publisher is not told it was stored"
    );
    assert!(net.events(2).contains(&Ev::GaveUp(mid)), "its app gets the give-up");
}

/// A retry of the stored message is acknowledged with no second signature check, and a copy whose signature bytes
/// differ is not the stored message: it is refused unverified and not acknowledged.
#[test]
fn a_copy_with_other_signature_bytes_is_refused_unverified() {
    let mut net = Net::new(ALG, 1, 2, SEC);
    let first = tap_first(&mut net, 1);
    let mid = net.publish(1, T, b"body");
    net.filter = None;
    assert!(net.events(1).contains(&Ev::Acked(mid)));
    let _ = rejects(&mut net, 0);
    let mut rest = rest_of(&first.borrow().clone().unwrap());
    let acks = net.count(ty::PACK);
    hub_gets(&mut net, 1, &rest);
    assert_eq!(net.count(ty::PACK), acks + 1, "the exact retry is acknowledged");
    assert_eq!(rejects(&mut net, 0), vec![Reject::Duplicate]);
    // Flip a byte of the signature, found where the head says it is.
    let at = {
        let (head, _) = Head::parse(&rest).unwrap();
        head.sig.as_ptr() as usize - rest.as_ptr() as usize
    };
    rest[at + 3] ^= 1;
    hub_gets(&mut net, 1, &rest);
    assert_eq!(net.count(ty::PACK), acks + 1, "the copy is not acknowledged");
    assert_eq!(
        rejects(&mut net, 0),
        vec![Reject::IdTaken],
        "it is refused and its signature is not checked"
    );
}

/// A hub with an 8 KiB log and two members. Node 1 publishes and its acknowledgement is lost; node 2 then publishes
/// ten messages of 1 KiB, so the log has let the first go. Returns the net and the first message's id.
fn log_let_go() -> (Net, [u8; 8]) {
    let limits = Limits {
        max_body: 1024,
        log_bytes: 8192,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&[ALG; 3], 1, SEC, limits);
    net.attach(1);
    net.attach(2);
    let lost = Rc::new(Cell::new(false));
    net.filter = Some(Box::new(move |from, to, bytes| {
        !(from == 0 && to == 1 && bytes.get(4) == Some(&ty::PACK) && !lost.replace(true))
    }));
    let mid = net.publish(1, T, b"first");
    assert!(!net.events(1).contains(&Ev::Acked(mid)), "its acknowledgement was lost");
    let full = net.nodes[0].t.reject_stats().count(Reject::LogFull);
    for _ in 0..10 {
        net.publish(2, T, &[7u8; 1024]);
    }
    net.filter = None;
    // The ring lets the oldest go first, so a log that holds fewer than the eleven messages published has let `mid` go.
    let held = net.nodes[0].t.log_len(T);
    assert!(held < 11, "the log let the first message go, yet it holds {held} of 11");
    // Every filler was stored: a log that refused the newcomer instead of letting the oldest go would count them.
    assert_eq!(
        net.nodes[0].t.reject_stats().count(Reject::LogFull),
        full,
        "no message was refused for want of room"
    );
    (net, mid)
}

/// The hub stored a message and its acknowledgement was lost; the log then let the message go. The publisher's retry
/// is acknowledged all the same: the hub remembers the print of the signature it stored.
#[test]
fn a_retry_after_the_log_let_the_message_go_is_acknowledged() {
    let (mut net, mid) = log_let_go();
    net.run_until(10 * SEC);
    assert!(
        net.events(1).contains(&Ev::Acked(mid)),
        "the retry was acknowledged: {:?}",
        net.events(1)
    );
}

/// After the log let a message go, another origin's message under its id is refused, not acknowledged.
#[test]
fn a_rival_after_the_log_let_the_message_go_is_refused() {
    let (mut net, mid) = log_let_go();
    let _ = rejects(&mut net, 0);
    let acks = net.count(ty::PACK);
    hub_gets(&mut net, 2, &signed(2, mid, b"rival", Hlc::new(WALL0 + 1000, 0)));
    assert_eq!(rejects(&mut net, 0), vec![Reject::IdTaken]);
    assert_eq!(net.count(ty::PACK), acks, "the rival is not acknowledged");
}

/// A copy that is due no acknowledgement (a FAN) compares nothing: another body under a stored id is a duplicate.
#[test]
fn a_copy_due_no_acknowledgement_is_a_plain_duplicate() {
    let mut net = Net::new(ALG, 1, 2, SEC);
    let mid = net.publish(1, T, b"mine");
    let _ = rejects(&mut net, 0);
    let acks = net.count(ty::PACK);
    hub_gets_as(
        &mut net,
        2,
        ty::FAN,
        &signed(2, mid, b"rival", Hlc::new(WALL0 + 1000, 0)),
    );
    assert_eq!(rejects(&mut net, 0), vec![Reject::Duplicate]);
    assert_eq!(net.count(ty::PACK), acks, "a FAN is never acknowledged");
}

/// A run of ids that share a home slot in the hub's dedupe set is delivered,
/// stored and acknowledged in full: no id is refused for the length of the walk, and the long walks are counted.
#[test]
fn a_long_run_is_delivered_stored_and_acknowledged() {
    let two_step = SeedableState::custom(0x5eed, &pinc_tests::MAP_SECRETS);
    let home = |id: u64| two_step.hash_one(id) & 16383;
    let ids: Vec<u64> = (0u64..).filter(|id| home(*id) == 0).take(140).collect();
    let mut net = Net::new(ALG, 1, 2, SEC);
    net.subscribe(0, T);
    let _ = rejects(&mut net, 0);
    for (k, id) in ids.iter().enumerate() {
        let ts = Hlc::new(WALL0 + 2000 + k as u64, 0);
        hub_gets(&mut net, 1, &signed(1, id.to_le_bytes(), b"x", ts));
    }
    assert_eq!(net.count(ty::PACK), 140, "every message is acknowledged");
    assert_eq!(net.delivered(0).len(), 140, "every message is delivered");
    assert!(rejects(&mut net, 0).is_empty(), "nothing is refused");
    assert!(
        net.nodes[0].t.reject_stats().long_walks() > 0,
        "the long walks are counted"
    );
}

/// A publish at a node that is not a hub is turned away and counted, though no record of it is traced.
#[test]
fn a_frame_from_a_sender_not_allowed_is_counted() {
    let mut net = Net::new(ALG, 1, 2, SEC);
    let first = tap_first(&mut net, 1);
    net.publish(1, T, b"mine");
    let rest = rest_of(&first.borrow().clone().unwrap());
    let (now, from) = (net.now, net.id(1));
    let before = net.nodes[2].t.reject_stats().count(Reject::NotAllowed);
    let n = &mut net.nodes[2];
    n.h.tick(now);
    n.t.frame(&mut n.h, now, &from, ty::PUB, T, &rest);
    assert_eq!(n.t.reject_stats().count(Reject::NotAllowed), before + 1);
}

/// The rejections are counted whether or not the node queues trace records.
#[test]
fn rejects_are_counted_with_tracing_off() {
    let mut net = Net::new(ALG, 1, 2, SEC);
    net.trace = false;
    net.restart(0, 2 * SEC);
    let first = tap_first(&mut net, 1);
    let mid = net.publish(1, T, b"mine");
    let frame = first.borrow().clone().unwrap();
    hub_gets(&mut net, 1, &rest_of(&frame));
    hub_gets(&mut net, 2, &signed(2, mid, b"rival", Hlc::new(WALL0 + 1000, 0)));
    hub_gets(&mut net, 1, &[0u8; 3]);
    let stats = net.nodes[0].t.reject_stats();
    assert_eq!(stats.count(Reject::Duplicate), 1);
    assert_eq!(stats.count(Reject::IdTaken), 1);
    assert_eq!(stats.count(Reject::BadHead), 1);
    assert_eq!(stats.total(), 3);
    assert!(rejects(&mut net, 0).is_empty(), "no trace record is queued");
}
