//! A hub acknowledges a publish only for the message it stored under that id: an exact retry is acknowledged without
//! checking the signature again, another message under a taken id is refused and its publisher gives up.
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
use std::rc::Rc;

use common::{Ev, Net, SEC, WALL0, keypair, ty};
use vinc_broadcast::wire::Head;
use vinc_broadcast::{Reject, Trace, auth};
use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_wire::hlc::Hlc;

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
    let (now, from) = (net.now, net.id(from));
    let n = &mut net.nodes[0];
    n.h.tick(now);
    n.t.frame(&mut n.h, now, &from, ty::PUB, T, rest);
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

/// A retry of the stored message is acknowledged with no second signature check: a copy whose signature bytes are
/// damaged but whose origin, body and timestamp are the stored ones is acknowledged and no `BadSignature` is counted.
#[test]
fn an_exact_retry_is_acknowledged_without_a_second_verification() {
    let mut net = Net::new(ALG, 1, 2, SEC);
    let first: Rc<RefCell<Option<Vec<u8>>>> = Rc::default();
    let tap = Rc::clone(&first);
    net.filter = Some(Box::new(move |from, to, bytes| {
        if from == 1 && to == 0 && matches!(bytes.get(4), Some(&ty::PUB | &ty::FANP)) {
            *tap.borrow_mut() = Some(bytes.clone());
        }
        true
    }));
    let mid = net.publish(1, T, b"body");
    net.filter = None;
    assert!(net.events(1).contains(&Ev::Acked(mid)));
    let _ = rejects(&mut net, 0);
    let frame = first.borrow().clone().unwrap();
    let mut rest = frame[6 + T.len()..].to_vec();
    // mid (8) + origin (32) + alg (1) + the signature, which has no key before it for Ed25519.
    rest[8 + 32 + 1 + 3] ^= 1;
    let acks = net.count(ty::PACK);
    hub_gets(&mut net, 1, &rest);
    assert_eq!(net.count(ty::PACK), acks + 1, "the retry is acknowledged");
    let why = rejects(&mut net, 0);
    assert_eq!(
        why,
        vec![Reject::Duplicate],
        "it is a duplicate and its signature is not checked again"
    );
}
