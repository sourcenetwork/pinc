//! The signed head travels with a delivered message when the node keeps heads: the envelope built from the topic, the
//! head and the body verifies offline and names the publisher, also for a message that was held first; with it off
//! the head is empty and the hold keeps what it kept before.
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

use common::{ALGS, Ev, Net, SEC};
use vinc_broadcast::Limits;
use vinc_broadcast::envelope::{Envelope, verify_bytes};
use vinc_crypto::IdentityAlg;

const T: &[u8] = b"env";

fn keeping(on: bool) -> Limits {
    Limits {
        keep_heads: on,
        ..Limits::default()
    }
}

/// Hub 0, publisher 1, subscriber 2 who answers access checks by hand.
fn world(alg: IdentityAlg, on: bool) -> Net {
    let mut net = Net::with_limits(&[alg; 3], 1, SEC, keeping(on));
    for i in 1..3 {
        net.attach(i);
    }
    net.nodes[2].auto_acp = None;
    net.subscribe(2, T);
    net
}

fn heard(net: &Net, i: usize) -> Vec<(Vec<u8>, Vec<u8>, Vec<u8>)> {
    net.events(i)
        .iter()
        .filter_map(|e| match e {
            Ev::Msg { topic, body, head, .. } => Some((topic.clone(), head.clone(), body.clone())),
            _ => None,
        })
        .collect()
}

fn answer_all(net: &mut Net) {
    let checks: Vec<u32> = net
        .events(2)
        .iter()
        .filter_map(|e| if let Ev::Acp { id, .. } = e { Some(*id) } else { None })
        .collect();
    for id in checks {
        let now = net.now;
        let n = &mut net.nodes[2];
        n.t.acp_answer(&mut n.h, now, id, true);
    }
    net.pump();
}

fn check(net: &Net, alg: IdentityAlg) {
    let got = heard(net, 2);
    assert_eq!(got.len(), 1, "{alg:?}");
    let (topic, head, body) = &got[0];
    assert!(!head.is_empty(), "{alg:?}");
    let mut bytes = Vec::new();
    Envelope { topic, head, body }.encode_into(&mut bytes);
    let v = verify_bytes(&bytes).unwrap();
    assert_eq!(
        (v.origin, v.topic, v.payload, v.alg),
        (&net.id(1), T, &b"hello"[..], alg)
    );
}

#[test]
fn a_delivered_message_carries_a_head_that_makes_a_verifying_envelope() {
    for alg in ALGS {
        let mut net = Net::with_limits(&[alg; 3], 1, SEC, keeping(true));
        for i in 1..3 {
            net.attach(i);
        }
        net.subscribe(2, T);
        net.publish(1, T, b"hello");
        net.advance(SEC);
        check(&net, alg);
    }
}

#[test]
fn a_message_held_for_the_access_check_keeps_its_head() {
    for alg in ALGS {
        let mut net = world(alg, true);
        net.publish(1, T, b"hello");
        assert!(heard(&net, 2).is_empty());
        answer_all(&mut net);
        check(&net, alg);
    }
}

#[test]
fn a_message_held_for_the_floors_keeps_its_head() {
    let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 4], 2, SEC, keeping(true));
    for i in 2..4 {
        net.attach(i);
    }
    net.subscribe(3, T);
    net.restart(3, 10 * SEC);
    net.set_primary(3, 0);
    net.link(3, 1, false);
    net.attach_to(3, 0);
    net.subscribe(3, T);
    net.publish(2, T, b"hello");
    net.run_until(12 * SEC);
    assert!(heard(&net, 3).is_empty(), "held until hub 1 reports its floor");
    net.link(3, 1, true);
    net.attach_to(3, 1);
    net.run_until(13 * SEC);
    let got = heard(&net, 3);
    assert_eq!(got.len(), 1);
    let (topic, head, body) = &got[0];
    let mut bytes = Vec::new();
    Envelope { topic, head, body }.encode_into(&mut bytes);
    let v = verify_bytes(&bytes).unwrap();
    assert_eq!((v.origin, v.topic, v.payload), (&net.id(2), T, &b"hello"[..]));
}

#[test]
fn the_hold_charges_the_head_only_when_heads_are_kept() {
    let mut held = [0usize; 2];
    for (k, on) in [false, true].into_iter().enumerate() {
        let mut net = world(IdentityAlg::Ed25519, on);
        net.publish(1, T, b"hello");
        held[k] = net.nodes[2].t.held_bytes();
        answer_all(&mut net);
        assert_eq!(net.nodes[2].t.held_bytes(), 0);
        if !on {
            assert!(heard(&net, 2)[0].1.is_empty(), "no head unless kept");
        }
    }
    let topic_and_body = 1 + T.len() + b"hello".len();
    assert_eq!(
        held[0], topic_and_body,
        "what is held without heads is the topic and the body"
    );
    // mid 8, origin 32, algorithm 1, signature 64, flag 1, length 4, timestamp 12.
    assert_eq!(held[1], topic_and_body + 122, "an Ed25519 head is 122 bytes");
}
