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

use std::cell::RefCell;
use std::rc::Rc;

use common::{ALGS, Ev, Net, SEC, ty};
use proptest::prelude::*;
use proptest::strategy::ValueTree;
use vinc_broadcast::Limits;
use vinc_broadcast::envelope::{EnvelopeRef, verify_bytes};
use vinc_broadcast::wire::Head;
use vinc_crypto::IdentityAlg;
use vinc_wire::hlc::Hlc;

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
    EnvelopeRef::topic(topic, head, body).encode_into(&mut bytes);
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
    EnvelopeRef::topic(topic, head, body).encode_into(&mut bytes);
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

/// A hub that also subscribes delivers the exact head its publisher sent.
#[test]
fn a_hub_that_subscribes_delivers_the_wire_head_it_stored() {
    for alg in ALGS {
        let mut net = Net::with_limits(&[alg; 2], 1, SEC, keeping(true));
        net.attach(1);
        net.subscribe(0, T);
        let wire_head = Rc::new(RefCell::new(Vec::new()));
        let seen = Rc::clone(&wire_head);
        net.filter = Some(Box::new(move |_, to, bytes| {
            if to == 0 && (bytes[4] == ty::FANP || bytes[4] == ty::PUB) {
                let tl = usize::from(bytes[5]);
                let rest = &bytes[6 + tl..];
                let (head, _) = Head::parse(rest).unwrap();
                *seen.borrow_mut() = rest[..head.len()].to_vec();
            }
            true
        }));
        net.publish(1, T, b"hello");
        net.advance(SEC);
        let got = heard(&net, 0);
        assert_eq!(got.len(), 1, "{alg:?}");
        assert!(!wire_head.borrow().is_empty(), "{alg:?}: the frame to the hub was seen");
        assert_eq!(got[0].1, *wire_head.borrow(), "{alg:?}");
        let mut bytes = Vec::new();
        EnvelopeRef::topic(&got[0].0, &got[0].1, &got[0].2).encode_into(&mut bytes);
        assert_eq!(verify_bytes(&bytes).unwrap().origin, &net.id(1), "{alg:?}");
    }
}

/// A well-formed envelope structure with random head fields (the signature need not verify), as bytes.
fn structured() -> impl Strategy<Value = Vec<u8>> {
    (
        any::<[u8; 8]>(),
        any::<[u8; 32]>(),
        0..ALGS.len(),
        prop::collection::vec(any::<u8>(), 6000),
        any::<bool>(),
        (any::<u64>(), any::<u32>()),
        prop::collection::vec(any::<u8>(), 0..300),
        prop::collection::vec(any::<u8>(), 0..=255),
    )
        .prop_map(|(mid, origin, a, junk, isb, (wall, counter), body, topic)| {
            let alg = ALGS[a];
            let pk = if alg == IdentityAlg::Ed25519 {
                &[][..]
            } else {
                &junk[..alg.public_key_len()]
            };
            let sig = &junk[2000..2000 + alg.signature_len()];
            let mut head = Vec::new();
            Head {
                mid,
                origin: &origin,
                alg,
                pk,
                sig,
                isb,
                ts: Hlc::new(wall, counter),
            }
            .write(u32::try_from(body.len()).unwrap(), &mut head);
            let mut out = Vec::new();
            EnvelopeRef::topic(&topic, &head, &body).encode_into(&mut out);
            out
        })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn arbitrary_bytes_never_panic_decode_or_verify(b in prop::collection::vec(any::<u8>(), 0..400)) {
        let _ = EnvelopeRef::decode(&b);
        let _ = verify_bytes(&b);
    }

    #[test]
    fn what_decodes_encodes_back_to_the_same_bytes(
        b in structured(),
        cut in any::<prop::sample::Index>(),
        flip in any::<prop::sample::Index>(),
        how in 0..3u8,
    ) {
        let mut b = b;
        match how {
            0 => {}
            1 => b.truncate(cut.index(b.len().max(1))),
            _ => {
                let at = flip.index(b.len().max(1));
                if let Some(x) = b.get_mut(at) {
                    *x ^= 1;
                }
            }
        }
        if let Ok(e) = EnvelopeRef::decode(&b) {
            let mut again = Vec::new();
            e.encode_into(&mut again);
            prop_assert_eq!(again, b);
        }
    }
}

/// The strategy is not vacuous: unmodified structured bytes decode.
#[test]
fn the_structured_envelopes_decode() {
    let mut runner = proptest::test_runner::TestRunner::default();
    let mut ok = 0;
    for _ in 0..64 {
        let b = structured().new_tree(&mut runner).unwrap().current();
        ok += usize::from(EnvelopeRef::decode(&b).is_ok());
    }
    assert!(ok > 40, "{ok} of 64 decoded");
}
