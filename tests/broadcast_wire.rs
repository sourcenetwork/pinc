//! The wire format: the head and the frames parse strictly, never panic, and encode back to the same bytes; garbage
//! frames fed to the machine neither panic nor deliver anything.
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

use common::{ALGS, Net, SEC, keypair};
use proptest::prelude::*;
use vinc_broadcast::consts::DEFAULT_MAX_BODY;
use vinc_broadcast::wire::{self, Head, build, ty};
use vinc_broadcast::{auth, consts};
use vinc_crypto::IdentityAlg;
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_wire::hlc::Hlc;

const T: &[u8] = b"wire";

fn encoded(alg: IdentityAlg, body: &[u8]) -> Vec<u8> {
    let key = keypair(alg, 5);
    let id = key.node_id();
    let mid = auth::message_id(&id.bytes, 1, 1, T);
    let mut sig = [0u8; MAX_SIGNATURE_LEN];
    let n = auth::sign(&key, T, &mid, body, Hlc::new(1_700_000_000_000, 7), true, &mut sig).unwrap();
    let mut pk = vec![0u8; alg.public_key_len()];
    key.public_key(&mut pk).unwrap();
    let head = Head {
        mid,
        origin: &id.bytes,
        alg,
        pk: if alg == IdentityAlg::Ed25519 { &[] } else { &pk },
        sig: &sig[..n],
        isb: true,
        ts: Hlc::new(1_700_000_000_000, 7),
    };
    let mut out = Vec::new();
    head.write(u32::try_from(body.len()).unwrap(), &mut out);
    out.extend_from_slice(body);
    out
}

#[test]
fn a_head_round_trips_for_every_algorithm() {
    for alg in ALGS {
        let bytes = encoded(alg, b"payload");
        let (head, body) = Head::parse(&bytes).unwrap();
        assert_eq!(body, b"payload");
        assert_eq!(head.alg, alg);
        assert_eq!(head.ts, Hlc::new(1_700_000_000_000, 7));
        assert_eq!(head.len() + body.len(), bytes.len());
        assert!(head.isb);
        assert!(auth::verify(&head, T, body), "{alg:?}");
        let mut again = Vec::new();
        head.write(u32::try_from(body.len()).unwrap(), &mut again);
        again.extend_from_slice(body);
        assert_eq!(again, bytes);
    }
}

#[test]
fn every_truncation_of_a_head_is_an_error_never_a_panic() {
    for alg in ALGS {
        let bytes = encoded(alg, b"payload");
        for cut in 0..bytes.len() - b"payload".len() {
            assert!(Head::parse(&bytes[..cut]).is_err(), "{alg:?} cut {cut}");
        }
    }
}

#[test]
fn a_body_shorter_or_longer_than_the_head_says_is_an_error() {
    let bytes = encoded(IdentityAlg::Ed25519, b"payload");
    assert!(Head::parse(&bytes[..bytes.len() - 1]).is_err());
    let mut longer = bytes.clone();
    longer.push(0);
    assert!(Head::parse(&longer).is_err());
}

#[test]
fn an_unknown_algorithm_and_a_reserved_body_flag_are_errors() {
    let mut bytes = encoded(IdentityAlg::Ed25519, b"x");
    bytes[8 + 32] = 9;
    assert!(Head::parse(&bytes).is_err());
    let mut bytes = encoded(IdentityAlg::Ed25519, b"x");
    let isb_at = 8 + 32 + 1 + 64;
    bytes[isb_at] = 2;
    assert!(Head::parse(&bytes).is_err());
}

#[test]
fn the_size_limit_is_the_nodes_configuration_not_the_parsers() {
    let mut bytes = encoded(IdentityAlg::Ed25519, &vec![0; DEFAULT_MAX_BODY]);
    assert!(Head::parse(&bytes).is_ok());
    // Claim one more byte and supply it.
    let at = 8 + 32 + 1 + 64 + 1;
    bytes[at..at + 4].copy_from_slice(&u32::try_from(DEFAULT_MAX_BODY + 1).unwrap().to_be_bytes());
    bytes.push(0);
    assert!(
        Head::parse(&bytes).is_ok(),
        "a node enforces its configured limit; see broadcast_limits"
    );
}

#[test]
fn a_frame_is_built_with_its_prefix_and_never_outgrows_its_buffer() {
    let mut buf = Vec::with_capacity(64);
    build(&mut buf, ty::HAVE, b"abc", &[b"12345678"]).unwrap();
    assert_eq!(
        buf,
        [
            0,
            0,
            0,
            13,
            ty::HAVE,
            3,
            b'a',
            b'b',
            b'c',
            b'1',
            b'2',
            b'3',
            b'4',
            b'5',
            b'6',
            b'7',
            b'8'
        ]
    );
    let cap = buf.capacity();
    assert!(
        build(&mut buf, ty::HAVE, b"abc", &[&[0u8; 100]]).is_err(),
        "over the capacity"
    );
    assert_eq!(buf.capacity(), cap);
    assert!(build(&mut buf, ty::HAVE, &[0u8; 256], &[]).is_err(), "topic over 255");
    assert!(wire::get_ts(&[0; 11]).is_none());
    assert_eq!(
        wire::get_ts(&[0, 0, 0, 0, 0, 0, 0, 5, 0, 0, 0, 6]),
        Some(Hlc::new(5, 6))
    );
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn garbage_never_panics_a_head_parse(bytes in proptest::collection::vec(any::<u8>(), 0..6000)) {
        let _ = Head::parse(&bytes);
    }

    #[test]
    fn garbage_frames_never_panic_a_hub_or_a_member_and_deliver_nothing(
        ty_byte in 0u8..32,
        topic in proptest::collection::vec(any::<u8>(), 0..300),
        rest in proptest::collection::vec(any::<u8>(), 0..400),
        from_hub in any::<bool>(),
    ) {
        let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
        net.subscribe(2, b"t");
        let hub = net.id(0);
        let stranger = [9u8; 32];
        let from = if from_hub { hub } else { stranger };
        let now = net.now;
        for target in 0..3 {
            let n = &mut net.nodes[target];
            n.t.frame(&mut n.h, now, &from, ty_byte, &topic, &rest);
            n.t.on_timer(&mut n.h, now + SEC);
        }
        net.pump();
        prop_assert!(net.delivered(1).is_empty() && net.delivered(2).is_empty());
        for n in &net.nodes {
            prop_assert!(n.t.topic_count() <= consts::DEFAULT_MAX_TOPICS);
        }
    }

    #[test]
    fn a_message_frame_with_a_valid_head_and_a_garbled_tail_is_never_delivered(
        flips in proptest::collection::vec((any::<prop::sample::Index>(), 1u8..=255), 1..4),
    ) {
        let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
        net.subscribe(2, b"t");
        let good = encoded(IdentityAlg::Ed25519, b"payload");
        let mut bad = good.clone();
        for (i, x) in &flips {
            let at = i.index(bad.len());
            bad[at] ^= x;
        }
        let hub = net.id(0);
        let now = net.now;
        let n = &mut net.nodes[2];
        n.t.frame(&mut n.h, now, &hub, ty::MSG, T, &bad);
        net.pump();
        // The origin of this fixed message is not a node of the net, so the access check never even starts unless the
        // signature verified; flipping any byte breaks either the parse or the signature.
        prop_assert!(net.delivered(2).is_empty());
    }
}

#[test]
fn a_message_signed_by_an_unknown_but_valid_origin_is_delivered_once_allowed() {
    // Control for the property above: the untouched frame verifies and is delivered.
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    net.subscribe(2, b"wire");
    let good = encoded(IdentityAlg::Ed25519, b"payload");
    let hub = net.id(0);
    let now = net.now;
    let n = &mut net.nodes[2];
    n.t.frame(&mut n.h, now, &hub, ty::MSG, T, &good);
    net.pump();
    assert_eq!(net.bodies(2), vec![b"payload".to_vec()]);
}
