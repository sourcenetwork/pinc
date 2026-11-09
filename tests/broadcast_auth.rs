//! Origin authentication: the signature covers the topic, the id and the hash of the body, for every identity
//! algorithm. A flipped body byte or a flipped signature byte is rejected and never delivered or acknowledged.
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

use common::{ALGS, Net, SEC, keypair, ty};
use vinc_broadcast::wire::Head;
use vinc_broadcast::{Reject, Trace, auth};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;

const T: &[u8] = b"news";

/// Where the signature and the body sit in a whole frame.
fn offsets(frame: &[u8]) -> (usize, usize) {
    let tl = usize::from(frame[5]);
    let rest = &frame[6 + tl..];
    let (head, body) = Head::parse(rest).unwrap();
    let sig_at = 6 + tl + 8 + 32 + 1 + head.pk.len();
    let _ = head.sig;
    (sig_at, frame.len() - body.len())
}

fn rejected(net: &mut Net, i: usize) -> Vec<Reject> {
    let mut out = Vec::new();
    while let Some(t) = net.nodes[i].t.poll_trace() {
        if let Trace::Rejected { why, .. } = t {
            out.push(why);
        }
    }
    out
}

fn tamper_world(alg: vinc_crypto::IdentityAlg, hop: (usize, u8), flip_body: bool) -> Net {
    let mut net = Net::new(alg, 1, 2, SEC);
    net.subscribe(2, T);
    net.filter = Some(Box::new(move |_, to, bytes| {
        if to == hop.0 && bytes[4] == hop.1 {
            let (sig_at, body_at) = offsets(bytes);
            if flip_body {
                assert!(body_at < bytes.len(), "the test body is not empty");
                bytes[body_at] ^= 1;
            } else {
                bytes[sig_at + 3] ^= 1;
            }
        }
        true
    }));
    net
}

#[test]
fn a_flipped_body_byte_is_rejected_at_the_hub_for_every_algorithm() {
    for alg in ALGS {
        let mut net = tamper_world(alg, (0, ty::FANP), true);
        net.publish(1, T, b"hello");
        net.advance(SEC);
        assert!(net.delivered(2).is_empty(), "{alg:?}");
        assert_eq!(net.nodes[0].t.log_len(T), 0, "{alg:?}");
        assert!(rejected(&mut net, 0).contains(&Reject::BadSignature), "{alg:?}");
        assert_eq!(
            net.count(ty::PACK),
            0,
            "a message the hub rejected is not acknowledged ({alg:?})"
        );
    }
}

#[test]
fn a_flipped_signature_byte_is_rejected_at_the_hub_for_every_algorithm() {
    for alg in ALGS {
        let mut net = tamper_world(alg, (0, ty::FANP), false);
        net.publish(1, T, b"hello");
        net.advance(SEC);
        assert!(net.delivered(2).is_empty(), "{alg:?}");
        assert!(rejected(&mut net, 0).contains(&Reject::BadSignature), "{alg:?}");
    }
}

#[test]
fn a_body_swapped_by_a_hub_is_rejected_at_the_subscriber_for_every_algorithm() {
    for alg in ALGS {
        let mut net = tamper_world(alg, (2, ty::MSG), true);
        net.publish(1, T, b"hello");
        net.advance(SEC);
        assert!(net.delivered(2).is_empty(), "{alg:?}");
        assert_eq!(
            net.nodes[0].t.log_len(T),
            1,
            "the hub itself held a good copy ({alg:?})"
        );
        assert!(rejected(&mut net, 2).contains(&Reject::BadSignature), "{alg:?}");
    }
}

#[test]
fn a_flipped_signature_byte_is_rejected_at_the_subscriber_for_every_algorithm() {
    for alg in ALGS {
        let mut net = tamper_world(alg, (2, ty::MSG), false);
        net.publish(1, T, b"hello");
        net.advance(SEC);
        assert!(net.delivered(2).is_empty(), "{alg:?}");
    }
}

#[test]
fn an_empty_body_is_signed_too() {
    for alg in ALGS {
        let mut net = Net::new(alg, 1, 2, SEC);
        net.subscribe(2, T);
        let mid = net.publish(1, T, b"");
        net.advance(SEC);
        assert_eq!(net.delivered(2), vec![mid]);
        assert_eq!(net.bodies(2), vec![Vec::<u8>::new()]);
    }
}

fn mk<'a>(alg: vinc_crypto::IdentityAlg, pk: &'a [u8], mid: [u8; 8], origin: &'a [u8; 32], sig: &'a [u8]) -> Head<'a> {
    Head {
        mid,
        origin,
        alg,
        pk: if alg == vinc_crypto::IdentityAlg::Ed25519 {
            &[]
        } else {
            pk
        },
        sig,
        isb: true,
        ts: vinc_wire::hlc::Hlc::new(1, 0),
    }
}

/// Build a signed head by hand and check `verify` against every part it covers.
#[test]
fn the_signature_covers_the_topic_the_id_and_the_body() {
    for alg in ALGS {
        let key = keypair(alg, 7);
        let id = key.node_id();
        let mid = auth::message_id(&id.bytes, 1, 1, T);
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let n = auth::sign(&key, T, &mid, b"body", vinc_wire::hlc::Hlc::new(1, 0), true, &mut sig).unwrap();
        let mut pk = vec![0u8; alg.public_key_len()];
        key.public_key(&mut pk).unwrap();
        let good = mk(alg, &pk, mid, &id.bytes, &sig[..n]);
        assert!(auth::verify(&good, T, b"body"), "{alg:?}");
        assert!(!auth::verify(&good, T, b"bodY"), "body {alg:?}");
        assert!(
            !auth::verify(&good, T, b"bod"),
            "the length alone is not what is signed {alg:?}"
        );
        assert!(!auth::verify(&good, b"other", b"body"), "topic {alg:?}");
        let mut other = mid;
        other[0] ^= 1;
        assert!(
            !auth::verify(&mk(alg, &pk, other, &id.bytes, &sig[..n]), T, b"body"),
            "mid {alg:?}"
        );
        let mut forged = id.bytes;
        forged[31] ^= 1;
        assert!(
            !auth::verify(&mk(alg, &pk, mid, &forged, &sig[..n]), T, b"body"),
            "origin {alg:?}"
        );
        // Same length body, different bytes: the old scheme (signing only the length) would have accepted this.
        assert!(!auth::verify(&good, T, b"BODY"), "{alg:?}");
    }
}

#[test]
fn a_key_that_is_not_the_origins_is_rejected() {
    for alg in [
        vinc_crypto::IdentityAlg::EcdsaP256,
        vinc_crypto::IdentityAlg::MlDsa65,
        vinc_crypto::IdentityAlg::Hybrid,
    ] {
        let (a, b) = (keypair(alg, 1), keypair(alg, 2));
        let mid = auth::message_id(&a.node_id().bytes, 1, 1, T);
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let n = auth::sign(&b, T, &mid, b"x", vinc_wire::hlc::Hlc::new(1, 0), true, &mut sig).unwrap();
        let mut pk = vec![0u8; alg.public_key_len()];
        b.public_key(&mut pk).unwrap();
        // b signed and supplies its own key, but claims a's node id.
        let head = Head {
            mid,
            origin: &a.node_id().bytes,
            alg,
            pk: &pk,
            sig: &sig[..n],
            isb: true,
            ts: vinc_wire::hlc::Hlc::new(1, 0),
        };
        assert!(!auth::verify(&head, T, b"x"), "{alg:?}");
    }
}

#[test]
fn message_ids_differ_by_every_input() {
    let o = [1u8; 32];
    let base = auth::message_id(&o, 1, 1, T);
    assert_ne!(base, auth::message_id(&[2u8; 32], 1, 1, T));
    assert_ne!(base, auth::message_id(&o, 2, 1, T));
    assert_ne!(base, auth::message_id(&o, 1, 2, T));
    assert_ne!(base, auth::message_id(&o, 1, 1, b"other"));
    assert_eq!(base, auth::message_id(&o, 1, 1, T));
}

#[test]
fn the_timestamp_and_the_body_flag_are_signed_too() {
    use vinc_wire::hlc::Hlc;
    for alg in ALGS {
        let key = keypair(alg, 9);
        let id = key.node_id();
        let mid = auth::message_id(&id.bytes, 1, 1, T);
        let ts = Hlc::new(1_700_000_000_000, 3);
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let n = auth::sign(&key, T, &mid, b"body", ts, true, &mut sig).unwrap();
        let mut pk = vec![0u8; alg.public_key_len()];
        key.public_key(&mut pk).unwrap();
        let with = |ts: Hlc, isb: bool| Head {
            mid,
            origin: &id.bytes,
            alg,
            pk: if alg == vinc_crypto::IdentityAlg::Ed25519 {
                &[]
            } else {
                &pk
            },
            sig: &sig[..n],
            isb,
            ts,
        };
        assert!(auth::verify(&with(ts, true), T, b"body"), "{alg:?}");
        assert!(
            !auth::verify(&with(Hlc::new(ts.wall - 1, 3), true), T, b"body"),
            "wall {alg:?}"
        );
        assert!(
            !auth::verify(&with(Hlc::new(ts.wall, 4), true), T, b"body"),
            "counter {alg:?}"
        );
        assert!(!auth::verify(&with(ts, false), T, b"body"), "flag {alg:?}");
    }
}
