#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use super::*;
use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify};
use vinc_wire::hlc::Hlc;

use crate::statement::FLAG_ISB;

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];
const TOPIC: &[u8] = b"docs/updates";
const BODY: &[u8] = b"the body of the message";
const PARENTS: [ContentId; 2] = [[1; 32], [2; 32]];

struct Signed {
    origin: [u8; 32],
    pk: [u8; MAX_PUBLIC_KEY_LEN],
    sig: [u8; MAX_SIGNATURE_LEN],
    id: ContentId,
}

fn signed(alg: IdentityAlg) -> Signed {
    let key = Keypair::from_seed(alg, &[7u8; 64][..alg.seed_len()]).unwrap();
    let origin = key.node_id().bytes;
    let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
    key.public_key(&mut pk).unwrap();
    let mut sig = [0u8; MAX_SIGNATURE_LEN];
    let unsigned = head_of(alg, &origin, &pk, &[]);
    let hash = *blake3::hash(BODY).as_bytes();
    let fields = unsigned.statement_fields(TOPIC, &hash);
    let n = sign2(&key, &fields, &mut sig).unwrap();
    assert_eq!(n, alg.signature_len());
    let id = id_of(&fields).unwrap();
    Signed { origin, pk, sig, id }
}

fn head_of<'a>(alg: IdentityAlg, origin: &'a [u8; 32], pk: &'a [u8], sig: &'a [u8]) -> Head2<'a> {
    Head2 {
        alg,
        isb: true,
        origin,
        incarnation: 4,
        seq: 11,
        ts: Hlc::new(1_700_000_000_000, 2),
        parents: &PARENTS,
        pk: if alg == IdentityAlg::Ed25519 {
            &[]
        } else {
            &pk[..alg.public_key_len()]
        },
        sig,
    }
}

fn head(alg: IdentityAlg, s: &Signed) -> Head2<'_> {
    head_of(alg, &s.origin, &s.pk, &s.sig[..alg.signature_len()])
}

#[test]
fn a_signed_head_verifies_and_returns_the_content_id() {
    for alg in ALGS {
        let s = signed(alg);
        let h = head(alg, &s);
        assert_eq!(verify2(&h, TOPIC, BODY), Some(s.id), "{alg:?}");
        let hash = *blake3::hash(BODY).as_bytes();
        let mut buf = [0u8; STATEMENT_MAX];
        let n = encode(&h.statement_fields(TOPIC, &hash), &mut buf).unwrap();
        assert_eq!(content_id(&buf[..n]), s.id);
    }
}

#[test]
fn the_signature_covers_the_label_and_the_id() {
    let s = signed(IdentityAlg::Ed25519);
    let sig = &s.sig[..64];
    assert!(verify(IdentityAlg::Ed25519, &s.origin, &signed_message(&s.id), sig).is_ok());
    assert!(verify(IdentityAlg::Ed25519, &s.origin, &s.id, sig).is_err());
}

#[test]
fn any_change_breaks_the_signature() {
    for alg in ALGS {
        let s = signed(alg);
        let h = head(alg, &s);
        let mut other_origin = s.origin;
        other_origin[0] ^= 1;
        let mut parents = PARENTS;
        parents[1][5] ^= 1;
        let mut sig = s.sig;
        sig[0] ^= 1;
        let mut body = [0u8; BODY.len()];
        body.copy_from_slice(BODY);
        body[3] ^= 1;
        let table = [
            (
                "origin",
                Head2 {
                    origin: &other_origin,
                    ..h
                },
                TOPIC,
                BODY,
            ),
            ("incarnation", Head2 { incarnation: 5, ..h }, TOPIC, BODY),
            ("seq", Head2 { seq: 12, ..h }, TOPIC, BODY),
            ("topic", h, b"docs/updatez", BODY),
            (
                "wall",
                Head2 {
                    ts: Hlc::new(1_700_000_000_001, 2),
                    ..h
                },
                TOPIC,
                BODY,
            ),
            (
                "counter",
                Head2 {
                    ts: Hlc::new(1_700_000_000_000, 3),
                    ..h
                },
                TOPIC,
                BODY,
            ),
            ("flags", Head2 { isb: false, ..h }, TOPIC, BODY),
            ("parent", Head2 { parents: &parents, ..h }, TOPIC, BODY),
            (
                "fewer parents",
                Head2 {
                    parents: &PARENTS[..1],
                    ..h
                },
                TOPIC,
                BODY,
            ),
            ("body", h, TOPIC, &body),
            ("shorter body", h, TOPIC, &BODY[..BODY.len() - 1]),
            (
                "signature",
                Head2 {
                    sig: &sig[..alg.signature_len()],
                    ..h
                },
                TOPIC,
                BODY,
            ),
        ];
        for (name, x, topic, body) in table {
            assert_eq!(verify2(&x, topic, body), None, "{alg:?}: {name}");
        }
        assert_eq!(FLAG_ISB, 1);
    }
}

#[test]
fn a_key_that_is_not_the_origins_is_refused() {
    let s = signed(IdentityAlg::Hybrid);
    let t = signed(IdentityAlg::MlDsa65);
    let h = head(IdentityAlg::Hybrid, &s);
    let mut other_pk = s.pk;
    other_pk[40] ^= 1;
    assert_eq!(
        verify2(
            &Head2 {
                pk: &other_pk[..h.pk.len()],
                ..h
            },
            TOPIC,
            BODY
        ),
        None
    );
    assert_eq!(verify2(&Head2 { origin: &t.origin, ..h }, TOPIC, BODY), None);
}

#[test]
fn fields_that_make_no_statement_do_not_sign() {
    let key = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
    let origin = key.node_id().bytes;
    let h = head_of(IdentityAlg::Ed25519, &origin, &[], &[]);
    let hash = [0u8; 32];
    let long = [b't'; 256];
    let mut sig = [0u8; 64];
    assert_eq!(sign2(&key, &h.statement_fields(&long, &hash), &mut sig), None);
    assert_eq!(sign2(&key, &h.statement_fields(TOPIC, &hash), &mut sig[..10]), None);
    assert_eq!(verify2(&h, &long, BODY), None);
}
