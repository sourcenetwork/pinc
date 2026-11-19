#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use super::*;
use pinc_crypto::IdentityAlg;
use pinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify};
use pinc_wire::hlc::Hlc;

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

fn key_of(alg: IdentityAlg, n: u8) -> Keypair {
    Keypair::from_seed(alg, &[n; 64][..alg.seed_len()]).unwrap()
}

/// `signer` signs the statement of the fixed message that names `origin_key`'s node id as its author.
fn sign_as(alg: IdentityAlg, origin_key: &Keypair, signer: &Keypair) -> Signed {
    let origin = origin_key.node_id().bytes;
    let mut pk = [0u8; MAX_PUBLIC_KEY_LEN];
    signer.public_key(&mut pk).unwrap();
    let mut sig = [0u8; MAX_SIGNATURE_LEN];
    let unsigned = head_of(alg, &origin, &pk, &[]);
    let hash = *blake3::hash(BODY).as_bytes();
    let (n, id) = sign2(signer, &unsigned.statement_fields(TOPIC, &hash), &mut sig).unwrap();
    assert_eq!(n, alg.signature_len());
    Signed { origin, pk, sig, id }
}

fn signed(alg: IdentityAlg) -> Signed {
    let key = key_of(alg, 7);
    sign_as(alg, &key, &key)
}

fn head_of<'a>(alg: IdentityAlg, origin: &'a [u8; 32], pk: &'a [u8], sig: &'a [u8]) -> Head2<'a> {
    Head2 {
        alg,
        flags: 1,
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
            ("flags", Head2 { flags: 0, ..h }, TOPIC, BODY),
            ("reserved flags", Head2 { flags: 3, ..h }, TOPIC, BODY),
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
    }
}

/// Key B signs a statement that names A's node id and the head carries B's key: only the check that the key is the
/// origin's refuses it, so the same head with A's own key and signature is the control.
#[test]
fn a_key_that_is_not_the_origins_is_refused() {
    for alg in [IdentityAlg::EcdsaP256, IdentityAlg::MlDsa65, IdentityAlg::Hybrid] {
        let (a, b) = (key_of(alg, 1), key_of(alg, 2));
        let forged = sign_as(alg, &a, &b);
        let h = head(alg, &forged);
        assert_eq!(h.origin, &a.node_id().bytes);
        assert_eq!(verify2(&h, TOPIC, BODY), None, "{alg:?}");
        let honest = sign_as(alg, &a, &a);
        assert_eq!(verify2(&head(alg, &honest), TOPIC, BODY), Some(honest.id), "{alg:?}");
    }
}

#[test]
fn sign2_returns_the_content_id_of_its_statement() {
    let key = key_of(IdentityAlg::Ed25519, 7);
    let origin = key.node_id().bytes;
    let hash = *blake3::hash(BODY).as_bytes();
    let h = head_of(IdentityAlg::Ed25519, &origin, &[], &[]);
    let f = h.statement_fields(TOPIC, &hash);
    let mut out = [0u8; 64];
    let (n, id) = sign2(&key, &f, &mut out).unwrap();
    let mut buf = [0u8; STATEMENT_MAX];
    let len = encode(&f, &mut buf).unwrap();
    assert_eq!((n, id), (64, content_id(&buf[..len])));
}

/// A failed `sign2` writes nothing: an unmade statement, a key of another algorithm, a buffer one byte short.
#[test]
fn a_failed_sign_leaves_the_buffer_untouched() {
    let hash = [0u8; 32];
    let long = [b't'; 256];
    let unsorted = [[2u8; 32], [1u8; 32]];
    for alg in ALGS {
        let key = key_of(alg, 7);
        let origin = key.node_id().bytes;
        let h = head_of(alg, &origin, &[0u8; MAX_PUBLIC_KEY_LEN], &[]);
        let other = ALGS.iter().copied().find(|a| *a != alg).unwrap();
        let wrong_key = key_of(other, 7);
        let fields = h.statement_fields(TOPIC, &hash);
        let short = alg.signature_len() - 1;
        let cases = [
            (
                "long topic",
                &key,
                h.statement_fields(&long, &hash),
                alg.signature_len(),
            ),
            (
                "unsorted parents",
                &key,
                Fields {
                    parents: &unsorted,
                    ..fields
                },
                alg.signature_len(),
            ),
            ("another algorithm", &wrong_key, fields, MAX_SIGNATURE_LEN),
            ("short buffer", &key, fields, short),
        ];
        for (name, k, f, room) in cases {
            let mut out = [0xaa_u8; MAX_SIGNATURE_LEN];
            assert_eq!(sign2(k, &f, &mut out[..room]), None, "{alg:?}: {name}");
            assert!(out.iter().all(|b| *b == 0xaa), "{alg:?}: {name} wrote");
        }
    }
}

#[test]
fn fields_that_make_no_statement_do_not_verify() {
    let s = signed(IdentityAlg::Ed25519);
    let h = head(IdentityAlg::Ed25519, &s);
    let long = [b't'; 256];
    assert_eq!(verify2(&h, TOPIC, BODY), Some(s.id));
    assert_eq!(verify2(&h, &long, BODY), None);
}
