#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    reason = "tests assert"
)]

use super::*;
use vinc_dag::cid::{BLAKE3, CidRef, DAG_CBOR, MAX_TEXT_LEN, RAW};
use vinc_wire::cbor::{Decoder, MapReader};

const ORIGIN: NodeId = {
    let mut o = [0u8; 32];
    let mut i = 0;
    while i < 32 {
        o[i] = i as u8;
        i += 1;
    }
    o
};
const P1: ContentId = [0x10; 32];
const P2: ContentId = [0x20; 32];
const BODY: &[u8] = b"twenty bytes of body";

fn base<'a>(parents: &'a [ContentId], body: &'a [u8; 32]) -> Fields<'a> {
    Fields {
        origin_alg: IdentityAlg::Ed25519,
        origin: &ORIGIN,
        incarnation: 7,
        seq: 3,
        topic: b"docs/updates",
        time: Hlc::new(1_700_000_000_000, 5),
        flags: 1,
        parents,
        body,
    }
}

fn enc(f: &Fields<'_>) -> ([u8; STATEMENT_MAX], usize) {
    let mut out = [0u8; STATEMENT_MAX];
    let n = encode(f, &mut out).unwrap();
    (out, n)
}

fn hex<'a>(b: &[u8], buf: &'a mut [u8; 2 * STATEMENT_MAX]) -> &'a str {
    const D: &[u8; 16] = b"0123456789abcdef";
    for (i, x) in b.iter().enumerate() {
        buf[2 * i] = D[usize::from(x >> 4)];
        buf[2 * i + 1] = D[usize::from(x & 15)];
    }
    core::str::from_utf8(&buf[..2 * b.len()]).unwrap()
}

/// The statement of one fixed message, its id, CIDs and signed message, as bytes checked by hand against the layout.
const STATEMENT_HEX: &str = "a9637365710364626f6479d82a58250001551e207061237440987f26b72647798a8b65c2203c4109e1bd7f063d168fdc5791e1c0646b696e647076696e632f62726f6164636173742f326474696d65821b0000018bcfe568000565666c6167730165746f7069634c646f63732f75706461746573666f726967696e582101000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f67706172656e747382d82a58250001711e201010101010101010101010101010101010101010101010101010101010101010d82a58250001711e2020202020202020202020202020202020202020202020202020202020202020206b696e6361726e6174696f6e07";
const ID_HEX: &str = "028e04d1e4f7f50e640657bd5a4f013baff01bf38d3406eb414a1d76749a7e27";
const CID_HEX: &str = "01711e20028e04d1e4f7f50e640657bd5a4f013baff01bf38d3406eb414a1d76749a7e27";
const BODY_CID_HEX: &str = "01551e207061237440987f26b72647798a8b65c2203c4109e1bd7f063d168fdc5791e1c0";
const SIGNED_HEX: &str =
    "56494e4320323032362076312073746174656d656e74028e04d1e4f7f50e640657bd5a4f013baff01bf38d3406eb414a1d76749a7e27";

#[test]
fn golden_bytes() {
    let hash = *blake3::hash(BODY).as_bytes();
    let parents = [P1, P2];
    let (out, n) = enc(&base(&parents, &hash));
    let mut buf = [0u8; 2 * STATEMENT_MAX];
    assert_eq!(hex(&out[..n], &mut buf), STATEMENT_HEX);
    let id = content_id(&out[..n]);
    assert_eq!(hex(&id, &mut buf), ID_HEX);
    assert_eq!(hex(&cid(&id), &mut buf), CID_HEX);
    assert_eq!(hex(&body_cid(&hash), &mut buf), BODY_CID_HEX);
    assert_eq!(hex(&signed_message(&id), &mut buf), SIGNED_HEX);
    assert_eq!(signed_message(&id)[..22], *b"VINC 2026 v1 statement");
}

#[test]
fn cid_text_forms() {
    let hash = *blake3::hash(BODY).as_bytes();
    let mut text = [0u8; MAX_TEXT_LEN];
    let c = cid(&hash);
    let s = CidRef::parse(&c).unwrap().encode_text(&mut text).unwrap();
    assert!(s.starts_with("bafyr4i"), "{s}");
    let c = body_cid(&hash);
    let s = CidRef::parse(&c).unwrap().encode_text(&mut text).unwrap();
    assert!(s.starts_with("bafkr4i"), "{s}");
}

#[test]
fn cids_parse_and_verify_with_the_dag_code() {
    let hash = *blake3::hash(BODY).as_bytes();
    let parents = [P1, P2];
    let (out, n) = enc(&base(&parents, &hash));
    let id = content_id(&out[..n]);
    let c = cid(&id);
    let r = CidRef::parse(&c).unwrap();
    assert_eq!((r.codec(), r.hash_code()), (DAG_CBOR, BLAKE3));
    r.verify(&out[..n]).unwrap();
    assert!(r.verify(&out[..n - 1]).is_err());
    let c = body_cid(&hash);
    let r = CidRef::parse(&c).unwrap();
    assert_eq!((r.codec(), r.hash_code()), (RAW, BLAKE3));
    r.verify(BODY).unwrap();
    assert!(r.verify(b"another body").is_err());
}

/// The keys come out in the DAG-CBOR order: shorter first, then bytewise.
#[test]
fn keys_are_in_canonical_order() {
    let hash = [9u8; 32];
    let (out, n) = enc(&base(&[], &hash));
    let mut dec = Decoder::new(&out[..n]);
    let mut map = MapReader::new(&mut dec).unwrap();
    let mut got = [""; 9];
    let mut count = 0;
    while let Some(k) = map.next_key(&mut dec).unwrap() {
        got[count] = k;
        count += 1;
        dec.skip_value().unwrap();
    }
    assert_eq!(count, 9);
    assert!(dec.is_empty());
    let mut sorted = got;
    sorted.sort_by(|a, b| (a.len(), a.as_bytes()).cmp(&(b.len(), b.as_bytes())));
    assert_eq!(got, sorted);
    assert_eq!(
        got,
        [
            "seq",
            "body",
            "kind",
            "time",
            "flags",
            "topic",
            "origin",
            "parents",
            "incarnation"
        ]
    );
    assert_eq!(got.map(str::len), [3, 4, 4, 4, 5, 5, 6, 7, 11]);
}

#[test]
fn every_field_changes_the_statement_and_its_id() {
    let hash = *blake3::hash(BODY).as_bytes();
    let other_hash = *blake3::hash(b"another").as_bytes();
    let parents = [P1, P2];
    let (first, second, other_second) = ([P1], [P2], [P1, [0x21; 32]]);
    let mut origin2 = ORIGIN;
    origin2[31] ^= 1;
    let f = base(&parents, &hash);
    let table = [
        (
            "alg",
            Fields {
                origin_alg: IdentityAlg::EcdsaP256,
                ..f
            },
        ),
        ("origin", Fields { origin: &origin2, ..f }),
        ("incarnation", Fields { incarnation: 8, ..f }),
        ("seq", Fields { seq: 4, ..f }),
        (
            "topic",
            Fields {
                topic: b"docs/updatez",
                ..f
            },
        ),
        (
            "topic shorter",
            Fields {
                topic: b"docs/update",
                ..f
            },
        ),
        (
            "wall",
            Fields {
                time: Hlc::new(1_700_000_000_001, 5),
                ..f
            },
        ),
        (
            "counter",
            Fields {
                time: Hlc::new(1_700_000_000_000, 6),
                ..f
            },
        ),
        ("flags", Fields { flags: 0, ..f }),
        ("no parents", Fields { parents: &[], ..f }),
        ("one parent", Fields { parents: &first, ..f }),
        ("other parent", Fields { parents: &second, ..f }),
        (
            "second parent",
            Fields {
                parents: &other_second,
                ..f
            },
        ),
        ("body", Fields { body: &other_hash, ..f }),
    ];
    let (base_out, base_n) = enc(&f);
    let base_id = content_id(&base_out[..base_n]);
    for (i, (name, x)) in table.iter().enumerate() {
        let (out, n) = enc(x);
        assert_ne!(out[..n], base_out[..base_n], "{name}");
        assert_ne!(content_id(&out[..n]), base_id, "{name}");
        for (other, y) in table.iter().skip(i + 1) {
            let (o2, n2) = enc(y);
            assert_ne!(out[..n], o2[..n2], "{name} against {other}");
        }
    }
}

#[test]
fn parents_must_be_strictly_ascending_and_few() {
    let hash = [0u8; 32];
    let refuse = |parents: &[ContentId]| {
        let mut out = [0u8; STATEMENT_MAX];
        encode(&base(parents, &hash), &mut out)
    };
    assert_eq!(refuse(&[P2, P1]), Err(StatementError::ParentsNotAscending));
    assert_eq!(refuse(&[P1, P1]), Err(StatementError::ParentsNotAscending));
    assert_eq!(refuse(&[P1, P2, P1]), Err(StatementError::ParentsNotAscending));
    let nine: [ContentId; 9] = core::array::from_fn(|i| [u8::try_from(i).unwrap(); 32]);
    assert_eq!(refuse(&nine), Err(StatementError::TooManyParents));
    assert!(refuse(&nine[..8]).is_ok());
    assert!(refuse(&[]).is_ok());
}

#[test]
fn flags_and_topic_are_bounded() {
    let hash = [0u8; 32];
    let mut out = [0u8; STATEMENT_MAX];
    for flags in [2u8, 3, 0x80, 0xff] {
        let f = Fields {
            flags,
            ..base(&[], &hash)
        };
        assert_eq!(encode(&f, &mut out), Err(StatementError::ReservedFlags), "{flags}");
    }
    assert!(
        encode(
            &Fields {
                flags: 0,
                ..base(&[], &hash)
            },
            &mut out
        )
        .is_ok()
    );
    let long = [b't'; MAX_TOPIC + 1];
    let f = Fields {
        topic: &long,
        ..base(&[], &hash)
    };
    assert_eq!(encode(&f, &mut out), Err(StatementError::TopicTooLong));
}

#[test]
fn the_longest_statement_is_the_maximum() {
    assert_eq!(STATEMENT_MAX, 772);
    let hash = [0xff; 32];
    let topic = [0xff; MAX_TOPIC];
    let parents: [ContentId; MAX_PARENTS] = core::array::from_fn(|i| [u8::try_from(i).unwrap() + 1; 32]);
    let f = Fields {
        origin_alg: IdentityAlg::Hybrid,
        origin: &[0xff; 32],
        incarnation: u64::MAX,
        seq: u64::MAX,
        topic: &topic,
        time: Hlc::new(u64::MAX, u32::MAX),
        flags: 1,
        parents: &parents,
        body: &hash,
    };
    assert_eq!(enc(&f).1, STATEMENT_MAX);
}
