//! Tests of pinc-dag's CIDs.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::type_complexity,
    clippy::redundant_closure_for_method_calls
)]

use std::cmp::Ordering;

use pinc_dag::cid::{BLAKE3, Cid, CidError, CidRef, DAG_CBOR, MAX_TEXT_LEN, RAW, SHA2_256, cmp_text};
use proptest::prelude::*;

mod golden;

pinc_tests::install_counting_allocator!();

fn arb_cid() -> impl Strategy<Value = Cid> {
    let known = (
        prop::sample::select(vec![DAG_CBOR, RAW, 0x70, 0x129]),
        prop::sample::select(vec![SHA2_256, BLAKE3]),
        any::<[u8; 32]>(),
    )
        .prop_map(|(c, h, d)| Cid::new(c, h, &d).unwrap());
    let other = (
        0u64..1 << 40,
        0x30u64..0x1000,
        prop::collection::vec(any::<u8>(), 0..=64),
    )
        .prop_map(|(c, h, d)| Cid::new(c, h, &d).unwrap());
    prop_oneof![known, other]
}

#[test]
fn golden_cids_round_trip_through_text() {
    for (name, bytes, text) in golden::BLOCKS {
        let cid = Cid::for_block(DAG_CBOR, SHA2_256, bytes).unwrap();
        assert_eq!(cid.to_string(), *text, "{name}");
        assert_eq!(Cid::parse_text(text).unwrap(), cid, "{name}");
        assert_eq!(cid.codec(), DAG_CBOR);
        assert_eq!(cid.hash_code(), SHA2_256);
        cid.verify(bytes).unwrap();
        assert_eq!(cid.verify(b"other"), Err(CidError::DigestMismatch));
    }
}

#[test]
fn blake3_cid_matches_the_blake3_crate() {
    let cid = Cid::for_block(RAW, BLAKE3, b"hello").unwrap();
    assert_eq!(cid.digest(), blake3::hash(b"hello").as_bytes());
    cid.verify(b"hello").unwrap();
    assert_eq!(cid.codec(), RAW);
}

#[test]
fn unknown_hash_cannot_be_computed_but_can_be_carried() {
    assert_eq!(Cid::for_block(RAW, 0x13, b"x"), Err(CidError::UnsupportedHash(0x13)));
    let cid = Cid::new(RAW, 0x13, &[7; 10]).unwrap();
    assert_eq!(cid.verify(b"x"), Err(CidError::UnsupportedHash(0x13)));
}

#[test]
fn parser_rejects_malformed_cids() {
    let ok = Cid::new(DAG_CBOR, SHA2_256, &[1; 32]).unwrap();
    let b = ok.as_bytes();
    // CIDv0: a bare sha2-256 multihash.
    let mut v0 = vec![0x12, 0x20];
    v0.extend_from_slice(&[1; 32]);
    assert_eq!(CidRef::parse(&v0), Err(CidError::CidV0));
    assert_eq!(
        CidRef::parse(&[2, 0x71, 0x12, 0x20]),
        Err(CidError::UnsupportedVersion(2))
    );
    // A digest over 64 bytes.
    let mut long = vec![1, 0x55, 0x30, 65];
    long.extend_from_slice(&[0; 65]);
    assert_eq!(CidRef::parse(&long), Err(CidError::DigestTooLong(65)));
    // A known hash with the wrong length.
    let mut short = vec![1, 0x71, 0x12, 31];
    short.extend_from_slice(&[0; 31]);
    assert_eq!(
        CidRef::parse(&short),
        Err(CidError::DigestLenMismatch { hash: 0x12, len: 31 })
    );
    // A non-minimal varint, trailing bytes, a short digest.
    let mut nonmin = vec![0x81, 0x00];
    nonmin.extend_from_slice(&b[1..]);
    assert!(matches!(CidRef::parse(&nonmin), Err(CidError::Wire(_))));
    let mut trailing = b.to_vec();
    trailing.push(0);
    assert_eq!(CidRef::parse(&trailing), Err(CidError::TrailingBytes));
    assert!(matches!(CidRef::parse(&b[..b.len() - 1]), Err(CidError::Wire(_))));
    assert_eq!(CidRef::parse_prefix(&trailing).unwrap().1, &[0]);
}

#[test]
fn text_parser_rejects_malformed_text() {
    let good = Cid::new(DAG_CBOR, SHA2_256, &[9; 32]).unwrap().to_string();
    assert!(Cid::parse_text(&good).is_ok());
    for bad in [
        "",
        "b",
        "z",
        &good[1..],
        &good.to_uppercase(),
        &format!("{good}="),
        &format!("{good}a"),
        &good[..good.len() - 1],
    ] {
        assert!(Cid::parse_text(bad).is_err(), "{bad}");
    }
    // Non-zero padding bits: the last digit of a canonical text has zero low bits; set one.
    let alphabet = b"abcdefghijklmnopqrstuvwxyz234567";
    let last = good.bytes().last().unwrap();
    let v = alphabet.iter().position(|&c| c == last).unwrap();
    assert_eq!(v & 1, 0);
    let mut dirty = good.clone();
    dirty.pop();
    dirty.push(alphabet[v | 1] as char);
    assert_eq!(
        Cid::parse_text(&dirty),
        Err(CidError::BadText("padding bits are not zero"))
    );
    // One digit leaves 5 bits: no whole number of bytes, so no padding bit is to blame.
    assert_eq!(
        Cid::parse_text("ba"),
        Err(CidError::BadText("the text is not a whole number of bytes"))
    );
    let too_long = format!("b{}", "a".repeat(200));
    assert!(Cid::parse_text(&too_long).is_err());
}

#[test]
fn text_order_differs_from_byte_order() {
    // Digest bytes chosen so a base32 digit in 2..=7 faces a letter at the same position.
    let low = Cid::new(RAW, 0x30, &[0xff; 4]).unwrap();
    let high = Cid::new(RAW, 0x30, &[0x00; 4]).unwrap();
    assert_eq!(
        cmp_text(low.as_ref(), high.as_ref()),
        low.to_string().cmp(&high.to_string())
    );
    let digits = (0..=255u8).flat_map(|a| (0..=255u8).map(move |b| (a, b)));
    let mut seen_disagreement = false;
    for (a, b) in digits.step_by(37) {
        let x = Cid::new(RAW, 0x30, &[a, 0, 0]).unwrap();
        let y = Cid::new(RAW, 0x30, &[b, 0, 0]).unwrap();
        let by_text = x.cmp_text(&y);
        assert_eq!(by_text, x.to_string().cmp(&y.to_string()));
        seen_disagreement |= by_text != x.cmp(&y);
    }
    assert!(seen_disagreement, "byte order and text order should differ somewhere");
}

#[test]
fn encode_text_reports_a_short_buffer() {
    let cid = Cid::for_block(DAG_CBOR, SHA2_256, b"x").unwrap();
    let mut small = [0u8; 10];
    assert!(matches!(
        cid.encode_text(&mut small),
        Err(CidError::BufferTooSmall { .. })
    ));
    let mut big = [0u8; MAX_TEXT_LEN];
    assert_eq!(cid.encode_text(&mut big).unwrap(), cid.to_string());
}

proptest! {
    #[test]
    fn binary_round_trip(cid in arb_cid()) {
        let back = Cid::from_bytes(cid.as_bytes()).unwrap();
        prop_assert_eq!(back, cid);
        let r = CidRef::parse(cid.as_bytes()).unwrap();
        prop_assert_eq!(r.as_bytes(), cid.as_bytes());
        prop_assert_eq!(r.digest(), cid.digest());
        prop_assert_eq!(r.codec(), cid.codec());
        prop_assert_eq!(r.hash_code(), cid.hash_code());
        prop_assert_eq!(r.into_owned(), cid);
    }

    #[test]
    fn text_round_trip(cid in arb_cid()) {
        let text = cid.to_string();
        prop_assert!(text.len() <= MAX_TEXT_LEN && text.starts_with('b'));
        prop_assert_eq!(Cid::parse_text(&text).unwrap(), cid);
        let mut buf = [0u8; MAX_TEXT_LEN];
        prop_assert_eq!(cid.encode_text(&mut buf).unwrap(), text);
    }

    #[test]
    fn cmp_text_agrees_with_the_strings(a in arb_cid(), b in arb_cid()) {
        let expect = a.to_string().cmp(&b.to_string());
        prop_assert_eq!(cmp_text(a.as_ref(), b.as_ref()), expect);
        prop_assert_eq!(a.cmp_text(&b), expect);
        prop_assert_eq!(expect == Ordering::Equal, a == b);
    }

    #[test]
    fn arbitrary_bytes_never_panic(bytes in prop::collection::vec(any::<u8>(), 0..200)) {
        let _ = CidRef::parse(&bytes);
        let _ = CidRef::parse_prefix(&bytes);
        let _ = Cid::from_bytes(&bytes);
        let _ = Cid::parse_text(&String::from_utf8_lossy(&bytes));
    }

    #[test]
    fn arbitrary_text_never_panics(text in "\\PC{0,200}") {
        let _ = Cid::parse_text(&text);
        let _ = Cid::parse_text(&format!("b{text}"));
    }

    #[test]
    fn accepted_bytes_are_canonical(bytes in prop::collection::vec(any::<u8>(), 0..100)) {
        if let Ok(c) = Cid::from_bytes(&bytes) {
            prop_assert_eq!(c.as_bytes(), &bytes[..]);
            prop_assert_eq!(Cid::parse_text(&c.to_string()).unwrap(), c);
        }
    }
}

#[test]
fn cid_parse_and_text_do_not_allocate() {
    let cid = Cid::for_block(DAG_CBOR, SHA2_256, b"zero").unwrap();
    let other = Cid::for_block(DAG_CBOR, BLAKE3, b"alloc").unwrap();
    let bytes = cid.as_bytes().to_vec();
    let text = cid.to_string();
    let info = pinc_tests::measure(|| {
        let r = CidRef::parse(&bytes).unwrap();
        let c = Cid::from_bytes(&bytes).unwrap();
        let mut buf = [0u8; MAX_TEXT_LEN];
        let t = c.encode_text(&mut buf).unwrap().len();
        let back = Cid::parse_text(&text).unwrap();
        let ord = cmp_text(r, other.as_ref());
        let made = Cid::for_block(DAG_CBOR, SHA2_256, b"zero").unwrap();
        std::hint::black_box((t, back, ord, made, r.verify(b"zero").is_ok()));
    });
    assert_eq!(info.count(), 0);
}
