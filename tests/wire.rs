//! Tests of vinc-wire: varint, reader, writer and the strict DAG-CBOR codec.
// Tests assert freely; the production lints on panics and indexing do not apply here.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use proptest::prelude::*;
use vinc_tests::SplitMix64;

vinc_tests::install_counting_allocator!();
use vinc_wire::cbor::{Decoder, Encoder, Item, MAX_DEPTH, MapReader};
use vinc_wire::{Reader, WireError, Writer, varint};

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

// ---------------------------------------------------------------- varint

#[test]
fn varint_boundaries() {
    let cases: [(u64, &[u8]); 7] = [
        (0, &[0x00]),
        (127, &[0x7f]),
        (128, &[0x80, 0x01]),
        ((1 << 14) - 1, &[0xff, 0x7f]),
        (1 << 14, &[0x80, 0x80, 0x01]),
        (300, &[0xac, 0x02]),
        ((1 << 63) - 1, &[0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]),
    ];
    for (value, bytes) in cases {
        let mut out = [0u8; 9];
        let n = varint::encode(value, &mut out).unwrap();
        assert_eq!(&out[..n], bytes, "encode {value}");
        assert_eq!(n, varint::encoded_len(value));
        assert_eq!(varint::decode(bytes), Ok((value, bytes.len())));
    }
}

#[test]
fn varint_rejections() {
    let mut out = [0u8; 16];
    assert_eq!(varint::encode(1 << 63, &mut out), Err(WireError::VarintOverflow));
    assert_eq!(varint::encode(u64::MAX, &mut out), Err(WireError::VarintOverflow));
    assert_eq!(varint::decode(&[0xff; 10]), Err(WireError::VarintTooLong));
    assert_eq!(varint::decode(&[0x80; 9]), Err(WireError::VarintTooLong));
    assert_eq!(varint::decode(&[0x80, 0x00]), Err(WireError::VarintNonMinimal));
    assert_eq!(varint::decode(&[0xff, 0x00]), Err(WireError::VarintNonMinimal));
    assert_eq!(varint::decode(&[0x80]), Err(WireError::Truncated { needed: 1 }));
    assert_eq!(varint::decode(&[]), Err(WireError::Truncated { needed: 1 }));
    // A trailing byte after a complete varint is left alone.
    assert_eq!(varint::decode(&[0x01, 0xff]), Ok((1, 1)));
    let mut small = [0u8; 1];
    assert_eq!(
        varint::encode(128, &mut small),
        Err(WireError::BufferTooSmall { needed: 1 })
    );
    assert_eq!(small, [0]);
}

proptest! {
    #[test]
    fn varint_round_trip(value in 0u64..(1 << 63)) {
        let mut out = [0u8; 9];
        let n = varint::encode(value, &mut out).unwrap();
        prop_assert_eq!(varint::decode(&out[..n]), Ok((value, n)));
    }

    #[test]
    fn varint_decode_is_canonical(bytes in proptest::collection::vec(any::<u8>(), 0..12)) {
        if let Ok((value, n)) = varint::decode(&bytes) {
            let mut out = [0u8; 9];
            prop_assert_eq!(varint::encode(value, &mut out), Ok(n));
            prop_assert_eq!(&out[..n], &bytes[..n]);
        }
    }
}

// -------------------------------------------------------- reader, writer

#[test]
fn reader_reads_and_bounds() {
    let data = [1, 0, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0, 0, 4, 0xac, 0x02, 9, 8];
    let mut r = Reader::new(&data);
    assert_eq!(r.read_u8(), Ok(1));
    assert_eq!(r.read_u16(), Ok(2));
    assert_eq!(r.read_u32(), Ok(3));
    assert_eq!(r.read_u64(), Ok(4));
    assert_eq!(r.read_varint(), Ok(300));
    assert_eq!(r.position(), 17);
    assert_eq!(r.remaining(), 2);
    assert_eq!(r.read_array::<2>(), Ok([9, 8]));
    assert!(r.is_empty());
    assert_eq!(r.read_u8(), Err(WireError::Truncated { needed: 1 }));
    assert_eq!(r.read_bytes(5), Err(WireError::Truncated { needed: 5 }));

    let mut r = Reader::new(&data[..3]);
    assert_eq!(r.read_u32(), Err(WireError::Truncated { needed: 1 }));
    assert_eq!(r.position(), 0, "a failed read consumes nothing");
    assert_eq!(r.read_bytes(3), Ok(&data[..3]));
    assert_eq!(
        Reader::new(&[0x80]).read_varint(),
        Err(WireError::Truncated { needed: 1 })
    );
}

#[test]
fn writer_writes_and_bounds() {
    let mut buf = [0u8; 8];
    let mut w = Writer::new(&mut buf);
    w.put_u8(1).unwrap();
    w.put_u16(0x0203).unwrap();
    w.put_u32(0x0405_0607).unwrap();
    assert_eq!(w.written(), &[1, 2, 3, 4, 5, 6, 7]);
    assert_eq!(w.put_u16(0), Err(WireError::BufferTooSmall { needed: 1 }));
    assert_eq!(w.put_varint(128), Err(WireError::BufferTooSmall { needed: 1 }));
    assert_eq!(w.put_varint(1 << 63), Err(WireError::VarintOverflow));
    assert_eq!(
        w.written(),
        &[1, 2, 3, 4, 5, 6, 7],
        "failed writes leave the content unchanged"
    );
    w.put_varint(5).unwrap();
    assert_eq!(w.written().len(), 8);
    assert_eq!(w.put_u8(0), Err(WireError::BufferTooSmall { needed: 1 }));

    let mut buf = [0u8; 16];
    let mut w = Writer::new(&mut buf);
    w.put_u64(1).unwrap();
    w.put_varint(300).unwrap();
    w.put_slice(&[7]).unwrap();
    assert_eq!(w.written(), &[0, 0, 0, 0, 0, 0, 0, 1, 0xac, 0x02, 7]);
}

// ------------------------------------------------------------------ cbor

#[derive(Debug, Clone, PartialEq)]
enum Val {
    U(u64),
    N(u64),
    B(Vec<u8>),
    T(String),
    A(Vec<Val>),
    M(Vec<(String, Val)>),
    Cid(Vec<u8>),
    Bool(bool),
    Null,
    F(f64),
}

fn encode_val(v: &Val, e: &mut Encoder<'_>) -> Result<(), WireError> {
    match v {
        Val::U(n) => e.unsigned(*n),
        Val::N(n) => e.negative(*n),
        Val::B(b) => e.bytes(b),
        Val::T(s) => e.text(s),
        Val::A(items) => {
            e.array(items.len() as u64)?;
            items.iter().try_for_each(|i| encode_val(i, e))
        }
        Val::M(entries) => {
            let mut keys = e.ordered_map(entries.len() as u64)?;
            for (k, val) in entries {
                keys.key(e, k)?;
                encode_val(val, e)?;
            }
            assert!(keys.is_complete());
            Ok(())
        }
        Val::Cid(c) => e.tag_cid(c),
        Val::Bool(b) => e.bool(*b),
        Val::Null => e.null(),
        Val::F(f) => e.float(*f),
    }
}

fn decode_val(d: &mut Decoder<'_>) -> Result<Val, WireError> {
    let mut probe = *d;
    if matches!(probe.next_item()?, Item::Map(_)) {
        let mut m = MapReader::new(d)?;
        let mut entries = Vec::new();
        while let Some(k) = m.next_key(d)? {
            entries.push((k.to_owned(), decode_val(d)?));
        }
        return Ok(Val::M(entries));
    }
    Ok(match d.next_item()? {
        Item::Unsigned(n) => Val::U(n),
        Item::Negative(n) => Val::N(n),
        Item::Bytes(b) => Val::B(b.to_vec()),
        Item::Text(s) => Val::T(s.to_owned()),
        Item::Array(n) => Val::A((0..n).map(|_| decode_val(d)).collect::<Result<_, _>>()?),
        Item::Tag(_) => match d.next_item()? {
            Item::Bytes([0, rest @ ..]) => Val::Cid(rest.to_vec()),
            _ => return Err(WireError::Unexpected("cid")),
        },
        Item::Bool(b) => Val::Bool(b),
        Item::Null => Val::Null,
        Item::Float(f) => Val::F(f),
        Item::Map(_) => return Err(WireError::Unexpected("map")),
    })
}

fn encode_to_vec(v: &Val) -> Vec<u8> {
    let mut buf = vec![0u8; 1 << 16];
    let mut e = Encoder::new(&mut buf);
    encode_val(v, &mut e).unwrap();
    let n = e.written().len();
    buf.truncate(n);
    buf
}

fn arb_val() -> impl Strategy<Value = Val> {
    let leaf = prop_oneof![
        any::<u64>().prop_map(Val::U),
        any::<u64>().prop_map(Val::N),
        proptest::collection::vec(any::<u8>(), 0..40).prop_map(Val::B),
        ".{0,12}".prop_map(Val::T),
        proptest::collection::vec(any::<u8>(), 0..40).prop_map(Val::Cid),
        any::<bool>().prop_map(Val::Bool),
        Just(Val::Null),
        any::<f64>().prop_filter("finite", |f| f.is_finite()).prop_map(Val::F),
    ];
    leaf.prop_recursive(4, 48, 5, |inner| {
        prop_oneof![
            proptest::collection::vec(inner.clone(), 0..5).prop_map(Val::A),
            proptest::collection::vec((".{0,6}", inner), 0..5).prop_map(|mut entries| {
                entries.sort_by(|a, b| (a.0.len(), a.0.as_bytes()).cmp(&(b.0.len(), b.0.as_bytes())));
                entries.dedup_by(|a, b| a.0 == b.0);
                Val::M(entries)
            }),
        ]
    })
}

#[test]
fn rfc8949_appendix_a_vectors_round_trip() {
    let cid_bytes: String = std::iter::repeat_n("ab", 36).collect();
    let vectors = [
        "00",
        "01",
        "0a",
        "17",
        "1818",
        "1819",
        "1864",
        "1903e8",
        "1a000f4240",
        "1b000000e8d4a51000",
        "1bffffffffffffffff",
        "20",
        "29",
        "3863",
        "3903e7",
        "3bffffffffffffffff",
        "fb3ff199999999999a",
        "fb7e37e43c8800759c",
        "fbc010666666666666",
        "fb7fefffffffffffff",
        "fb3ff0000000000000",
        "f4",
        "f5",
        "f6",
        "40",
        "4401020304",
        "60",
        "6161",
        "6449455446",
        "62225c",
        "62c3bc",
        "63e6b0b4",
        "64f0908591",
        "80",
        "83010203",
        "8301820203820405",
        "98190102030405060708090a0b0c0d0e0f101112131415161718181819",
        "a0",
        "a26161016162820203",
        "826161a161626163",
        "a56161614161626142616361436164614461656145",
    ];
    let cid = format!("d82a582500{cid_bytes}");
    for h in vectors.iter().copied().chain([cid.as_str()]) {
        let bytes = hex(h);
        let mut d = Decoder::new(&bytes);
        let v = decode_val(&mut d).unwrap_or_else(|e| panic!("{h}: {e}"));
        assert!(d.is_empty(), "{h}");
        assert_eq!(encode_to_vec(&v), bytes, "{h}");
        let mut d = Decoder::new(&bytes);
        d.skip_value().unwrap();
        assert!(d.is_empty(), "{h}");
    }
}

#[test]
fn every_item_kind_decodes() {
    let cases: Vec<(&str, Item<'_>)> = vec![
        ("0a", Item::Unsigned(10)),
        ("29", Item::Negative(9)),
        ("4101", Item::Bytes(&[1])),
        ("6161", Item::Text("a")),
        ("82", Item::Array(2)),
        ("a1", Item::Map(1)),
        ("f5", Item::Bool(true)),
        ("f4", Item::Bool(false)),
        ("f6", Item::Null),
        ("fb3ff8000000000000", Item::Float(1.5)),
    ];
    for (h, want) in cases {
        let bytes = hex(h);
        assert_eq!(Decoder::new(&bytes).next_item(), Ok(want), "{h}");
    }
}

fn first_error(h: &str) -> WireError {
    let bytes = hex(h);
    let by_item = (|| {
        let mut d = Decoder::new(&bytes);
        while !d.is_empty() {
            d.next_item()?;
        }
        Ok::<(), WireError>(())
    })();
    let by_skip = (|| {
        let mut d = Decoder::new(&bytes);
        while !d.is_empty() {
            d.skip_value()?;
        }
        Ok::<(), WireError>(())
    })();
    let e = by_skip.expect_err(h);
    if let Err(by_item) = by_item {
        assert_eq!(by_item, e, "{h}: skip_value agrees with next_item");
    }
    e
}

fn assert_non_canonical(hexes: &[&str], reason: &str) {
    for h in hexes {
        match first_error(h) {
            WireError::NonCanonical(r) => {
                assert!(r.contains(reason), "{h}: got {r:?}, wanted {reason:?}");
            }
            other => panic!("{h}: expected NonCanonical({reason}), got {other:?}"),
        }
    }
}

#[test]
fn rejects_non_minimal_arguments() {
    assert_non_canonical(
        &[
            "1800",
            "1817",
            "190001",
            "1900ff",
            "1a00000001",
            "1a0000ffff",
            "1b0000000000000001",
            "1b00000000ffffffff",
            "5800",
            "7800",
            "9800",
            "b800",
            "3800",
        ],
        "minimally",
    );
}

#[test]
fn rejects_indefinite_and_reserved() {
    assert_non_canonical(&["5f", "7f", "9f", "bf", "ff", "1f"], "indefinite");
    assert_non_canonical(&["1c", "1d", "1e", "fc"], "reserved");
}

#[test]
fn rejects_invalid_utf8() {
    assert_non_canonical(&["62c328", "61ff"], "UTF-8");
}

#[test]
fn rejects_non_64_bit_and_non_finite_floats() {
    assert_non_canonical(&["f93c00", "fa47c35000", "f97e00"], "64-bit");
    assert_non_canonical(
        &["fb7ff8000000000000", "fb7ff0000000000000", "fbfff0000000000000"],
        "NaN",
    );
    let mut buf = [0u8; 16];
    assert!(matches!(
        Encoder::new(&mut buf).float(f64::NAN),
        Err(WireError::NonCanonical(_))
    ));
    assert!(matches!(
        Encoder::new(&mut buf).float(f64::INFINITY),
        Err(WireError::NonCanonical(_))
    ));
}

#[test]
fn rejects_other_tags_and_bad_cids() {
    assert_non_canonical(
        &[
            "c074323031332d30332d32315432303a30343a30305a",
            "c11a514b67b0",
            "d74401020304",
            "d818456449455446",
        ],
        "tag 42",
    );
    assert_non_canonical(
        &["d82a01", "d82a4101", "d82a40", "d82ad82a4100", "d82a6100", "d82a80"],
        "tag 42",
    );
}

#[test]
fn rejects_simple_values() {
    assert_non_canonical(&["f7", "f0", "f820", "e0", "f3", "f8ff"], "simple");
}

#[test]
fn rejects_bad_map_keys() {
    assert_non_canonical(&["a10102", "a1410102", "a1f402"], "text strings");
    assert_non_canonical(&["a2616101616102", "a26261610162616102"], "duplicate");
    assert_non_canonical(&["a2616201616101", "a262616101616202"], "out of order");
    // "b" then "aa" is canonical (shorter first); "aa" then "b" is not.
    first_ok("a261620162616102");
}

fn first_ok(h: &str) {
    let bytes = hex(h);
    let mut d = Decoder::new(&bytes);
    d.skip_value().unwrap();
    assert!(d.is_empty());
}

#[test]
fn rejects_truncation() {
    for h in ["18", "19ff", "4401", "6261", "82", "a1", "a16161", "d82a", "fb3ff0"] {
        let bytes = hex(h);
        let mut d = Decoder::new(&bytes);
        let r = d.skip_value();
        assert!(matches!(r, Err(WireError::Truncated { .. })), "{h}: {r:?}");
    }
    // A length claiming more than the input holds.
    assert!(matches!(
        Decoder::new(&hex("5bffffffffffffffff")).next_item(),
        Err(WireError::Truncated { .. })
    ));
}

#[test]
fn nested_skip_value_validates_and_positions() {
    // [1, [2, {"a": [3]}], 4] followed by 5.
    let bytes = hex("83018202a1616181030405");
    let mut d = Decoder::new(&bytes);
    d.skip_value().unwrap();
    assert_eq!(d.position(), bytes.len() - 1);
    assert_eq!(d.next_item(), Ok(Item::Unsigned(5)));

    // A violation deep inside a skipped value is still found.
    assert_non_canonical(&["8201a2616101616102", "82018201a1f402", "8201d82a4101"], "");
}

#[test]
fn depth_limit() {
    let mut deep = vec![0x81; MAX_DEPTH];
    deep.push(0x00);
    let mut d = Decoder::new(&deep);
    d.skip_value().unwrap();
    assert!(d.is_empty());

    let mut too_deep = vec![0x81; MAX_DEPTH + 1];
    too_deep.push(0x00);
    assert_eq!(Decoder::new(&too_deep).skip_value(), Err(WireError::DepthExceeded));

    let mut maps = Vec::new();
    for _ in 0..=MAX_DEPTH {
        maps.extend_from_slice(&[0xa1, 0x61, 0x61]);
    }
    maps.push(0x00);
    assert_eq!(Decoder::new(&maps).skip_value(), Err(WireError::DepthExceeded));
}

#[test]
fn map_reader_iterates_in_order() {
    let bytes = hex("a36162016261610262636403");
    let mut d = Decoder::new(&bytes);
    let mut m = MapReader::new(&mut d).unwrap();
    assert_eq!(m.remaining(), 3);
    let mut seen = Vec::new();
    while let Some(k) = m.next_key(&mut d).unwrap() {
        seen.push((k, d.next_item().unwrap()));
    }
    assert_eq!(
        seen,
        [
            ("b", Item::Unsigned(1)),
            ("aa", Item::Unsigned(2)),
            ("cd", Item::Unsigned(3))
        ]
    );
    assert_eq!(m.next_key(&mut d), Ok(None));

    let mut d = Decoder::new(&[0x80]);
    assert!(matches!(MapReader::new(&mut d), Err(WireError::Unexpected(_))));

    let bytes = hex("a2616201616101");
    let mut d = Decoder::new(&bytes);
    let mut m = MapReader::new(&mut d).unwrap();
    m.next_key(&mut d).unwrap();
    d.skip_value().unwrap();
    assert!(matches!(m.next_key(&mut d), Err(WireError::NonCanonical(_))));
}

#[test]
fn encoder_orders_and_bounds() {
    let mut buf = [0u8; 64];
    let mut e = Encoder::new(&mut buf);
    let mut keys = e.ordered_map(2).unwrap();
    keys.key(&mut e, "b").unwrap();
    e.unsigned(1).unwrap();
    let before = e.written().len();
    assert!(
        matches!(keys.key(&mut e, "a"), Err(WireError::NonCanonical(_))),
        "out of order"
    );
    assert!(
        matches!(keys.key(&mut e, "b"), Err(WireError::NonCanonical(_))),
        "duplicate"
    );
    assert_eq!(e.written().len(), before, "rejected keys write nothing");
    keys.key(&mut e, "aa").unwrap();
    e.unsigned(2).unwrap();
    assert!(keys.is_complete());
    assert!(
        matches!(keys.key(&mut e, "zz"), Err(WireError::NonCanonical(_))),
        "beyond declared length"
    );
    assert_eq!(e.written(), hex("a261620162616102"));

    let mut small = [0u8; 3];
    let mut e = Encoder::new(&mut small);
    assert_eq!(e.text("abc"), Err(WireError::BufferTooSmall { needed: 1 }));
    assert_eq!(e.tag_cid(&[1, 2, 3]), Err(WireError::BufferTooSmall { needed: 4 }));
    assert_eq!(e.float(1.0), Err(WireError::BufferTooSmall { needed: 6 }));
    assert!(e.written().is_empty(), "failed encodes write nothing");
    e.null().unwrap();
    e.bool(true).unwrap();
    assert_eq!(e.written(), [0xf6, 0xf5]);
}

#[test]
fn encoder_emits_minimal_headers() {
    for (n, want) in [
        (23u64, "17"),
        (24, "1818"),
        (255, "18ff"),
        (256, "190100"),
        (65535, "19ffff"),
        (65536, "1a00010000"),
        (u64::from(u32::MAX), "1affffffff"),
        (1 << 32, "1b0000000100000000"),
    ] {
        assert_eq!(encode_to_vec(&Val::U(n)), hex(want), "{n}");
    }
}

// ------------------------------------------------------------ robustness

fn drain(bytes: &[u8], by_skip: bool) {
    let mut d = Decoder::new(bytes);
    while !d.is_empty() {
        let before = d.position();
        let r = if by_skip {
            d.skip_value()
        } else {
            d.next_item().map(drop)
        };
        if r.is_err() {
            return;
        }
        assert!(d.position() > before, "a successful step must make progress");
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn arbitrary_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..4096)) {
        drain(&bytes, false);
        drain(&bytes, true);
    }

    #[test]
    fn mutated_documents_never_panic(v in arb_val(), at in any::<usize>(), flip in 1u8..) {
        let mut bytes = encode_to_vec(&v);
        let i = at % bytes.len();
        bytes[i] ^= flip;
        drain(&bytes, false);
        drain(&bytes, true);
    }

    #[test]
    fn encoded_values_decode_back(v in arb_val()) {
        let bytes = encode_to_vec(&v);
        let mut d = Decoder::new(&bytes);
        prop_assert_eq!(decode_val(&mut d), Ok(v));
        prop_assert!(d.is_empty());
        let mut d = Decoder::new(&bytes);
        prop_assert_eq!(d.skip_value(), Ok(()));
        prop_assert!(d.is_empty());
    }
}

#[test]
fn seeded_noise_never_panics() {
    let mut rng = SplitMix64::new(0x5eed);
    let mut buf = [0u8; 256];
    for _ in 0..2000 {
        rng.fill(&mut buf);
        drain(&buf, true);
        drain(&buf, false);
    }
}

// ------------------------------------------------------------ allocation

#[test]
fn decoding_a_nested_document_allocates_nothing() {
    let doc = Val::M(vec![
        (
            "a".into(),
            Val::A(vec![Val::U(1), Val::N(2), Val::T("hello".into()), Val::F(1.5)]),
        ),
        (
            "bb".into(),
            Val::M(vec![
                ("x".into(), Val::Cid(vec![1; 36])),
                ("yy".into(), Val::A(vec![Val::Null, Val::Bool(true)])),
            ]),
        ),
        ("ccc".into(), Val::B(vec![9; 100])),
    ]);
    let bytes = encode_to_vec(&doc);

    let info = vinc_tests::measure(|| {
        let mut d = Decoder::new(&bytes);
        let mut items = 0usize;
        while !d.is_empty() {
            d.next_item().unwrap();
            items += 1;
        }
        assert!(items > 10);
        let mut d = Decoder::new(&bytes);
        d.skip_value().unwrap();
        let mut d = Decoder::new(&bytes);
        let mut m = MapReader::new(&mut d).unwrap();
        while m.next_key(&mut d).unwrap().is_some() {
            d.skip_value().unwrap();
        }
    });
    assert_eq!(info.count(), 0, "decoding must not touch the heap");
}
