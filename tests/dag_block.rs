//! Tests of pinc-dag's `DefraDB` block format.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::type_complexity,
    clippy::redundant_closure_for_method_calls
)]

use proptest::prelude::*;
use pinc_dag::block::{BlockError, BlockParts, BlockRef, Link, encode_block};
use pinc_dag::cid::{Cid, CidError, DAG_CBOR, RAW, SHA2_256};
use pinc_wire::WireError;
use pinc_wire::cbor::Decoder;

mod golden;

pinc_tests::install_counting_allocator!();

/// Re-encode a parsed block from its parts.
fn reencode(block: &BlockRef<'_>) -> Vec<u8> {
    let mut heads: Vec<Cid> = block.heads().map(|c| c.into_owned()).collect();
    let mut links: Vec<Link<'_>> = block
        .links()
        .map(|l| Link {
            name: l.name,
            cid: l.cid.into_owned(),
        })
        .collect();
    let mut parts = BlockParts {
        delta: block.delta(),
        heads: &mut heads,
        links: &mut links,
        encryption: block.encryption().map(|c| c.into_owned()),
        signature: block.signature().map(|c| c.into_owned()),
    };
    let mut out = vec![0; parts.encoded_len()];
    let n = encode_block(&mut out, &mut parts).unwrap();
    assert_eq!(n, out.len());
    out
}

fn cid_of(seed: u8) -> Cid {
    Cid::for_block(DAG_CBOR, SHA2_256, &[seed]).unwrap()
}

const DELTA: &[u8] = &[0xa1, 0x61, b'a', 0x01];

fn encode(heads: &mut [Cid], links: &mut [Link<'_>], enc: Option<Cid>, sig: Option<Cid>) -> Vec<u8> {
    let mut parts = BlockParts {
        delta: DELTA,
        heads,
        links,
        encryption: enc,
        signature: sig,
    };
    let mut out = vec![0; parts.encoded_len()];
    assert_eq!(encode_block(&mut out, &mut parts).unwrap(), out.len());
    out
}

#[test]
fn golden_blocks_parse_re_encode_and_hash_identically() {
    for (name, bytes, text) in golden::BLOCKS {
        let block = BlockRef::parse(bytes).unwrap_or_else(|e| panic!("{name}: {e}"));
        assert_eq!(reencode(&block), *bytes, "{name}");
        let cid = Cid::for_block(DAG_CBOR, SHA2_256, bytes).unwrap();
        assert_eq!(cid.to_string(), *text, "{name}");
        // The delta is one complete item that starts right after the `delta` key.
        let mut d = Decoder::new(block.delta());
        d.skip_value().unwrap();
        assert!(d.is_empty(), "{name}");
        assert!(block.encryption().is_none() && block.signature().is_none(), "{name}");
    }
}

#[test]
fn golden_block_structure() {
    let head = BlockRef::parse(golden::GO_BLOCK_WITH_ONE_HEAD_BYTES).unwrap();
    let heads: Vec<String> = head.heads().map(|c| c.to_string()).collect();
    assert_eq!(heads, [golden::GO_LWW_SIMPLE_CID]);
    assert_eq!(head.links().count(), 0);
    assert_eq!(head.all_links().count(), 1);

    let links = BlockRef::parse(golden::GO_COMPOSITE_BLOCK_WITH_LINKS_BYTES).unwrap();
    let l: Vec<_> = links.links().collect();
    assert_eq!(l.len(), 1);
    assert_eq!(l[0].name, "age");
    assert_eq!(links.heads().count(), 0);
    assert_eq!(links.references().count(), 1);

    // A field block has the delta and nothing else.
    let field = BlockRef::parse(golden::GO_LWW_SIMPLE_BYTES).unwrap();
    assert_eq!(field.references().count(), 0);
    assert_eq!(field.delta().first(), Some(&0xa1));
}

#[test]
fn golden_signature_blocks_have_their_cids() {
    for (name, bytes, text) in golden::SIGNATURES {
        let mut d = Decoder::new(bytes);
        d.skip_value().unwrap();
        assert!(d.is_empty(), "{name}");
        assert_eq!(
            Cid::for_block(DAG_CBOR, SHA2_256, bytes).unwrap().to_string(),
            *text,
            "{name}"
        );
    }
}

#[test]
fn signed_encrypted_block_round_trips() {
    let (enc, sig) = (cid_of(1), cid_of(2));
    let mut heads = [cid_of(3), cid_of(4), cid_of(5)];
    let mut links = [
        Link {
            name: "b",
            cid: cid_of(6),
        },
        Link {
            name: "a",
            cid: cid_of(6),
        },
        Link {
            name: "z",
            cid: cid_of(7),
        },
    ];
    let bytes = encode(&mut heads, &mut links, Some(enc), Some(sig));
    let block = BlockRef::parse(&bytes).unwrap();
    assert_eq!(block.encryption().unwrap().into_owned(), enc);
    assert_eq!(block.signature().unwrap().into_owned(), sig);
    assert_eq!(block.delta(), DELTA);
    // The encoder sorted its inputs in place, and the parser reads them back in that order.
    assert_eq!(block.heads().map(|c| c.into_owned()).collect::<Vec<_>>(), heads);
    let back: Vec<_> = block.links().map(|l| (l.name, l.cid.into_owned())).collect();
    let want: Vec<_> = links.iter().map(|l| (l.name, l.cid)).collect();
    assert_eq!(back, want);
    assert_eq!(block.references().count(), 3 + 3 + 2);
    assert_eq!(block.all_links().count(), 3 + 3);
    assert_eq!(reencode(&block), bytes);
}

#[test]
fn heads_and_links_order_by_cid_text_then_name() {
    let mut heads = [cid_of(9), cid_of(8), cid_of(7)];
    let mut by_bytes = heads;
    by_bytes.sort();
    let mut links = [
        Link {
            name: "b",
            cid: cid_of(1),
        },
        Link {
            name: "a",
            cid: cid_of(1),
        },
        Link {
            name: "c",
            cid: cid_of(0),
        },
    ];
    let bytes = encode(&mut heads, &mut links, None, None);
    assert!(heads.windows(2).all(|w| w[0].to_string() < w[1].to_string()));
    for pair in links.windows(2) {
        let key = |l: &Link<'static>| (l.cid.to_string(), l.name);
        assert!(key(&pair[0]) < key(&pair[1]));
    }
    // Byte order is not text order for every set of CIDs; the parser follows text order only.
    assert!(BlockRef::parse(&bytes).is_ok());
    let found = (0..=255u8)
        .flat_map(|a| (0..=255u8).map(move |b| (a, b)))
        .find(|&(a, b)| {
            let (x, y) = (cid_of(a), cid_of(b));
            a != b && x.cmp_text(&y) != x.cmp(&y)
        });
    let (a, b) = found.expect("two CIDs whose byte and text order differ");
    let (mut lo, mut hi) = (cid_of(a), cid_of(b));
    if lo.cmp_text(&hi).is_gt() {
        std::mem::swap(&mut lo, &mut hi);
    }
    let in_text_order = encode_heads_raw(&[lo, hi]);
    let in_wrong_order = encode_heads_raw(&[hi, lo]);
    assert!(BlockRef::parse(&in_text_order).is_ok());
    assert_eq!(
        BlockRef::parse(&in_wrong_order).unwrap_err(),
        BlockError::Unordered("heads")
    );
}

/// A block with the given heads written as given, without sorting.
fn encode_heads_raw(heads: &[Cid]) -> Vec<u8> {
    use pinc_wire::cbor::Encoder;
    let mut buf = vec![0u8; 1024];
    let mut e = Encoder::new(&mut buf);
    let mut keys = e.ordered_map(2).unwrap();
    keys.key(&mut e, "delta").unwrap();
    e.map(0).unwrap();
    keys.key(&mut e, "heads").unwrap();
    e.array(heads.len() as u64).unwrap();
    for h in heads {
        e.tag_cid(h.as_bytes()).unwrap();
    }
    e.written().to_vec()
}

#[test]
fn parser_rejects_what_defradb_rejects() {
    let good = encode(&mut [cid_of(1)], &mut [], None, None);
    let mut trailing = good.clone();
    trailing.push(0);
    assert_eq!(BlockRef::parse(&trailing).unwrap_err(), BlockError::TrailingBytes);
    // A map without a delta.
    assert_eq!(BlockRef::parse(&[0xa0]).unwrap_err(), BlockError::MissingDelta);
    // Duplicate heads.
    let h = cid_of(1);
    assert_eq!(
        BlockRef::parse(&encode_heads_raw(&[h, h])).unwrap_err(),
        BlockError::Unordered("heads")
    );
    // Not a map, truncated, a head that is not a CID.
    assert!(BlockRef::parse(&[0x80]).is_err());
    assert!(BlockRef::parse(&good[..good.len() - 1]).is_err());
    assert!(
        BlockRef::parse(&[
            0xa2, 0x65, b'd', b'e', b'l', b't', b'a', 0xa0, 0x65, b'h', b'e', b'a', b'd', b's', 0x81, 0x01
        ])
        .is_err()
    );
    // A signature that is not a CID.
    let mut bad = vec![0xa2, 0x65];
    bad.extend_from_slice(b"delta");
    bad.push(0xa0);
    bad.push(0x69);
    bad.extend_from_slice(b"signature");
    bad.push(0x01);
    assert!(BlockRef::parse(&bad).is_err());
}

#[test]
fn unknown_keys_null_and_empty_arrays_are_accepted_as_defradb_does() {
    // {"delta": {}, "heads": null, "links": [], "zzzzzz": 1}
    let mut b = vec![0xa4, 0x65];
    b.extend_from_slice(b"delta");
    b.extend_from_slice(&[0xa0, 0x65]);
    b.extend_from_slice(b"heads");
    b.extend_from_slice(&[0xf6, 0x65]);
    b.extend_from_slice(b"links");
    b.extend_from_slice(&[0x80, 0x66]);
    b.extend_from_slice(b"zzzzzz");
    b.push(0x01);
    let block = BlockRef::parse(&b).unwrap();
    assert_eq!(block.references().count(), 0);
    // It re-encodes to the canonical form, which is shorter.
    assert!(reencode(&block).len() < b.len());
}

#[test]
fn encoder_validates_and_reports_sizes() {
    let mut parts = BlockParts {
        delta: &[0x01, 0x02],
        heads: &mut [],
        links: &mut [],
        encryption: None,
        signature: None,
    };
    let mut out = [0u8; 64];
    assert!(matches!(
        encode_block(&mut out, &mut parts),
        Err(BlockError::Wire(WireError::Unexpected(_)))
    ));
    parts.delta = &[0xa1, 0x01];
    assert!(matches!(encode_block(&mut out, &mut parts), Err(BlockError::Wire(_))));
    parts.delta = DELTA;
    assert_eq!(encode_block(&mut out, &mut parts).unwrap(), parts.encoded_len());

    let h = cid_of(1);
    let mut dup = [h, h];
    let mut parts = BlockParts {
        delta: DELTA,
        heads: &mut dup,
        links: &mut [],
        encryption: None,
        signature: None,
    };
    assert_eq!(
        encode_block(&mut out, &mut parts).unwrap_err(),
        BlockError::Unordered("heads")
    );
    let mut same = [Link { name: "a", cid: h }, Link { name: "a", cid: h }];
    let mut parts = BlockParts {
        delta: DELTA,
        heads: &mut [],
        links: &mut same,
        encryption: None,
        signature: None,
    };
    assert_eq!(
        encode_block(&mut out, &mut parts).unwrap_err(),
        BlockError::Unordered("links")
    );

    // Every too-small buffer fails and reports the shortfall; the exact size succeeds.
    let mut heads = [cid_of(1), cid_of(2)];
    let mut links = [Link {
        name: "name",
        cid: cid_of(3),
    }];
    let mut parts = BlockParts {
        delta: DELTA,
        heads: &mut heads,
        links: &mut links,
        encryption: Some(cid_of(4)),
        signature: Some(cid_of(5)),
    };
    let len = parts.encoded_len();
    for n in 0..len {
        let mut small = vec![0u8; n];
        assert_eq!(
            encode_block(&mut small, &mut parts).unwrap_err(),
            BlockError::Wire(WireError::BufferTooSmall { needed: len - n })
        );
    }
    assert_eq!(encode_block(&mut vec![0u8; len], &mut parts).unwrap(), len);
}

#[test]
fn raw_codec_cids_are_carried() {
    let r = Cid::for_block(RAW, SHA2_256, b"x").unwrap();
    let bytes = encode(&mut [r], &mut [], None, None);
    let block = BlockRef::parse(&bytes).unwrap();
    assert_eq!(block.heads().next().unwrap().codec(), RAW);
}

#[test]
fn invalid_cid_inside_a_block_is_a_cid_error() {
    // A head whose CID has a 31 byte sha2-256 digest.
    let mut cid = vec![0x00, 1, 0x71, 0x12, 31];
    cid.extend_from_slice(&[0; 31]);
    let mut b = vec![0xa2, 0x65];
    b.extend_from_slice(b"delta");
    b.extend_from_slice(&[0xa0, 0x65]);
    b.extend_from_slice(b"heads");
    b.extend_from_slice(&[0x81, 0xd8, 0x2a, 0x58, cid.len() as u8]);
    b.extend_from_slice(&cid);
    assert_eq!(
        BlockRef::parse(&b).unwrap_err(),
        BlockError::Cid(CidError::DigestLenMismatch { hash: 0x12, len: 31 })
    );
}

fn arb_parts() -> impl Strategy<Value = (Vec<u8>, Vec<Cid>, Vec<(String, u8)>, Option<u8>, Option<u8>)> {
    (
        prop::collection::vec(any::<u8>(), 0..8).prop_map(|v| {
            // delta {"k": bytes}
            let mut d = vec![0xa1, 0x61, b'k', 0x40 | v.len() as u8];
            d.extend(v);
            d
        }),
        prop::collection::vec(any::<u8>().prop_map(cid_of), 0..6),
        prop::collection::vec(("[a-z]{0,30}", any::<u8>()), 0..6),
        prop::option::of(any::<u8>()),
        prop::option::of(any::<u8>()),
    )
}

proptest! {
    #[test]
    fn encode_then_parse_round_trips((delta, heads, links, enc, sig) in arb_parts()) {
        let mut heads = heads;
        heads.sort_by(Cid::cmp_text);
        heads.dedup();
        let mut links: Vec<Link<'_>> = links.iter().map(|(n, s)| Link { name: n, cid: cid_of(*s) }).collect();
        links.sort_by(|a, b| a.cid.cmp_text(&b.cid).then_with(|| a.name.cmp(b.name)));
        links.dedup_by(|a, b| a.cid == b.cid && a.name == b.name);
        let mut shuffled_heads: Vec<Cid> = heads.iter().rev().copied().collect();
        let mut shuffled_links: Vec<Link<'_>> = links.iter().rev().copied().collect();
        let mut parts = BlockParts {
            delta: &delta,
            heads: &mut shuffled_heads,
            links: &mut shuffled_links,
            encryption: enc.map(cid_of),
            signature: sig.map(cid_of),
        };
        let mut out = vec![0; parts.encoded_len()];
        prop_assert_eq!(encode_block(&mut out, &mut parts).unwrap(), out.len());
        let block = BlockRef::parse(&out).unwrap();
        prop_assert_eq!(block.delta(), &delta[..]);
        prop_assert_eq!(block.heads().map(|c| c.into_owned()).collect::<Vec<_>>(), heads);
        let got: Vec<_> = block.links().map(|l| (l.name.to_string(), l.cid.into_owned())).collect();
        let want: Vec<_> = links.iter().map(|l| (l.name.to_string(), l.cid)).collect();
        prop_assert_eq!(got, want);
        prop_assert_eq!(block.encryption().map(|c| c.into_owned()), enc.map(cid_of));
        prop_assert_eq!(block.signature().map(|c| c.into_owned()), sig.map(cid_of));
        prop_assert_eq!(reencode(&block), out);
    }

    #[test]
    fn arbitrary_bytes_never_panic(bytes in prop::collection::vec(any::<u8>(), 0..300)) {
        if let Ok(b) = BlockRef::parse(&bytes) {
            let _ = b.references().count();
        }
    }

    #[test]
    fn mutated_golden_blocks_never_panic(which in 0..golden::BLOCKS.len(), at in any::<usize>(), byte in any::<u8>()) {
        let mut bytes = golden::BLOCKS[which].1.to_vec();
        let i = at % bytes.len();
        bytes[i] = byte;
        if let Ok(b) = BlockRef::parse(&bytes) {
            let _ = (b.references().count(), reencode(&b).len());
        }
    }

    #[test]
    fn accepted_golden_prefixes_are_never_partial(which in 0..golden::BLOCKS.len(), cut in any::<usize>()) {
        let full = golden::BLOCKS[which].1;
        let cut = cut % full.len();
        prop_assert!(BlockRef::parse(&full[..cut]).is_err());
    }
}

#[test]
fn parse_and_encode_do_not_allocate() {
    let mut heads = [cid_of(1), cid_of(2)];
    let mut links = [Link {
        name: "f",
        cid: cid_of(3),
    }];
    let bytes = encode(&mut heads.clone(), &mut links.clone(), Some(cid_of(4)), Some(cid_of(5)));
    let mut out = [0u8; 512];
    let info = pinc_tests::measure(|| {
        let block = BlockRef::parse(&bytes).unwrap();
        let n = block.references().count() + block.heads().count() + block.links().count();
        let mut parts = BlockParts {
            delta: DELTA,
            heads: &mut heads,
            links: &mut links,
            encryption: block.encryption().map(|c| c.into_owned()),
            signature: block.signature().map(|c| c.into_owned()),
        };
        let written = encode_block(&mut out, &mut parts).unwrap();
        std::hint::black_box((n, written));
    });
    assert_eq!(info.count(), 0);
    for (_, bytes, _) in golden::BLOCKS {
        let info = pinc_tests::measure(|| {
            std::hint::black_box(BlockRef::parse(bytes).unwrap().references().count());
        });
        assert_eq!(info.count(), 0);
    }
}
