//! Tests of vinc-dag's CAR v1 reader, incremental decoder and writer.
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
use vinc_dag::car::{CarDecoder, CarError, CarReader, CarWriter, Decoded};
use vinc_dag::cid::{BLAKE3, Cid, CidError, DAG_CBOR, RAW, SHA2_256};
use vinc_wire::WireError;

mod golden;

const MAX: usize = 1 << 16;

fn golden_cids() -> Vec<Cid> {
    golden::BLOCKS
        .iter()
        .map(|(_, b, _)| Cid::for_block(DAG_CBOR, SHA2_256, b).unwrap())
        .collect()
}

fn build(roots: &[Cid], sections: &[(Cid, Vec<u8>)]) -> Vec<u8> {
    let total = CarWriter::header_len(roots)
        + sections
            .iter()
            .map(|(c, b)| CarWriter::section_len(c.as_ref(), b))
            .sum::<usize>();
    let mut buf = vec![0; total];
    let mut w = CarWriter::new(&mut buf, roots).unwrap();
    for (c, b) in sections {
        w.section(c.as_ref(), b).unwrap();
    }
    assert_eq!(w.written().len(), total);
    buf
}

fn golden_car() -> (Vec<u8>, Vec<Cid>) {
    let cids = golden_cids();
    let sections: Vec<_> = cids
        .iter()
        .zip(golden::BLOCKS)
        .map(|(c, (_, b, _))| (*c, b.to_vec()))
        .collect();
    (build(&cids[..2], &sections), cids)
}

#[test]
fn golden_blocks_round_trip_through_a_car() {
    let (car, cids) = golden_car();
    let reader = CarReader::new(&car, MAX).unwrap().with_verify(true);
    assert_eq!(reader.roots().map(|c| c.into_owned()).collect::<Vec<_>>(), cids[..2]);
    let got: Vec<_> = reader.sections().collect::<Result<_, _>>().unwrap();
    assert_eq!(got.len(), golden::BLOCKS.len());
    for ((cid, block), (want, (name, bytes, text))) in got.iter().zip(cids.iter().zip(golden::BLOCKS)) {
        assert_eq!(cid.to_string(), *text, "{name}");
        assert_eq!(cid.into_owned(), *want, "{name}");
        assert_eq!(block, bytes, "{name}");
    }
}

#[test]
fn header_bytes_are_the_canonical_car_v1_header() {
    let cid = Cid::for_block(DAG_CBOR, SHA2_256, b"x").unwrap();
    let car = build(&[cid], &[]);
    // varint(len), map(2), "roots", array(1), tag 42 over 0x00 + CID, "version", 1.
    let mut want = vec![0xa2, 0x65];
    want.extend_from_slice(b"roots");
    want.extend_from_slice(&[0x81, 0xd8, 0x2a, 0x58, 0x25, 0x00]);
    want.extend_from_slice(cid.as_bytes());
    want.push(0x67);
    want.extend_from_slice(b"version");
    want.push(0x01);
    let mut full = vec![want.len() as u8];
    full.extend(want);
    assert_eq!(car, full);
}

#[test]
fn truncation_at_every_offset_is_a_typed_error_or_a_shorter_car() {
    let (car, _) = golden_car();
    let boundaries = {
        let r = CarReader::new(&car, MAX).unwrap();
        let mut ends = vec![CarWriter::header_len(&golden_cids()[..2])];
        for s in r.sections() {
            let (c, b) = s.unwrap();
            ends.push(ends.last().unwrap() + CarWriter::section_len(c, b));
        }
        ends
    };
    assert_eq!(*boundaries.last().unwrap(), car.len());
    for cut in 0..car.len() {
        let on_boundary = boundaries.contains(&cut);
        let outcome = CarReader::new(&car[..cut], MAX).and_then(|r| r.sections().collect::<Result<Vec<_>, _>>());
        match outcome {
            Ok(sections) => assert!(on_boundary && sections.len() < golden::BLOCKS.len(), "cut {cut}"),
            Err(e) => {
                assert!(!on_boundary, "cut {cut}: {e}");
                assert!(
                    matches!(e, CarError::Truncated { needed } if needed > 0)
                        || matches!(e, CarError::Wire(WireError::Truncated { .. }))
                        || matches!(e, CarError::Cid(_)),
                    "cut {cut}: {e:?}"
                );
            }
        }
    }
}

#[test]
fn oversize_is_refused_before_the_body_is_needed() {
    let (car, _) = golden_car();
    assert!(matches!(
        CarReader::new(&car, 10),
        Err(CarError::TooLarge { max: 10, .. })
    ));
    let header = CarWriter::header_len(&golden_cids()[..2]);
    let biggest = golden::BLOCKS.iter().map(|b| b.1.len()).max().unwrap() + 36;
    let r = CarReader::new(&car, biggest - 1).and_then(|r| r.sections().collect::<Result<Vec<_>, _>>());
    assert!(matches!(r, Err(CarError::TooLarge { .. })));
    assert!(
        CarReader::new(&car, biggest.max(header))
            .unwrap()
            .sections()
            .all(|s| s.is_ok())
    );
    // A hostile length of 2^40 with no body behind it is TooLarge, not Truncated.
    let mut hostile = car[..header].to_vec();
    hostile.extend_from_slice(&[0x80, 0x80, 0x80, 0x80, 0x80, 0x20]);
    let first = CarReader::new(&hostile, MAX).unwrap().sections().next().unwrap();
    assert!(matches!(first, Err(CarError::TooLarge { len, .. }) if len == 1 << 40));
}

#[test]
fn verify_catches_a_corrupt_block() {
    let (mut car, _) = golden_car();
    let last = car.len() - 1;
    car[last] ^= 1;
    let r = CarReader::new(&car, MAX).unwrap();
    assert!(r.sections().all(|s| s.is_ok()));
    let err = r.with_verify(true).sections().find_map(Result::err).unwrap();
    assert_eq!(err, CarError::Cid(CidError::DigestMismatch));
}

#[test]
fn header_must_be_exactly_roots_and_version_one() {
    let cid = Cid::for_block(DAG_CBOR, SHA2_256, b"x").unwrap();
    let car = build(&[cid], &[]);
    let body = &car[1..];
    let with = |edit: &dyn Fn(&mut Vec<u8>)| {
        let mut b = body.to_vec();
        edit(&mut b);
        let mut out = vec![b.len() as u8];
        out.extend(b);
        CarReader::new(&out, MAX).map(|_| ())
    };
    assert!(with(&|_| {}).is_ok());
    let last = body.len() - 1;
    assert_eq!(with(&|b| b[last] = 2), Err(CarError::BadHeader("version is not 1")));
    assert_eq!(
        with(&|b| b.push(0)),
        Err(CarError::BadHeader("bytes follow the header map"))
    );
    assert!(matches!(with(&|b| b[0] = 0xa1), Err(CarError::BadHeader(_))));
    assert!(CarReader::new(&[0x01, 0xa0], MAX).is_err());
    assert!(CarReader::new(&[], MAX).is_err());
}

#[test]
fn incremental_decoder_matches_the_reader_at_every_chunk_size() {
    let (car, cids) = golden_car();
    let want: Vec<_> = CarReader::new(&car, MAX)
        .unwrap()
        .sections()
        .map(|s| s.unwrap().1.to_vec())
        .collect();
    for chunk in [1, 2, 3, 7, 16, 100, car.len()] {
        let mut dec = CarDecoder::new(MAX).with_verify(true);
        let mut buf: Vec<u8> = Vec::new();
        let mut high_water = 0;
        let (mut roots, mut blocks) = (Vec::new(), Vec::new());
        let mut input = car.chunks(chunk);
        loop {
            match dec.decode(&buf).unwrap() {
                Decoded::NeedMore(n) => {
                    assert!(n > 0);
                    let Some(next) = input.next() else { break };
                    buf.extend_from_slice(next);
                    high_water = high_water.max(buf.len());
                }
                Decoded::Header { consumed, roots: r } => {
                    roots = r.map(|c| c.into_owned()).collect();
                    buf.drain(..consumed);
                }
                Decoded::Section { consumed, cid, block } => {
                    blocks.push((cid.into_owned(), block.to_vec()));
                    buf.drain(..consumed);
                }
            }
        }
        assert!(buf.is_empty(), "chunk {chunk}");
        assert_eq!(roots, cids[..2], "chunk {chunk}");
        assert_eq!(
            blocks.iter().map(|b| b.1.clone()).collect::<Vec<_>>(),
            want,
            "chunk {chunk}"
        );
        let largest = golden::BLOCKS.iter().map(|b| b.1.len()).max().unwrap() + 36 + 9;
        assert!(high_water <= largest + chunk, "chunk {chunk}: held {high_water}");
    }
}

#[test]
fn decoder_reports_the_exact_shortfall() {
    let (car, _) = golden_car();
    let mut dec = CarDecoder::new(MAX);
    assert!(matches!(dec.decode(&[]).unwrap(), Decoded::NeedMore(1)));
    let header = CarWriter::header_len(&golden_cids()[..2]);
    for have in 1..header {
        assert!(
            matches!(CarDecoder::new(MAX).decode(&car[..have]).unwrap(), Decoded::NeedMore(n) if n == header - have)
        );
    }
    assert!(matches!(
        CarDecoder::new(4).decode(&car),
        Err(CarError::TooLarge { .. })
    ));
}

#[test]
fn writer_reports_a_short_buffer_and_stays_intact() {
    let cid = Cid::for_block(RAW, BLAKE3, b"blk").unwrap();
    let mut small = vec![0u8; CarWriter::header_len(&[cid]) - 1];
    assert!(matches!(
        CarWriter::new(&mut small, &[cid]),
        Err(CarError::Wire(WireError::BufferTooSmall { needed: 1 }))
    ));
    let mut buf = vec![0u8; CarWriter::header_len(&[cid]) + CarWriter::section_len(cid.as_ref(), b"blk") - 1];
    let mut w = CarWriter::new(&mut buf, &[cid]).unwrap();
    let before = w.written().to_vec();
    assert!(matches!(
        w.section(cid.as_ref(), b"blk"),
        Err(CarError::Wire(WireError::BufferTooSmall { needed: 1 }))
    ));
    assert_eq!(w.written(), before);
}

#[test]
fn many_roots_and_empty_roots_round_trip() {
    for n in [0usize, 1, 23, 24, 300] {
        let roots: Vec<Cid> = (0..n)
            .map(|i| Cid::for_block(RAW, SHA2_256, &(i as u32).to_le_bytes()).unwrap())
            .collect();
        let car = build(&roots, &[]);
        let r = CarReader::new(&car, MAX).unwrap();
        assert_eq!(r.roots().map(|c| c.into_owned()).collect::<Vec<_>>(), roots);
        assert_eq!(r.sections().count(), 0);
    }
}

proptest! {
    #[test]
    fn built_cars_round_trip(blocks in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..100), 0..8)) {
        let sections: Vec<_> = blocks.iter().map(|b| (Cid::for_block(RAW, BLAKE3, b).unwrap(), b.clone())).collect();
        let roots: Vec<Cid> = sections.iter().take(2).map(|s| s.0).collect();
        let car = build(&roots, &sections);
        let r = CarReader::new(&car, MAX).unwrap().with_verify(true);
        prop_assert_eq!(r.roots().map(|c| c.into_owned()).collect::<Vec<_>>(), roots);
        let got: Vec<_> = r.sections().map(|s| s.unwrap()).map(|(c, b)| (c.into_owned(), b.to_vec())).collect();
        prop_assert_eq!(got, sections);
    }

    #[test]
    fn arbitrary_bytes_never_panic(bytes in prop::collection::vec(any::<u8>(), 0..300), max in 0usize..400) {
        if let Ok(r) = CarReader::new(&bytes, max) {
            let _ = r.roots().count();
            let _ = r.with_verify(true).sections().count();
        }
        let mut dec = CarDecoder::new(max);
        let mut rest = &bytes[..];
        while let Ok(step) = dec.decode(rest) {
            match step {
                Decoded::NeedMore(_) => break,
                Decoded::Header { consumed, .. } | Decoded::Section { consumed, .. } => rest = &rest[consumed..],
            }
        }
    }

    #[test]
    fn mutated_cars_never_panic(at in any::<usize>(), byte in any::<u8>()) {
        let (mut car, _) = golden_car();
        let i = at % car.len();
        car[i] = byte;
        if let Ok(r) = CarReader::new(&car, MAX) {
            let _ = r.with_verify(true).sections().count();
        }
    }
}

#[test]
fn reading_and_writing_do_not_allocate() {
    let (car, cids) = golden_car();
    let mut out = vec![0u8; car.len()];
    let info = allocation_counter::measure(|| {
        let r = CarReader::new(&car, MAX).unwrap().with_verify(true);
        let n = r.roots().count() + r.sections().flatten().count();
        let mut dec = CarDecoder::new(MAX);
        let step = dec.decode(&car).unwrap();
        let mut w = CarWriter::new(&mut out, &cids[..2]).unwrap();
        for (cid, block) in r.sections().map(Result::unwrap) {
            w.section(cid, block).unwrap();
        }
        std::hint::black_box((n, matches!(step, Decoded::Header { .. }), w.written().len()));
    });
    assert_eq!(info.count_total, 0);
    assert_eq!(out, car);
}
