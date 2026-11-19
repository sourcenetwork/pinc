//! Benchmarks of `pinc-wire`: varint and the DAG-CBOR decoder and encoder.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use pinc_wire::cbor::{Decoder, Encoder, Item, MapReader};
use pinc_wire::varint;

fn bench_varint(c: &mut Criterion) {
    let mut g = c.benchmark_group("varint");
    for (name, value) in [("1b", 1u64), ("4b", 1 << 24), ("9b", (1 << 63) - 1)] {
        let mut buf = [0u8; varint::MAX_LEN];
        let n = varint::encode(value, &mut buf).unwrap();
        g.throughput(Throughput::Bytes(n as u64));
        g.bench_function(format!("encode_{name}"), |b| {
            b.iter(|| {
                let mut out = [0u8; varint::MAX_LEN];
                varint::encode(black_box(value), &mut out).unwrap();
                black_box(out)
            });
        });
        let enc = &buf[..n];
        g.bench_function(format!("decode_{name}"), |b| {
            b.iter(|| varint::decode(black_box(enc)).unwrap());
        });
    }
    g.finish();
}

const KEYS: [&str; 5] = ["n", "id", "cids", "data", "count"];

/// A map of 5 text keys: integers, an array of 8 CIDs (36 bytes each) and a 1 KiB byte string.
fn encode_doc(out: &mut [u8], cids: &[[u8; 36]; 8], blob: &[u8]) -> usize {
    let mut enc = Encoder::new(out);
    let mut keys = enc.ordered_map(5).unwrap();
    keys.key(&mut enc, KEYS[0]).unwrap();
    enc.unsigned(7).unwrap();
    keys.key(&mut enc, KEYS[1]).unwrap();
    enc.negative(123_456).unwrap();
    keys.key(&mut enc, KEYS[2]).unwrap();
    enc.array(8).unwrap();
    for cid in cids {
        enc.tag_cid(cid).unwrap();
    }
    keys.key(&mut enc, KEYS[3]).unwrap();
    enc.bytes(blob).unwrap();
    keys.key(&mut enc, KEYS[4]).unwrap();
    enc.unsigned(1 << 40).unwrap();
    assert!(keys.is_complete());
    enc.written().len()
}

fn pull_decode(doc: &[u8]) -> u64 {
    let mut dec = Decoder::new(doc);
    let mut map = MapReader::new(&mut dec).unwrap();
    let mut acc = 0u64;
    while let Some(key) = map.next_key(&mut dec).unwrap() {
        acc += key.len() as u64;
        match dec.next_item().unwrap() {
            Item::Unsigned(n) | Item::Negative(n) => acc += n,
            Item::Bytes(b) => acc += b.len() as u64,
            Item::Array(n) => {
                for _ in 0..n {
                    dec.next_item().unwrap();
                    if let Item::Bytes(b) = dec.next_item().unwrap() {
                        acc += b.len() as u64;
                    }
                }
            }
            _ => {}
        }
    }
    acc
}

fn bench_cbor(c: &mut Criterion) {
    let cids: [[u8; 36]; 8] = std::array::from_fn(|i| std::array::from_fn(|j| (i * 31 + j) as u8));
    let blob: Vec<u8> = (0..1024u32).map(|i| (i * 7) as u8).collect();
    let mut buf = vec![0u8; 4096];
    let n = encode_doc(&mut buf, &cids, &blob);
    let doc = buf[..n].to_vec();

    let mut g = c.benchmark_group("cbor");
    g.throughput(Throughput::Bytes(n as u64));
    g.bench_function("skip_value", |b| {
        b.iter(|| {
            let mut dec = Decoder::new(black_box(&doc));
            dec.skip_value().unwrap();
            dec.position()
        });
    });
    g.bench_function("pull_decode", |b| b.iter(|| pull_decode(black_box(&doc))));
    g.bench_function("encode", |b| {
        b.iter(|| encode_doc(black_box(&mut buf), black_box(&cids), black_box(&blob)));
    });
    g.finish();
}

criterion_group!(benches, bench_varint, bench_cbor);
criterion_main!(benches);
