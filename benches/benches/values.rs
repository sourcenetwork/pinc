//! Benchmarks of `pinc-values`: the incremental, caller-retains verifier against the copying verifier at packet-sized
//! pieces, and the store-reading response source.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};
use pinc_dag::tree::{Layout, RangeVerifier, build_outboard, encode_range, encoded_len};
use pinc_transport::stream::StreamSource;
use pinc_values::plan::Plan;
use pinc_values::source::ValueSource;
use pinc_values::span::Span;
use pinc_values::store::ValueRead;
use pinc_values::verify::GroupVerifier;

const MIB: usize = 1 << 20;
const LOG: u32 = 4;
const GROUP: usize = 16384;
const PACKET: usize = 1452;

struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

fn data(seed: u64, len: usize) -> Vec<u8> {
    let mut rng = SplitMix64(seed);
    let mut v = vec![0u8; len];
    for chunk in v.chunks_mut(8) {
        let b = rng.next().to_le_bytes();
        chunk.copy_from_slice(&b[..chunk.len()]);
    }
    v
}

fn bench_verifier(c: &mut Criterion) {
    let len = 16 * MIB;
    let v = data(3, len);
    let mut ob = vec![0u8; Layout::new(len as u64, LOG).unwrap().outboard_size() as usize];
    let root = build_outboard(&v, LOG, &mut ob).unwrap();
    let range = 0..len as u64;
    let mut stream = vec![0u8; encoded_len(Layout::new(len as u64, LOG).unwrap(), &range).unwrap() as usize];
    encode_range(&v, &ob, LOG, &range, &mut stream).unwrap();

    let mut g = c.benchmark_group("values_verifier");
    g.throughput(Throughput::Bytes(len as u64));
    g.bench_function("blake3_hash_16MiB", |b| b.iter(|| blake3::hash(black_box(&v))));
    for (name, piece) in [("1452B", PACKET), ("64KiB", 65536)] {
        g.bench_function(format!("copying_{name}"), |b| {
            b.iter(|| {
                let mut ver = RangeVerifier::<GROUP>::new(root, len as u64, &range).unwrap();
                let mut sum = 0usize;
                for part in stream.chunks(piece) {
                    let mut rest = part;
                    while !rest.is_empty() {
                        let fed = ver.feed(rest).unwrap();
                        if let Some(g) = fed.verified {
                            sum += black_box(g.data).len();
                        }
                        rest = &rest[fed.consumed..];
                    }
                }
                assert!(ver.is_complete());
                sum
            });
        });
        g.bench_function(format!("incremental_{name}"), |b| {
            b.iter(|| {
                let mut ver = GroupVerifier::new(root, len as u64, LOG, &range).unwrap();
                let mut sum = 0u64;
                for part in stream.chunks(piece) {
                    let mut rest = part;
                    while !rest.is_empty() {
                        let fed = ver.feed(rest).unwrap();
                        if let Some(g) = fed.group {
                            sum += black_box(g.len);
                        }
                        rest = &rest[fed.consumed..];
                    }
                }
                assert!(ver.is_complete());
                sum
            });
        });
    }
    g.finish();
}

struct Held {
    root: [u8; 32],
    value: Vec<u8>,
    outboard: Vec<u8>,
}

impl ValueRead for &Held {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        (*root == self.root).then_some(self.value.len() as u64)
    }
    fn read_at(&self, _: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let from = offset as usize;
        let n = dst.len().min(self.value.len().saturating_sub(from));
        dst[..n].copy_from_slice(&self.value[from..from + n]);
        n
    }
    fn read_outboard(&self, _: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let from = offset as usize;
        let n = dst.len().min(self.outboard.len().saturating_sub(from));
        dst[..n].copy_from_slice(&self.outboard[from..from + n]);
        n
    }
}

fn bench_source(c: &mut Criterion) {
    let len = 16 * MIB;
    let value = data(5, len);
    let mut outboard = vec![0u8; Layout::new(len as u64, LOG).unwrap().outboard_size() as usize];
    let root = build_outboard(&value, LOG, &mut outboard).unwrap();
    let held = Held { root, value, outboard };
    let plan = Plan::new(
        len as u64,
        &[Span {
            off: 0,
            len: len as u64,
        }],
    )
    .unwrap();
    let total = plan.total();

    let mut g = c.benchmark_group("values_source");
    g.throughput(Throughput::Bytes(total));
    g.bench_function("read_at_1452B_sequential_16MiB", |b| {
        let mut buf = [0u8; PACKET];
        b.iter(|| {
            let mut src = ValueSource::new(&held, root, plan.clone());
            let mut at = 0u64;
            while at < total {
                at += src.read_at(at, black_box(&mut buf)) as u64;
            }
            at
        });
    });
    g.bench_function("memcpy_16MiB_in_1452B", |b| {
        let mut buf = [0u8; PACKET];
        b.iter(|| {
            let mut at = 0usize;
            while at < len {
                let n = PACKET.min(len - at);
                buf[..n].copy_from_slice(&held.value[at..at + n]);
                black_box(&buf);
                at += n;
            }
        });
    });
    g.finish();
}

criterion_group!(benches, bench_verifier, bench_source);
criterion_main!(benches);
