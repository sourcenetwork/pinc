//! Benchmarks of `vinc-dag`: outboard building, range encoding, streaming verification and verified-range sets.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;
use std::ops::Range;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use vinc_dag::ranges::{VerifiedRanges, VerifiedRangesVec};
use vinc_dag::tree::{Layout, RangeVerifier, build_outboard, encode_range, encoded_len};

const MIB: usize = 1 << 20;
const LOG: u32 = 4;
const GROUP: usize = 16384;

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

fn outboard_of(value: &[u8]) -> (vinc_dag::tree::Cv, Vec<u8>) {
    let size = Layout::new(value.len() as u64, LOG).unwrap().outboard_size() as usize;
    let mut ob = vec![0u8; size];
    let root = build_outboard(value, LOG, &mut ob).unwrap();
    (root, ob)
}

fn bench_outboard(c: &mut Criterion) {
    let mut g = c.benchmark_group("outboard");
    for mib in [1usize, 64] {
        let v = data(1, mib * MIB);
        let (_, mut ob) = outboard_of(&v);
        g.throughput(Throughput::Bytes(v.len() as u64));
        g.bench_function(format!("blake3_hash_{mib}MiB"), |b| {
            b.iter(|| blake3::hash(black_box(&v)));
        });
        g.bench_function(format!("build_outboard_{mib}MiB"), |b| {
            b.iter(|| build_outboard(black_box(&v), LOG, black_box(&mut ob)).unwrap());
        });
    }
    g.finish();
}

fn bench_encode_range(c: &mut Criterion) {
    let v = data(2, 64 * MIB);
    let (_, ob) = outboard_of(&v);
    let range: Range<u64> = (32 * MIB) as u64..(33 * MIB) as u64;
    let mut out = vec![0u8; encoded_len(Layout::new(v.len() as u64, LOG).unwrap(), &range).unwrap() as usize];
    let mut g = c.benchmark_group("encode_range");
    g.throughput(Throughput::Bytes(MIB as u64));
    g.bench_function("1MiB_of_64MiB", |b| {
        b.iter(|| encode_range(black_box(&v), black_box(&ob), LOG, &range, black_box(&mut out)).unwrap());
    });
    g.finish();
}

fn bench_verifier(c: &mut Criterion) {
    let len = 16 * MIB;
    let v = data(3, len);
    let (root, ob) = outboard_of(&v);
    let range = 0..len as u64;
    let mut stream = vec![0u8; encoded_len(Layout::new(len as u64, LOG).unwrap(), &range).unwrap() as usize];
    encode_range(&v, &ob, LOG, &range, &mut stream).unwrap();

    let mut g = c.benchmark_group("verifier");
    g.throughput(Throughput::Bytes(len as u64));
    g.bench_function("blake3_hash_16MiB", |b| b.iter(|| blake3::hash(black_box(&v))));
    for (name, piece) in [("1452B", 1452usize), ("64KiB", 65536)] {
        g.bench_function(format!("verify_16MiB_{name}"), |b| {
            b.iter(|| {
                let mut ver = RangeVerifier::<GROUP>::new(root, len as u64, &range).unwrap();
                let mut sum = 0usize;
                for part in stream.chunks(piece) {
                    let mut rest = part;
                    while !rest.is_empty() {
                        let fed = ver.feed(rest).unwrap();
                        let consumed = fed.consumed;
                        if let Some(g) = fed.verified {
                            sum += black_box(g.data).len();
                        }
                        rest = &rest[consumed..];
                    }
                }
                assert!(ver.is_complete());
                sum
            });
        });
    }
    g.finish();
}

fn random_ranges(seed: u64, n: usize) -> Vec<Range<u64>> {
    let mut rng = SplitMix64(seed);
    (0..n)
        .map(|_| {
            let start = rng.next() % (1 << 30);
            start..start + 1 + rng.next() % (1 << 16)
        })
        .collect()
}

fn bench_ranges(c: &mut Criterion) {
    let ranges = random_ranges(4, 10_000);
    let mut g = c.benchmark_group("ranges");
    g.throughput(Throughput::Elements(ranges.len() as u64));
    // Both fixed-set variants use disjoint, non-adjacent ranges so that nothing merges.
    let fits: Vec<Range<u64>> = (0..64u64).map(|i| i * 100..i * 100 + 10).collect();
    g.throughput(Throughput::Elements(fits.len() as u64));
    g.bench_function("verified_ranges_64_insert_in_capacity", |b| {
        b.iter_batched(
            VerifiedRanges::<64>::new,
            |mut set| {
                for r in &fits {
                    black_box(set.insert(r.clone())).unwrap();
                }
                set
            },
            BatchSize::SmallInput,
        );
    });
    // A full set rejects a disjoint insert without changing, so one set serves every iteration.
    let mut full = VerifiedRanges::<64>::new();
    for r in &fits {
        full.insert(r.clone()).unwrap();
    }
    let rejected: Vec<Range<u64>> = (0..1000u64)
        .map(|i| (1 << 40) + i * 100..(1 << 40) + i * 100 + 10)
        .collect();
    g.throughput(Throughput::Elements(rejected.len() as u64));
    g.bench_function("verified_ranges_64_insert_rejected_when_full", |b| {
        b.iter(|| {
            for r in &rejected {
                black_box(full.insert(r.clone())).unwrap_err();
            }
        });
    });
    g.throughput(Throughput::Elements(ranges.len() as u64));
    g.bench_function("verified_ranges_vec_insert_10k", |b| {
        b.iter_batched(
            VerifiedRangesVec::new,
            |mut set| {
                for r in &ranges {
                    set.insert(r.clone());
                }
                set
            },
            BatchSize::SmallInput,
        );
    });
    g.finish();
}

criterion_group!(
    benches,
    bench_outboard,
    bench_encode_range,
    bench_verifier,
    bench_ranges
);
criterion_main!(benches);
