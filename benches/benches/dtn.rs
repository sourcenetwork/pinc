//! Benchmarks of `pinc-dtn`: the GF(2^8) kernel, Reed-Solomon encode and decode, and sealing and receiving bundles.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use pinc_crypto::{IdentityAlg, Keypair, Provider, Secret, Software};
use pinc_dtn::bundle::{Outgoing, Plan, Reception, seal_bundle, serve, serve_len};
use pinc_dtn::gf256::mul_add;
use pinc_dtn::head::Erasure;
use pinc_dtn::hlc::Hlc;
use pinc_dtn::layout::SliceLayout;
use pinc_dtn::rs::Rs;
use pinc_dtn::seal::{RecipientKeys, SealSeeds, decapsulate};

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

fn bench_kernel(c: &mut Criterion) {
    let mut g = c.benchmark_group("gf256");
    let src = data(1, 64 * 1024);
    let mut dst = data(2, 64 * 1024);
    g.throughput(Throughput::Bytes(src.len() as u64));
    g.bench_function("mul_add_64KiB", |b| {
        b.iter(|| mul_add(black_box(&mut dst), black_box(&src), black_box(0x8e)));
    });
    g.finish();
}

fn bench_rs(c: &mut Criterion) {
    let mut g = c.benchmark_group("rs");
    for (k, m, len) in [(16, 4, 1024), (16, 4, 16384), (128, 16, 1024), (223, 32, 1024)] {
        let rs = Rs::new(k, m).unwrap();
        let mut block = data(3, rs.n() * len);
        g.throughput(Throughput::Bytes((k * len) as u64));
        g.bench_function(format!("encode_k{k}_m{m}_{len}B"), |b| {
            b.iter(|| rs.encode(len, black_box(&mut block)).unwrap());
        });
        rs.encode(len, &mut block).unwrap();
        // The worst decode: as many data symbols missing as there are parity symbols.
        let mut present = vec![true; rs.n()];
        present[..m.min(k)].fill(false);
        g.bench_function(format!("decode_{}_erased_k{k}_m{m}_{len}B", m.min(k)), |b| {
            b.iter_batched_ref(
                || block.clone(),
                |blk| rs.reconstruct(len, black_box(blk), &present).unwrap(),
                BatchSize::LargeInput,
            );
        });
    }
    g.finish();
}

fn recipient(
    p: Software,
) -> (
    RecipientKeys,
    <Software as Provider>::KemDecapsKey,
    <Software as Provider>::X25519Secret,
    Keypair,
) {
    let id = Keypair::from_seed(IdentityAlg::Ed25519, &data(10, 32)).unwrap();
    let (dk, ek) = p.kem_keygen(&data(11, 32).try_into().unwrap(), &data(12, 32).try_into().unwrap());
    let xs = p.x25519_secret(&data(13, 32).try_into().unwrap());
    let keys = RecipientKeys {
        node: id.node_id(),
        epoch: 1,
        kem_ek: p.kem_encaps_key_bytes(&ek),
        x25519: p.x25519_public(&xs),
    };
    (keys, dk, xs, id)
}

fn bench_bundle(c: &mut Criterion) {
    let p = Software;
    let (keys, dk, xs, _) = recipient(p);
    let sender = Keypair::from_seed(IdentityAlg::Ed25519, &data(20, 32)).unwrap();
    let mut g = c.benchmark_group("bundle");
    g.sample_size(20);
    let payload = data(30, 4 << 20);
    let plan = Plan {
        created: Hlc::new(1, 0),
        lifetime_ms: 1 << 40,
        copies: 8,
        erasure: Erasure { k: 16, m: 4 },
        slice_log: 4,
    };
    let seeds = SealSeeds {
        eph_x25519: Secret::new(data(31, 32).try_into().unwrap()),
        kem_m: Secret::new(data(32, 32).try_into().unwrap()),
    };
    let layout = SliceLayout::new(16, 4, 4, payload.len() as u64).unwrap();
    let mut sealed = vec![0u8; layout.total_len() as usize];
    let mut outboard = vec![0u8; layout.outboard_len().unwrap() as usize];
    g.throughput(Throughput::Bytes(payload.len() as u64));
    let out = Outgoing {
        recipient: &keys,
        plan,
        seeds: &seeds,
    };
    g.bench_function("seal_4MiB_k16_m4", |b| {
        b.iter(|| seal_bundle(&p, &sender, &out, black_box(&payload), &mut sealed, &mut outboard).unwrap());
    });
    let signed = seal_bundle(&p, &sender, &out, &payload, &mut sealed, &mut outboard).unwrap();
    let total = layout.total_symbols();
    let mut proof = vec![0u8; serve_len(&layout, &(0..total)).unwrap()];
    serve(&layout, &sealed, &outboard, &(0..total), &mut proof).unwrap();
    let mut buf = vec![0u8; sealed.len()];
    g.bench_function("receive_verify_4MiB", |b| {
        b.iter(|| {
            let mut rx = Reception::<8>::new(&signed, &mut buf, 0).unwrap();
            rx.feed(0..total, black_box(&proof)).unwrap();
        });
    });
    let mut padded = vec![0u8; layout.padded_len() as usize];
    let mut rx = Reception::<8>::new(&signed, &mut buf, 0).unwrap();
    rx.feed(0..total, &proof).unwrap();
    let cipher = decapsulate(&p, &keys, &dk, &xs, signed.head()).unwrap();
    g.bench_function("open_4MiB", |b| {
        b.iter(|| rx.open(&p, &cipher, black_box(&mut padded)).unwrap());
    });
    g.finish();
}

criterion_group!(benches, bench_kernel, bench_rs, bench_bundle);
criterion_main!(benches);
