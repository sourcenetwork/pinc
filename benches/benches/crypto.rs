//! Benchmarks of `vinc-crypto`: key agreement, signatures, the AEADs, header protection, the KDF and the DRBG.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify};
use vinc_crypto::{Aead, Drbg, IdentityAlg, Keypair, Provider, Software, expand, labels};

fn bench_capabilities(c: &mut Criterion) {
    let caps = Software.capabilities();
    eprintln!("capabilities: {caps:?}");
    c.bench_function("capabilities", |b| b.iter(|| black_box(Software.capabilities())));
}

fn bench_x25519(c: &mut Criterion) {
    let p = Software;
    let secret = p.x25519_secret(&[7; 32]);
    let peer = p.x25519_public(&p.x25519_secret(&[9; 32]));
    c.bench_function("x25519/dh", |b| {
        b.iter(|| p.x25519_dh(black_box(&secret), black_box(&peer)).unwrap());
    });
}

fn bench_kem(c: &mut Criterion) {
    let p = Software;
    let mut g = c.benchmark_group("ml_kem_768");
    g.bench_function("keygen", |b| {
        b.iter(|| p.kem_keygen(black_box(&[1; 32]), black_box(&[2; 32])));
    });
    let (dk, ek) = p.kem_keygen(&[1; 32], &[2; 32]);
    g.bench_function("encapsulate", |b| {
        b.iter(|| p.kem_encapsulate(black_box(&ek), black_box(&[3; 32])).unwrap());
    });
    let (ct, _) = p.kem_encapsulate(&ek, &[3; 32]).unwrap();
    g.bench_function("decapsulate", |b| {
        b.iter(|| p.kem_decapsulate(black_box(&dk), black_box(&ct)).unwrap());
    });
    g.finish();
}

fn bench_signatures(c: &mut Criterion) {
    for (name, alg) in [
        ("ed25519", IdentityAlg::Ed25519),
        ("p256", IdentityAlg::EcdsaP256),
        ("ml_dsa_65", IdentityAlg::MlDsa65),
        ("hybrid", IdentityAlg::Hybrid),
    ] {
        let seed: Vec<u8> = (0..alg.seed_len()).map(|i| (i as u8).wrapping_add(1)).collect();
        let kp = Keypair::from_seed(alg, &seed).unwrap();
        let mut pk = vec![0u8; MAX_PUBLIC_KEY_LEN];
        let pk_len = kp.public_key(&mut pk).unwrap();
        let mut sig = vec![0u8; MAX_SIGNATURE_LEN];
        let sig_len = kp.sign(b"benchmark message", &mut sig).unwrap();
        let mut g = c.benchmark_group(name);
        g.bench_function("sign", |b| {
            b.iter(|| kp.sign(black_box(b"benchmark message"), black_box(&mut sig)).unwrap());
        });
        g.bench_function("verify", |b| {
            b.iter(|| {
                verify(
                    alg,
                    black_box(&pk[..pk_len]),
                    black_box(b"benchmark message"),
                    black_box(&sig[..sig_len]),
                )
                .unwrap();
            });
        });
        g.finish();
    }
}

fn bench_aead(c: &mut Criterion) {
    let p = Software;
    for (name, alg) in [
        ("chacha20poly1305", Aead::ChaCha20Poly1305),
        ("aes128gcm", Aead::Aes128Gcm),
    ] {
        let key = p.aead_key(alg, &vec![5u8; alg.key_len()]).unwrap();
        let mut g = c.benchmark_group(name);
        for size in [1200usize, 1452, 8952] {
            g.throughput(Throughput::Bytes(size as u64));
            let mut buf = vec![7u8; size];
            g.bench_function(format!("seal_{size}"), |b| {
                b.iter(|| p.seal(&key, &[1; 12], b"header", black_box(&mut buf)).unwrap());
            });
            let mut ct = vec![7u8; size];
            let tag = p.seal(&key, &[1; 12], b"header", &mut ct).unwrap();
            // `open` decrypts in place, so each run starts from a fresh copy of the ciphertext.
            g.bench_function(format!("open_{size}"), |b| {
                b.iter_batched_ref(
                    || ct.clone(),
                    |buf| p.open(&key, &[1; 12], b"header", buf, &tag).unwrap(),
                    BatchSize::SmallInput,
                );
            });
        }
        g.finish();
    }
}

fn bench_header_protection(c: &mut Criterion) {
    let p = Software;
    let mut g = c.benchmark_group("header_protection");
    for (name, alg) in [("chacha20", Aead::ChaCha20Poly1305), ("aes128", Aead::Aes128Gcm)] {
        let hp = p.hp_key(alg, &vec![3u8; alg.key_len()]).unwrap();
        g.bench_function(name, |b| b.iter(|| p.hp_mask(black_box(&hp), black_box(&[4; 16]))));
    }
    g.finish();
}

fn bench_kdf_and_drbg(c: &mut Criterion) {
    let prk = [1u8; 32];
    c.bench_function("kdf/expand_64", |b| {
        b.iter(|| {
            let mut out = [0u8; 64];
            expand(black_box(&prk), labels::NODE_ID, black_box(b"context"), &mut out);
            out
        });
    });
    let mut drbg = Drbg::new(&[2; 32]);
    let mut out = [0u8; 1024];
    let mut g = c.benchmark_group("drbg");
    g.throughput(Throughput::Bytes(1024));
    g.bench_function("fill_1k", |b| b.iter(|| drbg.fill(black_box(&mut out)).unwrap()));
    g.finish();
}

criterion_group!(
    benches,
    bench_capabilities,
    bench_x25519,
    bench_kem,
    bench_signatures,
    bench_aead,
    bench_header_protection,
    bench_kdf_and_drbg
);
criterion_main!(benches);
