//! Tests of the KDF, the transcript and the DRBG: official BLAKE3 vectors, injectivity, determinism and allocation.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names
)]

use proptest::prelude::*;
use vinc_crypto::drbg::MAX_FILL;
use vinc_crypto::{CryptoError, Drbg, Transcript, expand, extract, labels};

mod blake3_vectors;
mod hexutil;
use hexutil::{arr, hex};

vinc_tests::install_counting_allocator!();

fn input(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8).collect()
}

#[test]
fn extract_is_the_official_blake3_keyed_hash() {
    let key: [u8; 32] = blake3_vectors::KEY.as_bytes().try_into().unwrap();
    for (len, keyed, _) in blake3_vectors::CASES {
        assert_eq!(extract(&key, &input(*len)).to_vec(), hex(keyed), "input length {len}");
    }
}

#[test]
fn expand_is_the_official_blake3_derive_key() {
    // derive_key(context, material) with material = prk || ctx; the official context string is not a VINC label, so
    // it is passed through `expand` directly (its `&'static str` is any string).
    for (len, _, derived) in blake3_vectors::CASES.iter().filter(|c| c.0 >= 32) {
        let data = input(*len);
        let prk: [u8; 32] = data[..32].try_into().unwrap();
        let mut out = [0u8; 32];
        expand(&prk, blake3_vectors::CONTEXT, &data[32..], &mut out);
        assert_eq!(out.to_vec(), hex(derived), "input length {len}");
    }
}

#[test]
fn expand_is_an_xof_and_separates_labels() {
    let prk = [7u8; 32];
    let mut long = [0u8; 200];
    expand(&prk, labels::NODE_ID, b"ctx", &mut long);
    let mut short = [0u8; 64];
    expand(&prk, labels::NODE_ID, b"ctx", &mut short);
    assert_eq!(&long[..64], &short[..], "a longer output extends the shorter one");
    let mut other = [0u8; 64];
    expand(&prk, labels::HYBRID_SIGNATURE, b"ctx", &mut other);
    assert_ne!(short, other);
    expand(&prk, labels::NODE_ID, b"ctX", &mut other);
    assert_ne!(short, other);
    let mut prk2 = prk;
    prk2[31] ^= 1;
    expand(&prk2, labels::NODE_ID, b"ctx", &mut other);
    assert_ne!(short, other);
    expand(&prk, labels::NODE_ID, b"ctx", &mut []);
}

#[test]
fn every_label_has_the_prefix_and_is_unique() {
    for (i, a) in labels::ALL.iter().enumerate() {
        assert!(a.starts_with("VINC 2026 v1 "), "{a}");
        assert!(a.len() > labels::PREFIX.len(), "{a}");
        assert!(!a.contains('\u{2013}') && !a.contains('\u{2014}'));
        for b in &labels::ALL[i + 1..] {
            assert_ne!(a, b);
        }
    }
}

#[test]
fn kdf_does_not_allocate() {
    let mut out = [0u8; 64];
    let mut prk = [0u8; 32];
    let stats = vinc_tests::measure(|| {
        prk = extract(&[1; 32], b"input keying material");
        expand(&prk, labels::NODE_ID, b"context", &mut out);
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
    assert_ne!(out, [0; 64]);
}

fn absorb_all(fields: &[&[u8]]) -> [u8; 32] {
    let mut t = Transcript::new();
    for f in fields {
        t.absorb("f", f);
    }
    t.snapshot()
}

#[test]
fn transcript_is_length_prefixed() {
    // The encoding is varint(len) || bytes per field.
    let mut want = blake3::Hasher::new();
    want.update(&[3]).update(b"abc").update(&[0]).update(&[2]).update(b"de");
    assert_eq!(absorb_all(&[b"abc", b"", b"de"]), *want.finalize().as_bytes());
    // A 300-byte field has a two-byte varint length.
    let long = vec![9u8; 300];
    let mut want = blake3::Hasher::new();
    want.update(&[0xac, 0x02]).update(&long);
    assert_eq!(absorb_all(&[&long]), *want.finalize().as_bytes());
    assert_ne!(absorb_all(&[b"ab", b"c"]), absorb_all(&[b"a", b"bc"]));
    assert_ne!(absorb_all(&[b"abc"]), absorb_all(&[b"abc", b""]));
    assert_ne!(
        Transcript::new().snapshot(),
        Transcript::with_label(labels::NODE_ID).snapshot()
    );
}

#[test]
fn snapshot_does_not_consume_the_transcript() {
    let mut t = Transcript::new();
    t.absorb("f", b"one");
    let first = t.snapshot();
    assert_eq!(first, t.snapshot());
    t.absorb("f", b"two");
    assert_ne!(first, t.snapshot());
    assert_eq!(t.snapshot(), absorb_all(&[b"one", b"two"]));
}

proptest! {
    #[test]
    fn different_field_splits_hash_differently(
        data in prop::collection::vec(any::<u8>(), 0..200),
        cuts_a in prop::collection::vec(any::<prop::sample::Index>(), 0..5),
        cuts_b in prop::collection::vec(any::<prop::sample::Index>(), 0..5),
    ) {
        let split = |cuts: &[prop::sample::Index]| -> Vec<Vec<u8>> {
            let mut at: Vec<usize> = cuts.iter().map(|c| c.index(data.len() + 1)).collect();
            at.sort_unstable();
            let mut fields = Vec::new();
            let mut prev = 0;
            for a in at.into_iter().chain([data.len()]) {
                fields.push(data[prev..a].to_vec());
                prev = a;
            }
            fields
        };
        let (a, b) = (split(&cuts_a), split(&cuts_b));
        let hash = |fields: &[Vec<u8>]| {
            let refs: Vec<&[u8]> = fields.iter().map(Vec::as_slice).collect();
            absorb_all(&refs)
        };
        prop_assert_eq!(hash(&a) == hash(&b), a == b);
    }

    #[test]
    fn different_field_values_hash_differently(
        a in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..20), 0..4),
        b in prop::collection::vec(prop::collection::vec(any::<u8>(), 0..20), 0..4),
    ) {
        let hash = |fields: &[Vec<u8>]| {
            let refs: Vec<&[u8]> = fields.iter().map(Vec::as_slice).collect();
            absorb_all(&refs)
        };
        prop_assert_eq!(hash(&a) == hash(&b), a == b);
    }
}

#[test]
fn transcript_does_not_allocate() {
    let stats = vinc_tests::measure(|| {
        let mut t = Transcript::with_label(labels::NODE_ID);
        t.absorb("f", b"hello");
        t.absorb("f", &[0u8; 5000]);
        let _ = t.snapshot();
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}

#[test]
fn drbg_is_deterministic_per_seed() {
    let mut a = Drbg::new(&[1; 32]);
    let mut b = Drbg::new(&[1; 32]);
    let mut c = Drbg::new(&[2; 32]);
    let (mut x, mut y, mut z) = ([0u8; 100], [0u8; 100], [0u8; 100]);
    a.fill(&mut x).unwrap();
    b.fill(&mut y).unwrap();
    c.fill(&mut z).unwrap();
    assert_eq!(x, y);
    assert_ne!(x, z);
    assert_ne!(x, [0; 100]);
    a.fill(&mut x).unwrap();
    b.fill(&mut y).unwrap();
    assert_eq!(x, y);
}

#[test]
fn drbg_rekeys_after_every_call() {
    // With fast key erasure, two 32-byte calls are not one 64-byte call.
    let mut one = Drbg::new(&[5; 32]);
    let mut two = Drbg::new(&[5; 32]);
    let mut whole = [0u8; 64];
    one.fill(&mut whole).unwrap();
    let (mut first, mut second) = ([0u8; 32], [0u8; 32]);
    two.fill(&mut first).unwrap();
    two.fill(&mut second).unwrap();
    assert_eq!(&whole[..32], &first[..]);
    assert_ne!(&whole[32..], &second[..]);
    // Consecutive outputs differ, including for an empty call that still re-keys.
    let mut d = Drbg::new(&[6; 32]);
    let mut p = [0u8; 32];
    let mut q = [0u8; 32];
    d.fill(&mut p).unwrap();
    d.fill(&mut []).unwrap();
    d.fill(&mut q).unwrap();
    assert_ne!(p, q);
}

#[test]
fn drbg_known_answer() {
    // Seed 00..1f. Each call reads the ChaCha20 block-0 keystream (key = the state, nonce = 0): bytes 0..32 become the
    // next key, bytes 32.. are the output. Expected values come from an independent ChaCha20 (checked against
    // RFC 8439 section 2.3.2).
    let mut d = Drbg::new(&arr("000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f"));
    let mut out = [0u8; 32];
    d.fill(&mut out).unwrap();
    assert_eq!(
        out,
        arr::<32>("2b23cce7a26023ab3f0eef693ac87f64258235eab1f7a32dc22762a0485b410c")
    );
    d.fill(&mut out).unwrap();
    assert_eq!(
        out,
        arr::<32>("2d41a59c90e41a8e7a4dccaa1c46069983b1a333ce25719ec3437768ab57fa42")
    );
}

#[test]
fn drbg_reseed_mixes_entropy() {
    let mut a = Drbg::new(&[1; 32]);
    let mut b = Drbg::new(&[1; 32]);
    a.reseed(&[9; 32]);
    let (mut x, mut y) = ([0u8; 32], [0u8; 32]);
    a.fill(&mut x).unwrap();
    b.fill(&mut y).unwrap();
    assert_ne!(x, y);
    let mut c = Drbg::new(&[1; 32]);
    c.reseed(&[9; 32]);
    let mut z = [0u8; 32];
    c.fill(&mut z).unwrap();
    assert_eq!(x, z);
    // Reseeding with the same entropy twice cancels: the state is the old one again.
    let mut d = Drbg::new(&[1; 32]);
    d.reseed(&[9; 32]);
    d.reseed(&[9; 32]);
    let mut w = [0u8; 32];
    d.fill(&mut w).unwrap();
    assert_eq!(w, y);
}

#[test]
fn drbg_bounds_one_call() {
    assert_eq!(MAX_FILL, 1 << 30);
    let mut d = Drbg::new(&[1; 32]);
    let mut huge = vec![0u8; MAX_FILL + 1];
    assert_eq!(d.fill(&mut huge), Err(CryptoError::InputTooLong));
    let mut ok = [0u8; 16];
    d.fill(&mut ok).unwrap();
    let mut fresh = Drbg::new(&[1; 32]);
    let mut same = [0u8; 16];
    fresh.fill(&mut same).unwrap();
    assert_eq!(ok, same, "a refused call leaves the state unchanged");
}

#[test]
fn drbg_does_not_allocate() {
    let mut d = Drbg::new(&[1; 32]);
    let mut out = [0u8; 1024];
    let stats = vinc_tests::measure(|| {
        d.fill(&mut out).unwrap();
        d.reseed(&[2; 32]);
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
    assert_ne!(out, [0; 1024]);
}
