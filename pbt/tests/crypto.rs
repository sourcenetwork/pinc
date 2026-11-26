//! `pinc-crypto`: the software provider's header-protection mask and the DRBG against a ChaCha20 block function
//! written here from RFC 8439, the transcript against its stated encoding, the set-sum algebra, and the signature
//! rules (canonical forms only, both halves of a hybrid).
//!
//! Where the expected behaviour comes from:
//! - `Software::hp_mask`: "The mask is the first bytes of block `counter` of the stream (RFC 9001 5.4.4)", and for
//!   AES the first five bytes of AES-ECB of the sample (RFC 9001 5.4.3); RFC 9001 appendix A gives one vector each;
//! - `drbg`: "Every [`Drbg::fill`] derives the next key and the output from one `ChaCha20` stream, replaces the key",
//!   "The new key is the old key combined by XOR with the entropy", "the same seed always gives the same stream";
//! - `transcript`: "every field is written as its multiformats varint length followed by its bytes", over BLAKE3
//!   (plain, or `derive_key` under the label);
//! - `setsum`: "The empty set is the identity, the sum does not depend on order, an item added twice counts twice,
//!   and adding then subtracting an item returns the sum"; "the empty sum is 32 zero bytes";
//! - `identity`: "verification is always available and never panics; a signature is accepted only in its canonical
//!   form (Ed25519 by `verify_strict`, ECDSA only with a low `s`) ... a hybrid signature is valid only if both halves
//!   verify"; `verify` documents `HighS` "for a malleable ECDSA signature".
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation, missing_docs)]

use ephyra::prelude::*;
use pinc_crypto::identity::{MAX_SIGNATURE_LEN, verify, verify_node};
use pinc_crypto::{Aead, CryptoError, Drbg, IdentityAlg, Keypair, Provider, SetSum, Software, Transcript};
use pinc_pbt::bytes;

// ---------------------------------------------------------------------------------------------------------------
// A ChaCha20 block function, RFC 8439 section 2.3.

fn quarter(s: &mut [u32; 16], a: usize, b: usize, c: usize, d: usize) {
    s[a] = s[a].wrapping_add(s[b]);
    s[d] = (s[d] ^ s[a]).rotate_left(16);
    s[c] = s[c].wrapping_add(s[d]);
    s[b] = (s[b] ^ s[c]).rotate_left(12);
    s[a] = s[a].wrapping_add(s[b]);
    s[d] = (s[d] ^ s[a]).rotate_left(8);
    s[c] = s[c].wrapping_add(s[d]);
    s[b] = (s[b] ^ s[c]).rotate_left(7);
}

fn chacha_block(key: &[u8; 32], counter: u32, nonce: &[u8; 12]) -> [u8; 64] {
    let word = |b: &[u8]| u32::from_le_bytes([b[0], b[1], b[2], b[3]]);
    let mut s = [0u32; 16];
    s[..4].copy_from_slice(&[0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574]);
    for i in 0..8 {
        s[4 + i] = word(&key[4 * i..]);
    }
    s[12] = counter;
    for i in 0..3 {
        s[13 + i] = word(&nonce[4 * i..]);
    }
    let init = s;
    for _ in 0..10 {
        quarter(&mut s, 0, 4, 8, 12);
        quarter(&mut s, 1, 5, 9, 13);
        quarter(&mut s, 2, 6, 10, 14);
        quarter(&mut s, 3, 7, 11, 15);
        quarter(&mut s, 0, 5, 10, 15);
        quarter(&mut s, 1, 6, 11, 12);
        quarter(&mut s, 2, 7, 8, 13);
        quarter(&mut s, 3, 4, 9, 14);
    }
    let mut out = [0u8; 64];
    for i in 0..16 {
        out[4 * i..4 * i + 4].copy_from_slice(&s[i].wrapping_add(init[i]).to_le_bytes());
    }
    out
}

/// The keystream from block 0 with a zero nonce: what the DRBG reads.
fn chacha_stream(key: &[u8; 32], len: usize) -> Vec<u8> {
    let mut out = Vec::with_capacity(len);
    let mut counter = 0u32;
    while out.len() < len {
        out.extend_from_slice(&chacha_block(key, counter, &[0; 12]));
        counter += 1;
    }
    out.truncate(len);
    out
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len()).step_by(2).map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap()).collect()
}

#[test]
fn the_reference_block_function_matches_rfc_8439() {
    // RFC 8439 2.3.2.
    let key: [u8; 32] = core::array::from_fn(|i| i as u8);
    let nonce: [u8; 12] = hex("000000090000004a00000000").try_into().unwrap();
    let b = chacha_block(&key, 1, &nonce);
    assert_eq!(&b[..16], &hex("10f1e7e4d13b5915500fdd1fa32071c4")[..]);
}

#[test]
fn hp_masks_match_rfc_9001() {
    let p = Software;
    // RFC 9001 A.5: ChaCha20 header protection.
    let k = p
        .hp_key(Aead::ChaCha20Poly1305, &hex("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4"))
        .unwrap();
    let sample: [u8; 16] = hex("5e5cd55c41f69080575d7999c25a5bfb").try_into().unwrap();
    assert_eq!(p.hp_mask(&k, &sample).to_vec(), hex("aefefe7d03"));
    // RFC 9001 A.2: AES-128 header protection of the client Initial.
    let k = p.hp_key(Aead::Aes128Gcm, &hex("9f50449e04a0e810283a1e9933adedd2")).unwrap();
    let sample: [u8; 16] = hex("d1b1c98dd7689fb8ec11d242b123dc9b").try_into().unwrap();
    assert_eq!(p.hp_mask(&k, &sample).to_vec(), hex("437b9aec36"));
}

fn key32() -> impl Gen<Value = [u8; 32]> {
    gens::vec(gens::int(0u8..=255)).len(32..=32).map(|v| <[u8; 32]>::try_from(v).unwrap())
}

/// A sample whose first four bytes (the block counter) are often at the edges.
fn samples() -> impl Gen<Value = [u8; 16]> {
    (
        gens::frequency(vec![
            (1, gens::pick_from(vec![0u32, 1, u32::MAX, u32::MAX - 1, 1 << 31]).boxed()),
            (3, gens::int(0u32..=u32::MAX).boxed()),
        ]),
        gens::vec(gens::int(0u8..=255)).len(12..=12),
    )
        .map(|(c, n)| {
            let mut s = [0u8; 16];
            s[..4].copy_from_slice(&c.to_le_bytes());
            s[4..].copy_from_slice(&n);
            s
        })
}

#[ephyra::test(gen = (key32(), samples()), tests = 5000)]
fn chacha_hp_mask_is_the_counter_block_of_the_stream(x: ([u8; 32], [u8; 16])) {
    let (key, sample) = x;
    let p = Software;
    let k = p.hp_key(Aead::ChaCha20Poly1305, &key).unwrap();
    let counter = u32::from_le_bytes(sample[..4].try_into().unwrap());
    let reference = chacha_block(&key, counter, &sample[4..].try_into().unwrap());
    assert_eq!(p.hp_mask(&k, &sample)[..], reference[..5], "counter {counter}");
}

#[ephyra::test(gen = gens::vec(gens::int(0usize..=200)).len(1..=6), tests = 50)]
fn wrong_key_lengths_are_refused(lens: Vec<usize>) {
    let p = Software;
    for n in lens {
        let k = vec![7u8; n];
        for alg in [Aead::ChaCha20Poly1305, Aead::Aes128Gcm] {
            let ok = n == alg.key_len();
            assert_eq!(p.aead_key(alg, &k).is_ok(), ok, "aead key of {n} bytes for {alg:?}");
            let hp_ok = n == alg.key_len();
            assert_eq!(p.hp_key(alg, &k).is_ok(), hp_ok, "hp key of {n} bytes for {alg:?}");
        }
    }
}

#[ephyra::test(gen = (gens::bool(), key32(), bytes(40), bytes(300), gens::int(0usize..=400), gens::int(1u8..=255)), tests = 3000)]
fn aead_opens_what_it_sealed_and_nothing_changed(x: (bool, [u8; 32], Vec<u8>, Vec<u8>, usize, u8)) {
    let (aes, key, aad, msg, at, bit) = x;
    let p = Software;
    let alg = if aes { Aead::Aes128Gcm } else { Aead::ChaCha20Poly1305 };
    let k = p.aead_key(alg, &key[..alg.key_len()]).unwrap();
    let nonce = [9u8; 12];
    let mut ct = msg.clone();
    let tag = p.seal(&k, &nonce, &aad, &mut ct).unwrap();
    let mut pt = ct.clone();
    assert_eq!(p.open(&k, &nonce, &aad, &mut pt, &tag), Ok(()));
    assert_eq!(pt, msg);
    let total = aad.len() + ct.len() + 16 + 12;
    let i = at % total;
    let (mut aad2, mut ct2, mut tag2, mut nonce2) = (aad.clone(), ct.clone(), tag, nonce);
    if i < aad.len() {
        aad2[i] ^= bit;
    } else if i < aad.len() + ct.len() {
        ct2[i - aad.len()] ^= bit;
    } else if i < aad.len() + ct.len() + 16 {
        tag2[i - aad.len() - ct.len()] ^= bit;
    } else {
        nonce2[i - aad.len() - ct.len() - 16] ^= bit;
    }
    assert_eq!(p.open(&k, &nonce2, &aad2, &mut ct2, &tag2), Err(CryptoError::Authentication));
}

// ---------------------------------------------------------------------------------------------------------------
// DRBG.

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum DrbgOp {
    Fill(#[ephyra(gen = gens::frequency(vec![(3, gens::int(0usize..=200).boxed()), (1, gens::int(0usize..=5000).boxed())]))] usize),
    Reseed(#[ephyra(gen = key32())] [u8; 32]),
}

#[ephyra::test(gen = (key32(), gens::vec(ephyra::any::<DrbgOp>()).len(1..=20)), tests = 3000)]
fn drbg_is_chacha20_with_fast_key_erasure(x: ([u8; 32], Vec<DrbgOp>)) {
    let (seed, ops) = x;
    let mut d = Drbg::new(&seed);
    let mut key = seed;
    for op in &ops {
        match op {
            DrbgOp::Fill(n) => {
                let mut out = vec![0u8; *n];
                d.fill(&mut out).unwrap();
                let stream = chacha_stream(&key, 32 + n);
                assert_eq!(out, stream[32..], "a fill of {n} bytes is not the stream after the next key");
                key.copy_from_slice(&stream[..32]);
            }
            DrbgOp::Reseed(e) => {
                d.reseed(e);
                key.iter_mut().zip(e).for_each(|(k, e)| *k ^= e);
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Transcript.

fn leb128(mut n: u64, out: &mut Vec<u8>) {
    loop {
        let b = (n & 0x7f) as u8;
        n >>= 7;
        if n == 0 {
            out.push(b);
            return;
        }
        out.push(b | 0x80);
    }
}

fn fields() -> impl Gen<Value = Vec<Vec<u8>>> {
    gens::vec(gens::frequency(vec![(5, bytes(40).boxed()), (1, bytes(400).boxed())])).len(0..=8)
}

#[ephyra::test(gen = (gens::bool(), fields()), tests = 3000)]
fn transcript_is_blake3_of_the_length_prefixed_fields(x: (bool, Vec<Vec<u8>>)) {
    let (labelled, fs) = x;
    const LABEL: &str = "PINC 2026 v1 statement";
    let mut t = if labelled { Transcript::with_label(LABEL) } else { Transcript::new() };
    let mut enc = Vec::new();
    for (i, f) in fs.iter().enumerate() {
        t.absorb("field", f);
        leb128(f.len() as u64, &mut enc);
        enc.extend_from_slice(f);
        let expect = if labelled {
            let mut h = blake3::Hasher::new_derive_key(LABEL);
            h.update(&enc);
            *h.finalize().as_bytes()
        } else {
            *blake3::hash(&enc).as_bytes()
        };
        assert_eq!(t.snapshot(), expect, "after field {i}");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Set sums.

fn items() -> impl Gen<Value = Vec<Vec<u8>>> {
    gens::vec(bytes(12)).len(0..=10)
}

#[ephyra::test(gen = (items(), items(), gens::int(0usize..=100)), tests = 1000)]
fn setsum_is_a_commutative_group_over_multisets(x: (Vec<Vec<u8>>, Vec<Vec<u8>>, usize)) {
    let (a, b, rot) = x;
    let key = [3u8; 32];
    let sum = |v: &[Vec<u8>]| v.iter().fold(SetSum::zero(), |s, i| s + SetSum::of_item(&key, i));
    let sa = sum(&a);
    let mut rotated = a.clone();
    if !rotated.is_empty() {
        let r = rot % rotated.len();
        rotated.rotate_left(r);
        rotated.reverse();
    }
    assert_eq!(sum(&rotated), sa, "the sum depends on order");
    let ab: Vec<Vec<u8>> = a.iter().chain(b.iter()).cloned().collect();
    assert_eq!(sum(&ab) - sum(&b), sa, "adding then subtracting does not return the sum");
    assert_eq!(sa + (-sa), SetSum::zero());
    let mut acc = sa;
    acc -= sa;
    acc += sum(&b);
    assert_eq!(acc, sum(&b));
    assert_eq!(SetSum::decode(&sa.encode()), Some(sa), "the encoding does not decode to the sum");
    assert_eq!(SetSum::zero().encode(), [0u8; 32]);
    if let Some(first) = a.first() {
        let twice: Vec<Vec<u8>> = a.iter().chain(core::iter::once(first)).cloned().collect();
        assert_ne!(sum(&twice), sa, "an item added twice counts once");
    }
}

#[ephyra::test(gen = gens::vec(gens::int(0u8..=255)).len(32..=32), tests = 20_000)]
fn setsum_decode_accepts_only_canonical_encodings(b: Vec<u8>) {
    let b: [u8; 32] = b.try_into().unwrap();
    if let Some(s) = SetSum::decode(&b) {
        assert_eq!(s.encode(), b, "a non-canonical encoding decoded");
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Signatures.

const P256_N: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xbc, 0xe6, 0xfa,
    0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
];
/// The Ed25519 group order L, little-endian.
const ED_L: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0x10,
];

/// `a - b` for big-endian 256-bit numbers, `a >= b`.
fn sub_be(a: &[u8; 32], b: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut borrow = 0i16;
    for i in (0..32).rev() {
        let mut d = i16::from(a[i]) - i16::from(b[i]) - borrow;
        borrow = i16::from(d < 0);
        if d < 0 {
            d += 256;
        }
        out[i] = d as u8;
    }
    out
}

/// `a + b` for little-endian 256-bit numbers (no overflow for a scalar below L plus L).
fn add_le(a: &[u8], b: &[u8; 32]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut carry = 0u16;
    for i in 0..32 {
        let s = u16::from(a[i]) + u16::from(b[i]) + carry;
        out[i] = s as u8;
        carry = s >> 8;
    }
    out
}

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

fn sig_cases() -> impl Gen<Value = (u8, u8, Vec<u8>, usize, u8)> {
    (
        gens::frequency(vec![(4, gens::int(0u8..=1).boxed()), (1, gens::int(2u8..=3).boxed())]),
        // A seed of all 0x00 or all 0xff is no P-256 scalar (`InvalidSecretKey`, which `SoftwareStore::generate` retries).
        gens::int(1u8..=253),
        bytes(100),
        gens::int(0usize..=6000),
        gens::int(1u8..=255),
    )
}

#[ephyra::test(gen = sig_cases(), tests = 400)]
fn a_signature_verifies_only_as_made(x: (u8, u8, Vec<u8>, usize, u8)) {
    let (a, seed, msg, at, bit) = x;
    let alg = ALGS[usize::from(a)];
    let kp = Keypair::from_seed(alg, &vec![seed; alg.seed_len()]).unwrap();
    let other = Keypair::from_seed(alg, &vec![seed.wrapping_add(1); alg.seed_len()]).unwrap();
    let mut pk = vec![0u8; alg.public_key_len()];
    assert_eq!(kp.public_key(&mut pk), Ok(pk.len()));
    let mut opk = vec![0u8; alg.public_key_len()];
    other.public_key(&mut opk).unwrap();
    let mut sig = vec![0u8; MAX_SIGNATURE_LEN];
    let n = kp.sign(&msg, &mut sig).unwrap();
    sig.truncate(n);
    assert_eq!(n, alg.signature_len());
    assert_eq!(verify(alg, &pk, &msg, &sig), Ok(()), "a fresh signature does not verify");
    assert_eq!(verify_node(&kp.node_id(), &pk, &msg, &sig), Ok(()));
    assert_eq!(verify_node(&other.node_id(), &pk, &msg, &sig), Err(CryptoError::NodeIdMismatch));
    assert!(verify(alg, &opk, &msg, &sig).is_err(), "another key verifies the signature");
    // One bit changed in the message or the signature.
    let mut m2 = msg.clone();
    let mut s2 = sig.clone();
    let i = at % (msg.len() + sig.len());
    if i < msg.len() {
        m2[i] ^= bit;
    } else {
        s2[i - msg.len()] ^= bit;
    }
    assert!(verify(alg, &pk, &m2, &s2).is_err(), "a changed message or signature verifies (byte {i})");
    // The other canonical-form rules.
    match alg {
        IdentityAlg::EcdsaP256 => {
            let high = sub_be(&P256_N, &sig[32..]);
            let mut s3 = sig.clone();
            s3[32..].copy_from_slice(&high);
            assert_eq!(verify(alg, &pk, &msg, &s3), Err(CryptoError::HighS), "the high-s twin was not refused");
        }
        IdentityAlg::Ed25519 | IdentityAlg::Hybrid => {
            let s_plus_l = add_le(&sig[32..64], &ED_L);
            let mut s3 = sig.clone();
            s3[32..64].copy_from_slice(&s_plus_l);
            assert!(verify(alg, &pk, &msg, &s3).is_err(), "S + L verifies: the signature is malleable");
        }
        IdentityAlg::MlDsa65 => {}
    }
    if alg == IdentityAlg::Hybrid {
        // Each half alone, with the other half from a signature of another message.
        let mut sig_other = vec![0u8; MAX_SIGNATURE_LEN];
        let n2 = kp.sign(b"another message", &mut sig_other).unwrap();
        sig_other.truncate(n2);
        let mut mixed = sig.clone();
        mixed[..64].copy_from_slice(&sig_other[..64]);
        assert!(verify(alg, &pk, &msg, &mixed).is_err(), "a hybrid verified with a foreign Ed25519 half");
        let mut mixed = sig.clone();
        mixed[64..].copy_from_slice(&sig_other[64..]);
        assert!(verify(alg, &pk, &msg, &mixed).is_err(), "a hybrid verified with a foreign ML-DSA half");
    }
}

#[ephyra::test(gen = (gens::int(0u8..=3), bytes(64), bytes(80), gens::int(0u8..=4)), tests = 3000)]
fn verify_of_garbage_never_panics(x: (u8, Vec<u8>, Vec<u8>, u8)) {
    let (a, pk_head, sig_head, first) = x;
    let alg = ALGS[usize::from(a)];
    let mut pk = vec![0u8; alg.public_key_len()];
    let n = pk_head.len().min(pk.len());
    pk[..n].copy_from_slice(&pk_head[..n]);
    if alg == IdentityAlg::EcdsaP256 {
        pk[0] = first;
    }
    let mut sig = vec![0u8; alg.signature_len()];
    let n = sig_head.len().min(sig.len());
    sig[..n].copy_from_slice(&sig_head[..n]);
    assert!(verify(alg, &pk, b"m", &sig).is_err(), "garbage verified");
}

#[ephyra::test(gen = (gens::int(0u8..=3), gens::int(0usize..=70)), tests = 400)]
fn a_seed_of_the_wrong_length_is_refused_and_the_right_one_is_deterministic(x: (u8, usize)) {
    let (a, len) = x;
    let alg = ALGS[usize::from(a)];
    let seed = vec![0x42u8; len];
    let r = Keypair::from_seed(alg, &seed);
    assert_eq!(r.is_ok(), len == alg.seed_len(), "seed of {len} bytes for {alg:?}");
    if let Ok(kp) = r {
        let again = Keypair::from_seed(alg, &seed).unwrap();
        assert_eq!(kp.node_id(), again.node_id());
    }
}
