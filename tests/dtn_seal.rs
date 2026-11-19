//! Tests of one-shot hybrid encryption, bundles, partial reception and resumption.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::similar_names,
    clippy::trivially_copy_pass_by_ref,
    clippy::struct_field_names,
    clippy::cast_lossless,
    clippy::range_plus_one,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value
)]

mod dtn_common;

use dtn_common::{ALGS, Sealed, bytes, keypair, make, plan, recipient};
use proptest::prelude::*;
use pinc_crypto::{CryptoError, IdentityAlg, Software};
use pinc_dag::ranges::VerifiedRanges;
use pinc_dtn::bundle::Reception;
use pinc_dtn::error::DtnError;
use pinc_dtn::head::{BundleId, MAX_SIGNED_HEAD_LEN, SignedHead};
use pinc_dtn::hlc::Hlc;
use pinc_dtn::layout::SliceLayout;
use pinc_dtn::seal::decapsulate;

const NOW: u64 = 2_000;

/// Receive everything in one go and open it.
fn receive_and_open(s: &Sealed, to: &dtn_common::Recipient) -> Result<Vec<u8>, DtnError> {
    let head = s.signed.head();
    let layout = head.layout().unwrap();
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&s.signed, &mut buf, NOW)?;
    rx.feed(0..layout.total_symbols(), &s.proof(0..layout.total_symbols()))?;
    assert!(rx.is_complete());
    let cipher = decapsulate(&Software, &to.keys, &to.dk, &to.xs, head)?;
    let mut out = vec![0; layout.padded_len() as usize];
    let n = rx.open(&Software, &cipher, &mut out)?;
    out.truncate(n);
    Ok(out)
}

#[test]
fn round_trip_for_every_identity_algorithm() {
    for (i, alg) in ALGS.into_iter().enumerate() {
        let sender = keypair(alg, 100 + i as u64);
        let to = recipient(IdentityAlg::Ed25519, 200, 1);
        let payload = bytes(7, 5_000);
        let s = make(&sender, &to, plan(3, 2, 0), &payload, 300);
        assert_eq!(s.signed.head().source.alg, alg);
        s.signed.verify().unwrap();
        assert_eq!(receive_and_open(&s, &to).unwrap(), payload, "{alg:?}");
    }
}

#[test]
fn recipient_may_use_any_identity_algorithm() {
    for (i, alg) in ALGS.into_iter().enumerate() {
        let sender = keypair(IdentityAlg::Ed25519, 1);
        let to = recipient(alg, 400 + i as u64, 5);
        let payload = bytes(8, 1_500);
        let s = make(&sender, &to, plan(2, 1, 1), &payload, 301);
        assert_eq!(receive_and_open(&s, &to).unwrap(), payload, "{alg:?}");
    }
}

#[test]
fn signed_head_encoding_round_trips_for_every_algorithm() {
    for (i, alg) in ALGS.into_iter().enumerate() {
        let sender = keypair(alg, 10 + i as u64);
        let to = recipient(IdentityAlg::Ed25519, 20, 1);
        let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 100), 30);
        let mut buf = vec![0; MAX_SIGNED_HEAD_LEN + 1];
        let n = s.signed.encode(&mut buf).unwrap();
        assert_eq!(n, s.signed.encoded_len());
        let back = SignedHead::decode(&buf[..n]).unwrap();
        assert_eq!(back, s.signed);
        back.verify().unwrap();
        assert!(SignedHead::decode(&buf[..n - 1]).is_err());
        buf[n] = 0;
        assert!(SignedHead::decode(&buf[..=n]).is_err(), "trailing byte");
    }
}

#[test]
fn flipped_head_bits_are_all_rejected() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 700), 3);
    let mut enc = vec![0; MAX_SIGNED_HEAD_LEN];
    let n = s.signed.encode(&mut enc).unwrap();
    for at in (0..n).step_by(7).chain(n - 70..n) {
        let mut bad = enc[..n].to_vec();
        bad[at] ^= 0x01;
        let ok = SignedHead::decode(&bad).is_ok_and(|h| h.verify().is_ok());
        assert!(!ok, "bit flip at byte {at} was accepted");
    }
}

#[test]
fn wrong_recipient_and_wrong_epoch_cannot_decapsulate() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let other = recipient(IdentityAlg::Ed25519, 50, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 700), 3);
    let head = s.signed.head();
    assert_eq!(
        decapsulate(&Software, &other.keys, &other.dk, &other.xs, head).err(),
        Some(DtnError::WrongRecipient)
    );
    let mut rotated = recipient(IdentityAlg::Ed25519, 2, 2);
    rotated.keys.node = to.keys.node;
    assert_eq!(
        decapsulate(&Software, &rotated.keys, &rotated.dk, &rotated.xs, head).err(),
        Some(DtnError::WrongRecipient)
    );
    // Right node and epoch but the wrong secret keys: the key differs, the first slice fails to authenticate.
    let mut impostor = recipient(IdentityAlg::Ed25519, 50, 1);
    impostor.keys.node = to.keys.node;
    let layout = head.layout().unwrap();
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&s.signed, &mut buf, NOW).unwrap();
    rx.feed(0..layout.total_symbols(), &s.proof(0..layout.total_symbols()))
        .unwrap();
    let cipher = decapsulate(&Software, &impostor.keys, &impostor.dk, &impostor.xs, head).unwrap();
    let mut out = vec![0; layout.padded_len() as usize];
    assert_eq!(
        rx.open(&Software, &cipher, &mut out).err(),
        Some(DtnError::Crypto(CryptoError::Authentication))
    );
}

#[test]
fn tampered_slices_never_enter_the_buffer() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 3_000), 3);
    let layout = s.signed.head().layout().unwrap();
    let total = layout.total_symbols();
    let proof = s.proof(1..2);
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&s.signed, &mut buf, NOW).unwrap();
    for at in 0..proof.len() {
        let mut bad = proof.clone();
        bad[at] ^= 0x80;
        assert!(rx.feed(1..2, &bad).is_err(), "flip at {at} accepted");
        assert!(!rx.holds(1));
    }
    assert!(rx.have().is_empty());
    rx.feed(1..2, &proof).unwrap();
    assert!(rx.holds(1) && !rx.holds(0) && total > 2);
    // A proof for another run is not accepted for this one.
    assert!(rx.feed(0..1, &s.proof(2..3)).is_err());
    assert!(rx.feed(0..1, &proof[..proof.len() - 1]).is_err(), "truncated");
}

#[test]
fn corrupted_relay_data_fails_the_proof() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let mut s = make(&sender, &to, plan(2, 0, 0), &bytes(1, 1_500), 3);
    // The relay corrupts a ciphertext byte before computing proofs: the root no longer matches the signed head.
    s.sealed[10] ^= 1;
    let layout = s.signed.head().layout().unwrap();
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&s.signed, &mut buf, NOW).unwrap();
    // The proof is built from the corrupted data and the old outboard, so the group hash fails.
    assert!(rx.feed(0..1, &s.proof(0..1)).is_err());
}

#[test]
fn head_signed_by_another_key_is_rejected() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 500), 3);
    let forger = keypair(IdentityAlg::Ed25519, 99);
    assert_eq!(
        SignedHead::sign(*s.signed.head(), &forger).err(),
        Some(DtnError::Params)
    );
}

#[test]
fn expired_bundle_is_not_received() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 500), 3);
    let layout = s.signed.head().layout().unwrap();
    let mut buf = vec![0; layout.total_len() as usize];
    let at = s.signed.head().expires_at();
    assert!(Reception::<8>::new(&s.signed, &mut buf, at - 1).is_ok());
    assert_eq!(
        Reception::<8>::new(&s.signed, &mut buf, at).err(),
        Some(DtnError::Expired)
    );
    let mut small = vec![0; 3];
    assert_eq!(
        Reception::<8>::new(&s.signed, &mut small, 0).err(),
        Some(DtnError::Buffer)
    );
}

#[test]
fn partial_reception_resumes_and_decodes_from_any_k_symbols() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let payload = bytes(5, 10_000);
    // 1 KiB symbols, k = 4, m = 2: 10 data symbols, 3 blocks (4, 4, 2), 6 parity symbols.
    let s = make(&sender, &to, plan(4, 2, 0), &payload, 3);
    let layout = s.signed.head().layout().unwrap();
    assert_eq!(
        (layout.data_symbols(), layout.blocks(), layout.total_symbols()),
        (10, 3, 16)
    );

    // First session: block 0 data 0..2 and block 1 parity only; then the node restarts, keeping buffer and ranges.
    let mut buf = vec![0; layout.total_len() as usize];
    let kept: VerifiedRanges<8>;
    {
        let mut rx = Reception::<8>::new(&s.signed, &mut buf, NOW).unwrap();
        rx.feed(0..2, &s.proof(0..2)).unwrap();
        rx.feed(10..12, &s.proof(10..12)).unwrap();
        assert!(!rx.is_decodable());
        assert_eq!(rx.next_missing(0), Some(2..10));
        kept = rx.have().clone();
    }
    let mut rx = Reception::<8>::resume(&s.signed, &mut buf, kept, NOW).unwrap();
    assert!(rx.holds(0) && rx.holds(1) && !rx.holds(2));
    // Block 0: has 2 data, needs 2 more (any): take parity 4 and 5. Block 1 (symbols 6..12): has parity 10, 11 so far.
    rx.feed(4..6, &s.proof(4..6)).unwrap();
    // Block 1 needs two data symbols besides the two parity ones: 6 and 8. Block 2 (12..16): 2 data + 2 parity, take parity.
    rx.feed(6..7, &s.proof(6..7)).unwrap();
    rx.feed(8..9, &s.proof(8..9)).unwrap();
    rx.feed(14..16, &s.proof(14..16)).unwrap();
    rx.feed(12..13, &s.proof(12..13)).unwrap();
    assert!(!rx.is_complete());
    // Block 2 (k = 2) holds symbols 12, 14, 15: three of four. Block 0 holds 0, 1, 4, 5. Block 1 holds 6, 8, 10, 11.
    assert!(rx.is_decodable());
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    dtn_common::finish(&mut rx, &mut outboard).unwrap();
    assert!(rx.is_complete());
    assert_eq!(outboard, s.outboard);
    assert_eq!(rx.sealed(), &s.sealed[..]);

    let cipher = decapsulate(&Software, &to.keys, &to.dk, &to.xs, s.signed.head()).unwrap();
    let mut out = vec![0; layout.padded_len() as usize];
    let n = rx.open(&Software, &cipher, &mut out).unwrap();
    assert_eq!(&out[..n], &payload[..]);
}

#[test]
fn undecodable_partial_bundle_reports_incomplete() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(4, 2, 0), &bytes(5, 4_000), 3);
    let layout = s.signed.head().layout().unwrap();
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&s.signed, &mut buf, NOW).unwrap();
    rx.feed(0..3, &s.proof(0..3)).unwrap();
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    assert_eq!(
        dtn_common::finish(&mut rx, &mut outboard).err(),
        Some(DtnError::Incomplete)
    );
    assert!(!rx.is_complete());
}

#[test]
fn inconsistent_parity_is_detected_not_trusted() {
    // A sender that signs a root over parity that is not a code word: decoding from the data alone must not match.
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let good = make(&sender, &to, plan(2, 1, 0), &bytes(5, 1_800), 3);
    let layout = good.signed.head().layout().unwrap();
    let g = layout.slice_len() as usize;
    // Corrupt the parity symbol (symbol 2) and re-sign over the corrupted bundle.
    let mut sealed = good.sealed.clone();
    sealed[2 * g] ^= 0xff;
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    let root = pinc_dag::tree::build_outboard(&sealed, 0, &mut outboard).unwrap();
    let mut head = *good.signed.head();
    head.root = root;
    let signed = SignedHead::sign(head, &sender).unwrap();
    let bad = Sealed {
        signed,
        sealed,
        outboard,
        payload: Vec::new(),
    };
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&bad.signed, &mut buf, NOW).unwrap();
    rx.feed(0..2, &bad.proof(0..2)).unwrap();
    let mut ob = vec![0; layout.outboard_len().unwrap() as usize];
    assert_eq!(dtn_common::finish(&mut rx, &mut ob).err(), Some(DtnError::Inconsistent));
    assert!(!rx.is_complete());
}

#[test]
fn reception_full_is_reported_and_recoverable() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(8, 0, 0), &bytes(5, 8_000), 3);
    let layout = s.signed.head().layout().unwrap();
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<2>::new(&s.signed, &mut buf, NOW).unwrap();
    rx.feed(0..1, &s.proof(0..1)).unwrap();
    rx.feed(2..3, &s.proof(2..3)).unwrap();
    assert_eq!(rx.feed(4..5, &s.proof(4..5)).err(), Some(DtnError::ReceptionFull));
    assert!(!rx.holds(4));
    // Filling the gap merges the intervals and frees capacity.
    rx.feed(1..2, &s.proof(1..2)).unwrap();
    rx.feed(4..5, &s.proof(4..5)).unwrap();
    assert!(rx.holds(4));
}

#[test]
fn every_slice_size_works() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    for log in 0..=4u8 {
        let payload = bytes(u64::from(log), 40_000);
        let s = make(&sender, &to, plan(3, 1, log), &payload, 9);
        assert_eq!(receive_and_open(&s, &to).unwrap(), payload, "log {log}");
    }
}

#[test]
fn invalid_parameters_are_refused() {
    use pinc_dtn::layout::SliceLayout;
    assert!(SliceLayout::new(0, 1, 0, 10).is_err());
    assert!(SliceLayout::new(200, 56, 0, 10).is_err());
    assert!(SliceLayout::new(255, 0, 0, 10).is_ok());
    assert!(SliceLayout::new(1, 0, 5, 10).is_err());
    assert!(SliceLayout::new(1, 0, 0, 0).is_err());
    assert!(SliceLayout::new(1, 254, 4, u64::MAX).is_err());
}

#[test]
fn labels_are_unique_and_prefixed() {
    use std::collections::HashSet;
    let all: Vec<&str> = pinc_dtn::labels::ALL
        .into_iter()
        .chain(pinc_crypto::labels::ALL)
        .chain([pinc_crypto::labels::STATEMENT])
        .chain(pinc_security::labels::ALL)
        .collect();
    let set: HashSet<_> = all.iter().collect();
    assert_eq!(set.len(), all.len());
    assert!(all.iter().all(|l| l.starts_with(pinc_crypto::labels::RESERVED)));
    for l in pinc_dtn::labels::ALL {
        assert!(l.starts_with(pinc_dtn::labels::PREFIX));
        assert!(l.starts_with("PINC 2026 v1 "));
        assert!(l.starts_with(pinc_crypto::labels::RESERVED));
    }
}

#[test]
fn hlc_orders_and_advances() {
    let a = Hlc::new(10, 0);
    assert_eq!(a.tick(20), Hlc::new(20, 0));
    assert_eq!(a.tick(5), Hlc::new(10, 1));
    assert_eq!(a.observe(Hlc::new(10, 7), 3), Hlc::new(10, 8));
    assert_eq!(a.observe(Hlc::new(30, 2), 3), Hlc::new(30, 3));
    assert_eq!(a.observe(Hlc::new(5, 9), 50), Hlc::new(50, 0));
    assert_eq!(Hlc::new(u64::MAX, u32::MAX).tick(0), Hlc::new(u64::MAX, u32::MAX));
    assert_eq!(a.expires_at(u64::MAX), u64::MAX);
}

#[test]
fn bundle_ids_are_unique_per_ephemeral() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let a = make(&sender, &to, plan(2, 1, 0), &bytes(1, 100), 3);
    let b = make(&sender, &to, plan(2, 1, 0), &bytes(1, 100), 5);
    assert_ne!(a.signed.head().id, b.signed.head().id);
    assert_ne!(
        a.signed.head().root,
        b.signed.head().root,
        "a fresh key re-randomizes every slice"
    );
    let id: BundleId = a.signed.head().id;
    assert_eq!(id, a.signed.head().id);
}

/// The probe of a cipher: its sealing of 16 zero bytes at index 0; equal probes mean equal keys.
fn key_probe(c: &pinc_dtn::seal::Cipher<Software>) -> Vec<u8> {
    let mut buf = [0u8; 16];
    let tag = c.seal_slice(&Software, 0, &mut buf).unwrap();
    buf.iter().chain(tag.iter()).copied().collect()
}

#[test]
fn the_slice_key_is_bound_to_every_input_and_to_nothing_else() {
    use pinc_crypto::Secret;
    use pinc_dtn::seal::{SealSeeds, encapsulate};
    let sender = keypair(IdentityAlg::Ed25519, 1).node_id();
    let r = recipient(IdentityAlg::Ed25519, 2, 1);
    let key = |to: &dtn_common::Recipient, a: u8, b: u8, ctr: u32| {
        let seeds = SealSeeds {
            eph_x25519: Secret::new([a; 32]),
            kem_m: Secret::new([b; 32]),
        };
        let (_, _, c) = encapsulate(&Software, &to.keys, &sender, Hlc::new(1_000, ctr), &seeds).unwrap();
        key_probe(&c)
    };
    let base = key(&r, 1, 2, 0);
    assert_eq!(base, key(&r, 1, 2, 0), "the derivation is deterministic in its inputs");
    assert_ne!(base, key(&r, 3, 2, 0), "the ephemeral seed is bound");
    assert_ne!(base, key(&r, 1, 4, 0), "the KEM message is bound");
    assert_ne!(
        base,
        key(&r, 1, 2, 1),
        "the creation time, through the bundle id, is bound"
    );
    // The same keys at another epoch, and another key pair under the same node and epoch, derive other keys.
    let r2 = recipient(IdentityAlg::Ed25519, 2, 2);
    assert_eq!(r.keys.node, r2.keys.node);
    assert_ne!(base, key(&r2, 1, 2, 0), "the epoch is bound");
    let mut other = recipient(IdentityAlg::Ed25519, 50, 1);
    other.keys.node = r.keys.node;
    assert_ne!(base, key(&other, 1, 2, 0), "the recipient's static keys are bound");
    // A slice sealed at one index opens at no other, even for the largest index.
    let seeds = SealSeeds {
        eph_x25519: Secret::new([1; 32]),
        kem_m: Secret::new([2; 32]),
    };
    let (_, _, c) = encapsulate(&Software, &r.keys, &sender, Hlc::new(1_000, 0), &seeds).unwrap();
    let mut buf = [7u8; 16];
    let tag = c.seal_slice(&Software, 4, &mut buf).unwrap();
    for j in [0, 3, 5, u64::MAX] {
        let mut b = buf;
        assert!(c.open_slice(&Software, j, &mut b, &tag).is_err());
    }
    let mut b = buf;
    assert!(c.open_slice(&Software, 4, &mut b, &tag).is_ok());
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]

    #[test]
    fn any_payload_round_trips(len in 1usize..6_000, k in 1u8..6, m in 0u8..4, log in 0u8..3, seed in any::<u64>()) {
        let sender = keypair(IdentityAlg::Ed25519, 1);
        let to = recipient(IdentityAlg::Ed25519, 2, 1);
        let payload = bytes(seed, len);
        let s = make(&sender, &to, plan(k, m, log), &payload, seed);
        prop_assert_eq!(receive_and_open(&s, &to).unwrap(), payload);
    }
}

/// A sealed bundle (k = 2, m = 2) whose symbol `bad` was changed before the root was computed, so the signed root
/// commits to content that is not a code word.
fn bundle_with_bad_symbol(bad: usize) -> (Sealed, SliceLayout) {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let good = make(&sender, &to, plan(2, 2, 0), &bytes(5, 1_800), 3);
    let layout = good.signed.head().layout().unwrap();
    let g = layout.slice_len() as usize;
    let mut sealed = good.sealed.clone();
    sealed[bad * g] ^= 0xff;
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    let root = pinc_dag::tree::build_outboard(&sealed, 0, &mut outboard).unwrap();
    let mut head = *good.signed.head();
    head.root = root;
    let signed = SignedHead::sign(head, &sender).unwrap();
    (
        Sealed {
            signed,
            sealed,
            outboard,
            payload: Vec::new(),
        },
        layout,
    )
}

#[test]
fn finish_never_writes_over_a_held_symbol() {
    // Holding the first data symbol and both parity symbols, finish solves the missing data symbol from the first
    // parity row and recomputes the second parity row. Written back over the held symbol, that row would differ from
    // the verified one whenever the sender's parity is not a code word.
    // 1. The second parity symbol is the bad one and is held: the signed root commits to it, so finish succeeds and
    //    the buffer is the sealed bundle, bad symbol included.
    let (bad, layout) = bundle_with_bad_symbol(3);
    let g = layout.slice_len() as usize;
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&bad.signed, &mut buf, NOW).unwrap();
    rx.feed(0..1, &bad.proof(0..1)).unwrap();
    rx.feed(2..4, &bad.proof(2..4)).unwrap();
    let mut ob = vec![0; layout.outboard_len().unwrap() as usize];
    dtn_common::finish(&mut rx, &mut ob).unwrap();
    assert!(rx.is_complete());
    assert_eq!(rx.sealed(), &bad.sealed[..]);
    // 2. The first parity symbol is the bad one and is held: the solved data symbol is wrong, the root does not
    //    match, and every held symbol is still the verified one.
    let (bad, layout) = bundle_with_bad_symbol(2);
    let mut buf = vec![0; layout.total_len() as usize];
    let mut rx = Reception::<8>::new(&bad.signed, &mut buf, NOW).unwrap();
    rx.feed(0..1, &bad.proof(0..1)).unwrap();
    rx.feed(2..4, &bad.proof(2..4)).unwrap();
    assert_eq!(dtn_common::finish(&mut rx, &mut ob).err(), Some(DtnError::Inconsistent));
    assert!(rx.holds(0) && rx.holds(2) && rx.holds(3) && !rx.holds(1));
    for s in [0, 2, 3] {
        assert_eq!(
            &rx.sealed()[s * g..(s + 1) * g],
            &bad.sealed[s * g..(s + 1) * g],
            "symbol {s}"
        );
    }
    // The scratch and outboard sizes are checked before anything moves.
    let mut scratch = vec![0; rx.scratch_len().unwrap()];
    assert_eq!(rx.finish(&mut ob[1..], &mut scratch).err(), Some(DtnError::Buffer));
    assert_eq!(rx.finish(&mut ob, &mut scratch[1..]).err(), Some(DtnError::Buffer));
}

#[test]
fn decapsulate_recomputes_the_bundle_id() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let s = make(&sender, &to, plan(2, 1, 0), &bytes(5, 1_800), 3);
    let mut head = *s.signed.head();
    decapsulate(&Software, &to.keys, &to.dk, &to.xs, &head).unwrap();
    // A head whose id is not derived from its source, creation time and ephemeral key is refused.
    head.id = BundleId([0xaa; 32]);
    assert_eq!(
        decapsulate(&Software, &to.keys, &to.dk, &to.xs, &head).err(),
        Some(DtnError::BadId)
    );
    let mut head = *s.signed.head();
    head.created = Hlc::new(head.created.wall + 1, head.created.counter);
    assert_eq!(
        decapsulate(&Software, &to.keys, &to.dk, &to.xs, &head).err(),
        Some(DtnError::BadId)
    );
}
