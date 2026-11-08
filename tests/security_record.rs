//! Record protection, key update and its limits, the replay window, address tokens, the amplification budget and labels.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::match_same_arms
)]

use std::collections::BTreeSet;

use proptest::prelude::*;
use vinc_crypto::{Aead, Provider, Secret, Software, expand};
use vinc_security::amp::{FACTOR, OVERHEAD};
use vinc_security::record::{AES_GCM_PACKET_LIMIT, CHACHA_FAILURE_LIMIT, MAX_PACKET_NUMBER};
use vinc_security::token::{MAX_ADDR_LEN, MAX_TOKEN_LEN, NEW_TOKEN_LIFETIME_NS, RETRY_LIFETIME_NS};
use vinc_security::{
    AmpBudget, HeaderKey, Limits, PacketKey, RecordError, ReplayError, ReplayWindow, TokenError, TokenKey, TokenKind,
    labels,
};

mod sec_common;

vinc_tests::install_counting_allocator!();

const AEADS: [Aead; 2] = [Aead::ChaCha20Poly1305, Aead::Aes128Gcm];

fn secret(tag: u8) -> Secret<32> {
    Secret::new([tag; 32])
}

#[test]
fn seal_and_open_round_trip_and_authenticate_everything() {
    let p = Software;
    for aead in AEADS {
        let mut tx = PacketKey::from_secret(&p, aead, &secret(1)).unwrap();
        let mut rx = PacketKey::from_secret(&p, aead, &secret(1)).unwrap();
        let plain = *b"a packet of some length, more than one block of the cipher";
        let mut buf = plain;
        let tag = tx.seal(&p, 41, b"header", &mut buf).unwrap();
        assert_ne!(buf, plain);
        let mut ok = buf;
        rx.open(&p, 41, b"header", &mut ok, &tag).unwrap();
        assert_eq!(ok, plain);
        // Wrong packet number, header, ciphertext, tag, key.
        let mut again = buf;
        assert_eq!(
            rx.open(&p, 42, b"header", &mut again, &tag),
            Err(RecordError::Authentication)
        );
        let mut again = buf;
        assert_eq!(
            rx.open(&p, 41, b"headeR", &mut again, &tag),
            Err(RecordError::Authentication)
        );
        let mut bad = buf;
        bad[3] ^= 1;
        assert_eq!(
            rx.open(&p, 41, b"header", &mut bad, &tag),
            Err(RecordError::Authentication)
        );
        let mut bad_tag = tag;
        bad_tag[15] ^= 1;
        let mut again = buf;
        assert_eq!(
            rx.open(&p, 41, b"header", &mut again, &bad_tag),
            Err(RecordError::Authentication)
        );
        let mut other = PacketKey::from_secret(&p, aead, &secret(2)).unwrap();
        let mut again = buf;
        assert_eq!(
            other.open(&p, 41, b"header", &mut again, &tag),
            Err(RecordError::Authentication)
        );
        assert_eq!(rx.failed_opens(), 4);
        assert_eq!(tx.sealed(), 1);
    }
}

#[test]
fn the_nonce_is_the_iv_xor_the_packet_number() {
    let p = Software;
    for aead in AEADS {
        let s = secret(9);
        let mut key = [0u8; 32];
        expand(s.expose(), labels::PACKET_KEY, &[], &mut key[..aead.key_len()]);
        let mut iv = [0u8; 12];
        expand(s.expose(), labels::PACKET_IV, &[], &mut iv);
        let raw = p.aead_key(aead, &key[..aead.key_len()]).unwrap();
        let mut pk = PacketKey::from_secret(&p, aead, &s).unwrap();
        for pn in [0u64, 1, 255, 256, 0xdead_beef, MAX_PACKET_NUMBER] {
            let mut nonce = iv;
            for (n, b) in nonce[4..].iter_mut().zip(pn.to_be_bytes()) {
                *n ^= b;
            }
            let mut expected = *b"payload";
            let expected_tag = p.seal(&raw, &nonce, b"aad", &mut expected).unwrap();
            let mut got = *b"payload";
            let tag = pk.seal(&p, pn, b"aad", &mut got).unwrap();
            assert_eq!((got, tag), (expected, expected_tag), "{aead:?} pn {pn}");
        }
        // The packet number must be below 2^62.
        let mut buf = [0u8; 4];
        assert_eq!(
            pk.seal(&p, MAX_PACKET_NUMBER + 1, b"", &mut buf),
            Err(RecordError::PacketNumber)
        );
        assert_eq!(pk.seal(&p, u64::MAX, b"", &mut buf), Err(RecordError::PacketNumber));
        assert_eq!(
            pk.open(&p, 1 << 62, b"", &mut buf, &[0; 16]),
            Err(RecordError::PacketNumber)
        );
    }
}

#[test]
fn header_protection_masks_the_low_bits_and_the_packet_number() {
    let p = Software;
    for aead in AEADS {
        let s = secret(5);
        let hk = HeaderKey::from_secret(&p, aead, &s).unwrap();
        let mut hp = [0u8; 32];
        expand(s.expose(), labels::HEADER_KEY, &[], &mut hp[..aead.key_len()]);
        let raw = p.hp_key(aead, &hp[..aead.key_len()]).unwrap();
        let sample: [u8; 16] = core::array::from_fn(|i| (i * 7 + 1) as u8);
        let mask = p.hp_mask(&raw, &sample);
        for long in [false, true] {
            for pn_len in 1..=4usize {
                let first0 = 0xc0 | (pn_len as u8 - 1);
                let pn0 = [0x11, 0x22, 0x33, 0x44];
                let (mut first, mut pn) = (first0, pn0);
                hk.protect(&p, &mut first, &mut pn[..pn_len], &sample, long).unwrap();
                let bits = if long { 0x0f } else { 0x1f };
                assert_eq!(first, first0 ^ (mask[0] & bits), "first byte, long {long}");
                for i in 0..pn_len {
                    assert_eq!(pn[i], pn0[i] ^ mask[1 + i]);
                }
                assert_eq!(
                    pn[pn_len..],
                    pn0[pn_len..],
                    "bytes past the packet number are untouched"
                );
                // Removing the mask reveals the length the caller chose.
                let got = hk.unprotect(&p, &mut first, &mut pn, &sample, long).unwrap();
                assert_eq!((got, first, pn), (pn_len, first0, pn0));
            }
        }
        let (mut first, mut pn) = (0x40u8, [0u8; 4]);
        assert_eq!(
            hk.protect(&p, &mut first, &mut pn[..0], &sample, false),
            Err(RecordError::HeaderLength)
        );
        assert_eq!(
            hk.protect(&p, &mut first, &mut [0u8; 5], &sample, false),
            Err(RecordError::HeaderLength)
        );
        // A masked length that does not fit the buffer.
        let mut first = 0x43 ^ mask[0] & 0x1f;
        assert_eq!(
            hk.unprotect(&p, &mut first, &mut [0u8; 3], &sample, false),
            Err(RecordError::HeaderLength)
        );
    }
}

#[test]
fn key_update_moves_both_sides_in_step() {
    let p = Software;
    for aead in AEADS {
        let mut tx0 = PacketKey::from_secret(&p, aead, &secret(3)).unwrap();
        let mut rx0 = PacketKey::from_secret(&p, aead, &secret(3)).unwrap();
        let mut tx1 = tx0.next_generation(&p).unwrap();
        let mut rx1 = rx0.next_generation(&p).unwrap();
        assert_eq!((tx0.generation(), tx1.generation()), (0, 1));
        let mut buf = *b"generation one";
        let tag = tx1.seal(&p, 0, b"h", &mut buf).unwrap();
        // The receiver's independently derived generation 1 opens it; generation 0 cannot.
        let mut a = buf;
        assert_eq!(rx0.open(&p, 0, b"h", &mut a, &tag), Err(RecordError::Authentication));
        rx1.open(&p, 0, b"h", &mut buf, &tag).unwrap();
        assert_eq!(&buf, b"generation one");
        // Packet number 0 under generation 0 and 1 gives different ciphertext: no nonce reuse across generations.
        let (mut x, mut y) = (*b"same", *b"same");
        let tag0 = tx0.seal(&p, 0, b"h", &mut x).unwrap();
        let mut tx1b = tx0.next_generation(&p).unwrap();
        let tag1 = tx1b.seal(&p, 0, b"h", &mut y).unwrap();
        assert_ne!((x, tag0), (y, tag1));
        // The chain continues, and each generation is distinct.
        let tx2 = tx1.next_generation(&p).unwrap();
        assert_eq!(tx2.generation(), 2);
        let mut z = *b"same";
        let mut tx2 = tx2;
        let tag2 = tx2.seal(&p, 0, b"h", &mut z).unwrap();
        assert_ne!((z, tag2), (y, tag1));
        assert_eq!(tx2.sealed(), 1, "a new generation starts its counters at zero");
    }
}

#[test]
fn key_update_over_a_real_session() {
    sec_common::big_stack(|| {
        let mut w = sec_common::World::new(
            vinc_crypto::IdentityAlg::Ed25519,
            vinc_crypto::IdentityAlg::Ed25519,
            true,
            true,
        );
        let out = w.full();
        let (i, r) = (out.i_est().unwrap(), out.r_est().unwrap());
        let tx = i.traffic.send_keys(&w.i_prov).unwrap();
        let rx = r.traffic.recv_keys(&w.r_prov).unwrap();
        let (mut tx1, mut rx1) = (
            tx.packet.next_generation(&w.i_prov).unwrap(),
            rx.packet.next_generation(&w.r_prov).unwrap(),
        );
        let mut buf = *b"after the update";
        let tag = tx1.seal(&w.i_prov, 3, b"x", &mut buf).unwrap();
        rx1.open(&w.r_prov, 3, b"x", &mut buf, &tag).unwrap();
        assert_eq!(&buf, b"after the update");
    });
}

#[test]
fn aes_gcm_keys_must_update_before_the_packet_limit() {
    let p = Software;
    assert_eq!(AES_GCM_PACKET_LIMIT, 1 << 22);
    assert_eq!(CHACHA_FAILURE_LIMIT, 1 << 36);
    assert_eq!(Limits::default().aes_gcm_packets, 1 << 22);
    assert_eq!(Limits::default().chacha_failures, 1 << 36);
    let limits = Limits {
        aes_gcm_packets: 3,
        chacha_failures: 1 << 36,
    };
    let mut key = PacketKey::from_secret(&p, Aead::Aes128Gcm, &secret(4))
        .unwrap()
        .with_limits(limits);
    let mut buf = [7u8; 8];
    for pn in 0..3 {
        key.seal(&p, pn, b"", &mut buf).unwrap();
    }
    let before = buf;
    assert_eq!(key.seal(&p, 3, b"", &mut buf), Err(RecordError::KeyUpdateRequired));
    assert_eq!(buf, before, "nothing is encrypted once the limit is hit");
    assert_eq!(key.seal(&p, 4, b"", &mut buf), Err(RecordError::KeyUpdateRequired));
    let mut next = key.next_generation(&p).unwrap();
    next.seal(&p, 0, b"", &mut buf).unwrap();
    assert_eq!(next.sealed(), 1);
    // ChaCha20-Poly1305 seals are not limited by packet count.
    let mut chacha = PacketKey::from_secret(&p, Aead::ChaCha20Poly1305, &secret(4))
        .unwrap()
        .with_limits(limits);
    for pn in 0..10 {
        chacha.seal(&p, pn, b"", &mut buf).unwrap();
    }
}

#[test]
fn chacha_keys_count_failed_opens_toward_their_limit() {
    let p = Software;
    let limits = Limits {
        aes_gcm_packets: 1 << 22,
        chacha_failures: 2,
    };
    let mut tx = PacketKey::from_secret(&p, Aead::ChaCha20Poly1305, &secret(6)).unwrap();
    let mut rx = PacketKey::from_secret(&p, Aead::ChaCha20Poly1305, &secret(6))
        .unwrap()
        .with_limits(limits);
    let mut good = [1u8; 8];
    let tag = tx.seal(&p, 0, b"", &mut good).unwrap();
    let forged = [0u8; 16];
    for _ in 0..2 {
        let mut copy = good;
        assert_eq!(
            rx.open(&p, 0, b"", &mut copy, &forged),
            Err(RecordError::Authentication)
        );
    }
    assert_eq!(rx.failed_opens(), 2);
    // At the limit even a genuine packet is refused: the caller must update keys.
    let mut copy = good;
    assert_eq!(
        rx.open(&p, 0, b"", &mut copy, &tag),
        Err(RecordError::KeyUpdateRequired)
    );
    let mut rx1 = rx.next_generation(&p).unwrap();
    let mut tx1 = tx.next_generation(&p).unwrap();
    let mut fresh = [2u8; 8];
    let tag1 = tx1.seal(&p, 0, b"", &mut fresh).unwrap();
    rx1.open(&p, 0, b"", &mut fresh, &tag1).unwrap();
    assert_eq!(rx1.failed_opens(), 0);
    // AES-GCM opens are not gated by failures.
    let mut aes = PacketKey::from_secret(&p, Aead::Aes128Gcm, &secret(6))
        .unwrap()
        .with_limits(limits);
    for _ in 0..5 {
        let mut copy = good;
        assert_eq!(
            aes.open(&p, 0, b"", &mut copy, &forged),
            Err(RecordError::Authentication)
        );
    }
}

#[test]
fn seal_open_and_header_protection_allocate_nothing() {
    let p = Software;
    for aead in AEADS {
        let mut tx = PacketKey::from_secret(&p, aead, &secret(8)).unwrap();
        let mut rx = PacketKey::from_secret(&p, aead, &secret(8)).unwrap();
        let hk = HeaderKey::from_secret(&p, aead, &secret(8)).unwrap();
        let mut payload = [3u8; 1400];
        let sample = [9u8; 16];
        let stats = vinc_tests::measure(|| {
            let tag = tx.seal(&p, 1, b"hdr", &mut payload).unwrap();
            let (mut first, mut pn) = (0x41u8, [0u8, 1]);
            hk.protect(&p, &mut first, &mut pn, &sample, false).unwrap();
            hk.unprotect(&p, &mut first, &mut pn, &sample, false).unwrap();
            rx.open(&p, 1, b"hdr", &mut payload, &tag).unwrap();
            let next = tx.next_generation(&p).unwrap();
            drop(next);
        });
        assert_eq!(stats.count(), 0, "{aead:?}: {stats:?}");
        assert_eq!(payload, [3u8; 1400]);
    }
}

fn model_window<const B: usize>(pns: &[u64]) {
    let mut w = ReplayWindow::<B>::new();
    let mut seen = BTreeSet::new();
    let mut max: Option<u64> = None;
    for &pn in pns {
        let expect = match max {
            None => Ok(()),
            Some(m) if pn > m => Ok(()),
            Some(m) if m - pn >= B as u64 => Err(ReplayError::TooOld),
            Some(_) if seen.contains(&pn) => Err(ReplayError::Duplicate),
            Some(_) => Ok(()),
        };
        assert_eq!(w.check(pn), expect, "check {pn} (window {B}, highest {max:?})");
        assert_eq!(w.check(pn), expect, "check does not change the window");
        assert_eq!(w.insert(pn), expect, "insert {pn}");
        if expect.is_ok() {
            seen.insert(pn);
            max = Some(max.map_or(pn, |m| m.max(pn)));
        }
        assert_eq!(w.highest(), max);
    }
}

fn walk() -> impl Strategy<Value = Vec<u64>> {
    let start = prop_oneof![Just(0u64), 0u64..5000, (u64::MAX - 5000)..=u64::MAX];
    (start, prop::collection::vec((0u64..6, 0u64..300), 0..300)).prop_map(|(start, steps)| {
        let mut cursor = start;
        steps
            .into_iter()
            .map(|(up, back)| {
                cursor = cursor.saturating_add(up);
                cursor.saturating_sub(back)
            })
            .collect()
    })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

    #[test]
    fn the_replay_window_matches_a_set_model(pns in walk()) {
        model_window::<64>(&pns);
        model_window::<128>(&pns);
        model_window::<1024>(&pns);
        model_window::<1>(&pns);
        model_window::<100>(&pns);
    }

    #[test]
    fn the_replay_window_matches_a_set_model_on_random_numbers(pns in prop::collection::vec(any::<u64>(), 0..100)) {
        model_window::<64>(&pns);
        model_window::<1024>(&pns);
    }

    #[test]
    fn the_amplification_budget_keeps_its_invariant(
        ops in prop::collection::vec((0u8..3, 0u64..3000), 0..200)
    ) {
        let mut budget = AmpBudget::new();
        let (mut rx, mut tx) = (0u128, 0u128);
        let mut validated = false;
        for (kind, n) in ops {
            match kind {
                0 => {
                    budget.on_receive(n);
                    rx += u128::from(n);
                }
                1 => {
                    let allowed = validated || tx + u128::from(n) + OVERHEAD as u128 <= rx * u128::from(FACTOR);
                    prop_assert_eq!(budget.can_send(n), allowed);
                    if budget.can_send(n) {
                        budget.on_send(n);
                        tx += u128::from(n);
                    }
                }
                _ => {
                    budget.validate();
                    validated = true;
                }
            }
            if !validated {
                prop_assert!(tx <= rx * u128::from(FACTOR), "tx {} rx {}", tx, rx);
            }
            prop_assert_eq!(budget.is_validated(), validated);
            prop_assert_eq!((u128::from(budget.received()), u128::from(budget.sent())), (rx, tx));
        }
    }
}

#[test]
fn replay_window_examples() {
    let mut w = ReplayWindow::<64>::new();
    assert_eq!(w.highest(), None);
    w.insert(100).unwrap();
    assert_eq!(w.insert(100), Err(ReplayError::Duplicate));
    assert_eq!(
        w.insert(36),
        Err(ReplayError::TooOld),
        "100 - 36 = 64 is outside a window of 64"
    );
    w.insert(37).unwrap();
    w.insert(99).unwrap();
    assert_eq!(w.insert(99), Err(ReplayError::Duplicate));
    w.insert(164).unwrap();
    assert_eq!(w.insert(100), Err(ReplayError::TooOld));
    assert_eq!(w.insert(164), Err(ReplayError::Duplicate));
    w.insert(101).unwrap();
    // A huge jump clears the window; the first packet number may be anything, including 0.
    w.insert(u64::MAX).unwrap();
    assert_eq!(w.insert(u64::MAX), Err(ReplayError::Duplicate));
    assert_eq!(w.insert(164), Err(ReplayError::TooOld));
    let mut z = ReplayWindow::<64>::default();
    z.insert(0).unwrap();
    assert_eq!(z.insert(0), Err(ReplayError::Duplicate));
}

#[test]
fn amp_budget_examples() {
    let mut b = AmpBudget::new();
    assert!(!b.can_send(0), "nothing may be sent before anything is received");
    b.on_receive(1200);
    assert!(b.can_send(3600 - 48));
    assert!(!b.can_send(3600 - 48 + 1));
    b.on_send(3000);
    assert!(b.can_send(552));
    assert!(!b.can_send(553));
    b.validate();
    assert!(b.can_send(u64::MAX));
    let mut huge = AmpBudget::new();
    huge.on_receive(u64::MAX);
    huge.on_receive(u64::MAX);
    huge.on_send(u64::MAX);
    huge.on_send(u64::MAX);
    assert!(huge.can_send(1), "the comparison does not overflow");
}

fn token_key() -> TokenKey<Software> {
    TokenKey::new(&Software, &secret(0x42)).unwrap()
}

#[test]
fn tokens_validate_for_their_address_and_kind() {
    let p = Software;
    let key = token_key();
    let addr = b"\x7f\x00\x00\x01\x1f\x90";
    let mut buf = [0u8; MAX_TOKEN_LEN];
    for kind in [TokenKind::Retry, TokenKind::NewToken] {
        let n = key.issue(&p, addr, kind, 1_000, &[5; 12], &mut buf).unwrap();
        assert_eq!(n, 12 + addr.len() + 9 + 16);
        let token = &buf[..n];
        key.validate(&p, token, addr, kind, 1_000).unwrap();
        key.validate(&p, token, addr, kind, 1_000 + kind.lifetime_ns()).unwrap();
        assert_eq!(
            key.validate(&p, token, addr, kind, 1_001 + kind.lifetime_ns()),
            Err(TokenError::Expired)
        );
        assert_eq!(key.validate(&p, token, addr, kind, 999), Err(TokenError::NotYetValid));
        assert_eq!(
            key.validate(&p, token, b"\x7f\x00\x00\x02\x1f\x90", kind, 1_000),
            Err(TokenError::WrongAddress)
        );
        assert_eq!(key.validate(&p, token, b"", kind, 1_000), Err(TokenError::WrongAddress));
        let other = if kind == TokenKind::Retry {
            TokenKind::NewToken
        } else {
            TokenKind::Retry
        };
        assert_eq!(key.validate(&p, token, addr, other, 1_000), Err(TokenError::WrongKind));
        // Another key did not issue it.
        let stranger = TokenKey::new(&p, &secret(0x43)).unwrap();
        assert_eq!(
            stranger.validate(&p, token, addr, kind, 1_000),
            Err(TokenError::Authentication)
        );
        // Every byte is authenticated, and every truncation is refused.
        for at in 0..n {
            let mut bad = token.to_vec();
            bad[at] ^= 1;
            assert!(key.validate(&p, &bad, addr, kind, 1_000).is_err(), "byte {at}");
            assert!(key.validate(&p, &token[..at], addr, kind, 1_000).is_err(), "cut {at}");
        }
        let mut longer = token.to_vec();
        longer.push(0);
        assert!(key.validate(&p, &longer, addr, kind, 1_000).is_err());
    }
    const { assert!(RETRY_LIFETIME_NS < NEW_TOKEN_LIFETIME_NS) };
}

#[test]
fn token_edge_cases() {
    let p = Software;
    let key = token_key();
    let mut buf = [0u8; MAX_TOKEN_LEN];
    let longest = [9u8; MAX_ADDR_LEN];
    let n = key
        .issue(&p, &longest, TokenKind::Retry, 5, &[1; 12], &mut buf)
        .unwrap();
    assert_eq!(n, MAX_TOKEN_LEN);
    key.validate(&p, &buf[..n], &longest, TokenKind::Retry, 5).unwrap();
    assert_eq!(
        key.issue(&p, &[0; MAX_ADDR_LEN + 1], TokenKind::Retry, 5, &[1; 12], &mut buf),
        Err(TokenError::AddressTooLong)
    );
    assert_eq!(
        key.issue(&p, b"abc", TokenKind::Retry, 5, &[1; 12], &mut buf[..30]),
        Err(TokenError::BufferTooSmall)
    );
    let n = key.issue(&p, b"", TokenKind::NewToken, 0, &[2; 12], &mut buf).unwrap();
    key.validate(&p, &buf[..n], b"", TokenKind::NewToken, 0).unwrap();
    assert_eq!(
        key.validate(&p, &[], b"", TokenKind::Retry, 0),
        Err(TokenError::Malformed)
    );
    assert_eq!(
        key.validate(&p, &[0; 200], b"", TokenKind::Retry, 0),
        Err(TokenError::Malformed)
    );
    // The same address, time and kind with another nonce is another token.
    let mut other = [0u8; MAX_TOKEN_LEN];
    let m = key
        .issue(&p, b"", TokenKind::NewToken, 0, &[3; 12], &mut other)
        .unwrap();
    assert_ne!(buf[..n], other[..m]);
}

#[test]
fn labels_are_prefixed_unique_and_distinct_from_the_crypto_labels() {
    let mut all: Vec<&str> = labels::ALL.to_vec();
    all.extend(vinc_crypto::labels::ALL);
    for l in &all {
        assert!(l.starts_with("VINC 2026 v1 "), "{l}");
        assert!(l.len() > labels::PREFIX.len(), "{l}");
        assert!(l.is_ascii());
        assert!(!l.contains('\u{2013}') && !l.contains('\u{2014}'));
    }
    let unique: BTreeSet<&str> = all.iter().copied().collect();
    assert_eq!(unique.len(), all.len(), "a label is used twice");
    assert_eq!(labels::PREFIX, vinc_crypto::labels::PREFIX);
    assert_eq!(labels::SIGNATURE_RESPONDER, "VINC 2026 v1 responder");
    assert_eq!(labels::SIGNATURE_INITIATOR, "VINC 2026 v1 initiator");
    assert_eq!(labels::HANDSHAKE, "VINC 2026 v1 handshake");
}

#[test]
fn a_key_never_seals_a_packet_number_twice() {
    let p = Software;
    for aead in AEADS {
        let mut k = PacketKey::from_secret(&p, aead, &secret(5)).unwrap();
        let mut buf = [7u8; 32];
        k.seal(&p, 5, b"aad", &mut buf).unwrap();
        for pn in [5u64, 4, 0] {
            assert_eq!(
                k.seal(&p, pn, b"aad", &mut buf),
                Err(RecordError::NotIncreasing),
                "{pn}"
            );
        }
        assert_eq!(k.sealed(), 1, "a refused seal is not counted");
        k.seal(&p, 6, b"aad", &mut buf).unwrap();
        k.seal(&p, 1000, b"aad", &mut buf).unwrap();
        // A fresh generation has sealed nothing yet.
        let mut next = k.next_generation(&p).unwrap();
        next.seal(&p, 7, b"aad", &mut buf).unwrap();
    }
}
