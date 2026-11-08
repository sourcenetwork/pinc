//! Record protection, key rolls and the limits, the amplification budget and labels.
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
use vinc_security::{AmpBudget, HeaderKey, Limits, PacketKey, RecordError, labels, roll_secret};

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

fn dh(tag: u8) -> Secret<32> {
    Secret::new([tag; 32])
}

#[test]
fn a_key_roll_moves_both_sides_in_step() {
    let p = Software;
    for aead in AEADS {
        let mut tx0 = PacketKey::from_secret(&p, aead, &secret(3)).unwrap();
        let mut rx0 = PacketKey::from_secret(&p, aead, &secret(3)).unwrap();
        // Both sides roll with the same Diffie-Hellman value and need no other message to agree.
        let mut tx1 = tx0.rolled(&p, &dh(9)).unwrap();
        let mut rx1 = rx0.rolled(&p, &dh(9)).unwrap();
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
        let mut tx1b = tx0.rolled(&p, &dh(9)).unwrap();
        let tag1 = tx1b.seal(&p, 0, b"h", &mut y).unwrap();
        assert_ne!((x, tag0), (y, tag1));
        // A different Diffie-Hellman value gives a different generation: the old secret alone is not enough.
        let mut other = tx0.rolled(&p, &dh(10)).unwrap();
        let mut o = *b"same";
        let tag_o = other.seal(&p, 0, b"h", &mut o).unwrap();
        assert_ne!((o, tag_o), (y, tag1));
        // The chain continues, and each generation is distinct.
        let tx2 = tx1.rolled(&p, &dh(11)).unwrap();
        assert_eq!(tx2.generation(), 2);
        let mut z = *b"same";
        let mut tx2 = tx2;
        let tag2 = tx2.seal(&p, 0, b"h", &mut z).unwrap();
        assert_ne!((z, tag2), (y, tag1));
        assert_eq!(tx2.sealed(), 1, "a new generation starts its counters at zero");
    }
}

#[test]
fn the_rolled_secret_depends_on_the_old_secret_and_the_fresh_value() {
    // Post-compromise: with the old secret known and a different (or no) Diffie-Hellman value, the next secret
    // cannot be computed. The roll is not the hash successor `expand(secret)` either.
    let (old, fresh) = (secret(5), dh(6));
    let next = roll_secret(&old, &fresh);
    assert_ne!(next.expose(), old.expose());
    assert_ne!(
        next.expose(),
        roll_secret(&old, &dh(7)).expose(),
        "another value, another secret"
    );
    assert_ne!(
        next.expose(),
        roll_secret(&secret(4), &fresh).expose(),
        "another old secret"
    );
    assert_ne!(next.expose(), roll_secret(&old, &Secret::new([0; 32])).expose());
    let mut hash_successor = [0u8; 32];
    expand(old.expose(), labels::KEY_ROLL, &[], &mut hash_successor);
    assert_ne!(&hash_successor, next.expose(), "not a function of the old secret alone");
    // The roll label is its own domain.
    assert!(labels::ALL.contains(&labels::KEY_ROLL) && labels::ALL.contains(&labels::CID_SECRET));
}

#[test]
fn aes_gcm_keys_must_roll_before_the_packet_limit() {
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
    assert_eq!(key.seal(&p, 3, b"", &mut buf), Err(RecordError::KeyRollRequired));
    assert_eq!(buf, before, "nothing is encrypted once the limit is hit");
    assert_eq!(key.seal(&p, 4, b"", &mut buf), Err(RecordError::KeyRollRequired));
    let mut next = key.rolled(&p, &dh(1)).unwrap();
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
    // At the limit even a genuine packet is refused: the caller must roll keys.
    let mut copy = good;
    assert_eq!(rx.open(&p, 0, b"", &mut copy, &tag), Err(RecordError::KeyRollRequired));
    let mut rx1 = rx.rolled(&p, &dh(1)).unwrap();
    let mut tx1 = tx.rolled(&p, &dh(1)).unwrap();
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
            let next = tx.rolled(&p, &dh(1)).unwrap();
            drop(next);
        });
        assert_eq!(stats.count(), 0, "{aead:?}: {stats:?}");
        assert_eq!(payload, [3u8; 1400]);
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(400))]

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
        let mut next = k.rolled(&p, &dh(1)).unwrap();
        next.seal(&p, 7, b"aad", &mut buf).unwrap();
    }
}
