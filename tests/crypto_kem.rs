//! Tests of the ML-KEM-768 provider: NIST ACVP vectors, round trips, negative and allocation tests.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    deprecated
)]

use ml_kem::ExpandedKeyEncoding;
use pinc_crypto::provider::{KEM_CIPHERTEXT_LEN, KEM_ENCAPS_KEY_LEN};
use pinc_crypto::{CryptoError, Provider, Software};
use proptest::prelude::*;

mod acvp_kem;
mod hexutil;
use hexutil::{arr, hex};

pinc_tests::install_counting_allocator!();

#[test]
fn acvp_key_generation() {
    let p = Software;
    for (id, d, z, ek, dk) in acvp_kem::KEYGEN {
        let (dec, enc) = p.kem_keygen(&arr(d), &arr(z));
        assert_eq!(p.kem_encaps_key_bytes(&enc).to_vec(), hex(ek), "ek of tcId {id}");
        assert_eq!(dec.to_expanded_bytes().to_vec(), hex(dk), "dk of tcId {id}");
    }
}

#[test]
fn acvp_encapsulation() {
    let p = Software;
    for (id, ek, m, c, k) in acvp_kem::ENCAPS {
        let ek = p.kem_encaps_key(&hex(ek)).unwrap();
        let (ct, shared) = p.kem_encapsulate(&ek, &arr(m)).unwrap();
        assert_eq!(p.kem_ciphertext_bytes(&ct).to_vec(), hex(c), "ciphertext of tcId {id}");
        assert_eq!(shared.expose().to_vec(), hex(k), "secret of tcId {id}");
    }
}

#[test]
fn acvp_decapsulation_including_implicit_rejection() {
    let p = Software;
    for (id, dk, c, k, reason) in acvp_kem::DECAPS {
        let dk =
            <Software as Provider>::KemDecapsKey::from_expanded_bytes(&hex(dk).as_slice().try_into().unwrap()).unwrap();
        let ct = p.kem_ciphertext(&hex(c)).unwrap();
        let shared = p.kem_decapsulate(&dk, &ct).unwrap();
        assert_eq!(shared.expose().to_vec(), hex(k), "tcId {id}: {reason}");
    }
}

#[test]
fn acvp_encapsulation_key_check() {
    let p = Software;
    for (id, ek, passed, reason) in acvp_kem::EK_CHECK {
        let r = p.kem_encaps_key(&hex(ek));
        assert_eq!(r.is_ok(), *passed, "tcId {id}: {reason}");
        if !passed {
            assert_eq!(r.err(), Some(CryptoError::InvalidEncapsulationKey));
        }
    }
}

#[test]
fn invalid_encapsulation_keys_are_rejected() {
    let p = Software;
    let (_, ek) = p.kem_keygen(&[1; 32], &[2; 32]);
    let good = p.kem_encaps_key_bytes(&ek);
    assert!(p.kem_encaps_key(&good).is_ok());
    // A coefficient of 0xfff is at least q = 3329: the modulus check fails.
    let mut bad = good;
    bad[0] = 0xff;
    bad[1] |= 0x0f;
    assert_eq!(p.kem_encaps_key(&bad).err(), Some(CryptoError::InvalidEncapsulationKey));
    for len in [0, 1, KEM_ENCAPS_KEY_LEN - 1, KEM_ENCAPS_KEY_LEN + 1] {
        assert_eq!(
            p.kem_encaps_key(&vec![0u8; len]).err(),
            Some(CryptoError::InvalidEncapsulationKey)
        );
    }
    for len in [0, KEM_CIPHERTEXT_LEN - 1, KEM_CIPHERTEXT_LEN + 1] {
        assert_eq!(
            p.kem_ciphertext(&vec![0u8; len]).err(),
            Some(CryptoError::InvalidLength)
        );
    }
}

#[test]
fn a_tampered_ciphertext_gives_a_different_secret() {
    let p = Software;
    let (dk, ek) = p.kem_keygen(&[3; 32], &[4; 32]);
    let (ct, shared) = p.kem_encapsulate(&ek, &[5; 32]).unwrap();
    assert_eq!(p.kem_decapsulate(&dk, &ct).unwrap(), shared);
    let mut bytes = p.kem_ciphertext_bytes(&ct).to_vec();
    bytes[100] ^= 1;
    let forged = p.kem_ciphertext(&bytes).unwrap();
    let rejected = p.kem_decapsulate(&dk, &forged).unwrap();
    assert_ne!(rejected, shared);
    assert_eq!(
        rejected,
        p.kem_decapsulate(&dk, &forged).unwrap(),
        "implicit rejection is deterministic"
    );
    let (other, _) = p.kem_keygen(&[6; 32], &[7; 32]);
    assert_ne!(p.kem_decapsulate(&other, &ct).unwrap(), shared, "a wrong key");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(24))]
    #[test]
    fn round_trip_and_determinism(d in any::<[u8; 32]>(), z in any::<[u8; 32]>(), m in any::<[u8; 32]>()) {
        let p = Software;
        let (dk, ek) = p.kem_keygen(&d, &z);
        let (dk2, ek2) = p.kem_keygen(&d, &z);
        prop_assert_eq!(p.kem_encaps_key_bytes(&ek), p.kem_encaps_key_bytes(&ek2));
        let ek = p.kem_encaps_key(&p.kem_encaps_key_bytes(&ek)).unwrap();
        let (ct, s1) = p.kem_encapsulate(&ek, &m).unwrap();
        let (ct2, s2) = p.kem_encapsulate(&ek, &m).unwrap();
        prop_assert_eq!(p.kem_ciphertext_bytes(&ct), p.kem_ciphertext_bytes(&ct2));
        prop_assert_eq!(&s1, &s2);
        prop_assert_eq!(p.kem_decapsulate(&dk, &ct).unwrap(), s1.clone());
        prop_assert_eq!(p.kem_decapsulate(&dk2, &ct).unwrap(), s1);
    }
}

#[test]
fn kem_operations_do_not_allocate() {
    let p = Software;
    let (dk, ek) = p.kem_keygen(&[1; 32], &[2; 32]);
    let ek_bytes = p.kem_encaps_key_bytes(&ek);
    // The stack frames are large: run the measured work on a thread with room for them.
    let stats = std::thread::Builder::new()
        .stack_size(8 << 20)
        .spawn(move || {
            pinc_tests::measure(|| {
                let (_dk, ek) = p.kem_keygen(&[1; 32], &[2; 32]);
                let ek2 = p.kem_encaps_key(&ek_bytes).unwrap();
                let (ct, s) = p.kem_encapsulate(&ek2, &[3; 32]).unwrap();
                assert_eq!(p.kem_decapsulate(&dk, &ct).unwrap(), s);
                let _ = p.kem_encaps_key_bytes(&ek);
            })
        })
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(stats.count(), 0, "{stats:?}");
}
