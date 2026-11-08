//! Tests of the identities: RFC and NIST known answers, negative cases, round trips and allocation counts.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    deprecated
)]

use ml_dsa::{ExpandedSigningKey, ExpandedSigningKeyBytes, MlDsa65};
use vinc_crypto::identity::{MAX_PUBLIC_KEY_LEN, MAX_SIGNATURE_LEN, verify, verify_ml_dsa_65, verify_node};
use vinc_crypto::{CryptoError, IdentityAlg, Keypair, NodeId};

mod acvp_dsa;
mod hexutil;
use hexutil::{arr, hex};

vinc_tests::install_counting_allocator!();

const ALL: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

/// Run `f` on a thread with a large stack: ML-DSA-65 keys and working state are tens of KiB.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

fn seed_for(alg: IdentityAlg, tweak: u8) -> Vec<u8> {
    (0..alg.seed_len())
        .map(|i| (i as u8).wrapping_mul(7).wrapping_add(tweak).wrapping_add(1))
        .collect()
}

fn public(kp: &Keypair) -> Vec<u8> {
    let mut pk = vec![0u8; MAX_PUBLIC_KEY_LEN];
    let n = kp.public_key(&mut pk).unwrap();
    pk.truncate(n);
    pk
}

fn sign(kp: &Keypair, msg: &[u8]) -> Vec<u8> {
    let mut sig = vec![0u8; MAX_SIGNATURE_LEN];
    let n = kp.sign(msg, &mut sig).unwrap();
    sig.truncate(n);
    sig
}

#[test]
fn ed25519_rfc8032() {
    // RFC 8032 section 7.1, tests 1 and 2.
    for (sk, pk, msg, sig) in [
        (
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            "",
            concat!(
                "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555fb8821590a33bacc61e39701cf9b46b",
                "d25bf5f0595bbe24655141438e7a100b"
            ),
        ),
        (
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
            "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            "72",
            concat!(
                "92a009a9f0d4cab8720e820b5f642540a2b27b5416503f8fb3762223ebdb69da085ac1e43e15996e458f3613d0f11d8c",
                "387b2eaeb4302aeeb00d291612bb0c00"
            ),
        ),
    ] {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &hex(sk)).unwrap();
        assert_eq!(public(&kp), hex(pk));
        assert_eq!(sign(&kp, &hex(msg)), hex(sig));
        verify(IdentityAlg::Ed25519, &hex(pk), &hex(msg), &hex(sig)).unwrap();
        // The node id of an Ed25519 key is the key itself.
        assert_eq!(kp.node_id().bytes, arr::<32>(pk));
    }
}

#[test]
fn p256_rfc6979_deterministic_signature() {
    // RFC 6979 appendix A.2.5, SHA-256, message "sample". The RFC's `s` is high, so the low-s form n - s is expected.
    let kp = Keypair::from_seed(
        IdentityAlg::EcdsaP256,
        &hex("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"),
    )
    .unwrap();
    let want = hex(concat!(
        "efd48b2aacb6a8fd1140dd9cd45e81d69d2c877b56aaf991c34d0ea84eaf3716",
        "0834e36ad29a83bf2bc9385e491d6099c8fdf9d1ed67aa7ea5f51f93782857a9"
    ));
    let sig = sign(&kp, b"sample");
    assert_eq!(sig, want);
    assert_eq!(sign(&kp, b"sample"), sig, "deterministic");
    verify(IdentityAlg::EcdsaP256, &public(&kp), b"sample", &sig).unwrap();
}

/// `n - s` for the P-256 group order, big endian.
fn flip_s(sig: &[u8]) -> Vec<u8> {
    let n = hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    let mut out = sig.to_vec();
    let mut borrow = 0i16;
    for i in (0..32).rev() {
        let d = i16::from(n[i]) - i16::from(sig[32 + i]) - borrow;
        out[32 + i] = d.rem_euclid(256) as u8;
        borrow = i16::from(d < 0);
    }
    out
}

#[test]
fn p256_rejects_high_s_and_corrupt_input() {
    let kp = Keypair::from_seed(IdentityAlg::EcdsaP256, &seed_for(IdentityAlg::EcdsaP256, 3)).unwrap();
    let pk = public(&kp);
    assert_eq!(pk.len(), 33);
    let sig = sign(&kp, b"msg");
    verify(IdentityAlg::EcdsaP256, &pk, b"msg", &sig).unwrap();
    let high = flip_s(&sig);
    assert_ne!(high, sig);
    assert_eq!(
        verify(IdentityAlg::EcdsaP256, &pk, b"msg", &high),
        Err(CryptoError::HighS)
    );
    assert_eq!(
        verify(IdentityAlg::EcdsaP256, &pk, b"other", &sig),
        Err(CryptoError::InvalidSignature)
    );
    let mut bad_pk = pk.clone();
    bad_pk[0] = 0x05;
    assert_eq!(
        verify(IdentityAlg::EcdsaP256, &bad_pk, b"msg", &sig),
        Err(CryptoError::InvalidPublicKey)
    );
    bad_pk[0] = 0x04;
    assert_eq!(
        verify(IdentityAlg::EcdsaP256, &bad_pk, b"msg", &sig),
        Err(CryptoError::InvalidPublicKey)
    );
    bad_pk[0] = 0x02;
    bad_pk[1..].fill(0xff);
    assert_eq!(
        verify(IdentityAlg::EcdsaP256, &bad_pk, b"msg", &sig),
        Err(CryptoError::InvalidPublicKey)
    );
    assert_eq!(
        verify(IdentityAlg::EcdsaP256, &pk, b"msg", &[0u8; 64]),
        Err(CryptoError::InvalidSignature)
    );
    // A seed of zero or at least the group order is not a key.
    for seed in [[0u8; 32], [0xff; 32]] {
        assert_eq!(
            Keypair::from_seed(IdentityAlg::EcdsaP256, &seed).unwrap_err(),
            CryptoError::InvalidSecretKey
        );
    }
}

#[test]
fn ml_dsa_65_acvp_key_generation() {
    big(|| {
        for (id, seed, pk) in acvp_dsa::KEYGEN {
            let kp = Keypair::from_seed(IdentityAlg::MlDsa65, &hex(seed)).unwrap();
            assert_eq!(public(&kp), hex(pk), "tcId {id}");
            assert_eq!(public(&kp).len(), 1952);
        }
    });
}

#[test]
fn ml_dsa_65_acvp_signature_verification() {
    big(|| {
        for (id, pk, ctx, msg, sig, passed, reason) in acvp_dsa::SIGVER {
            let r = verify_ml_dsa_65(&hex(pk), &hex(ctx), &hex(msg), &hex(sig));
            assert_eq!(r.is_ok(), *passed, "tcId {id}: {reason}");
            if !passed {
                assert_eq!(r, Err(CryptoError::InvalidSignature), "tcId {id}");
            }
        }
    });
}

#[test]
fn ml_dsa_65_acvp_signature_generation() {
    // The ACVP signing vectors give the expanded secret key, which only the underlying crate takes.
    big(|| {
        for (id, sk, ctx, msg, rnd, sig) in acvp_dsa::SIGGEN {
            let sk = ExpandedSigningKeyBytes::<MlDsa65>::try_from(hex(sk).as_slice()).unwrap();
            let key = ExpandedSigningKey::<MlDsa65>::from_expanded(&sk);
            let (ctx, msg) = (hex(ctx), hex(msg));
            let got = if rnd.is_empty() {
                key.sign_deterministic(&msg, &ctx).unwrap()
            } else {
                let rnd = ml_dsa::B32::try_from(hex(rnd).as_slice()).unwrap();
                key.sign_internal(&[&[0, ctx.len() as u8], &ctx, &msg], &rnd)
            };
            assert_eq!(got.encode().to_vec(), hex(sig), "tcId {id}");
        }
    });
}

#[test]
fn ml_dsa_65_signing_follows_fips_204_with_an_empty_context() {
    big(|| {
        let seed = hex(acvp_dsa::KEYGEN[0].1);
        let kp = Keypair::from_seed(IdentityAlg::MlDsa65, &seed).unwrap();
        let key = ml_dsa::SigningKey::<MlDsa65>::from_seed(&ml_dsa::Seed::try_from(seed.as_slice()).unwrap());
        for msg in [&b""[..], b"x", b"a longer message to sign"] {
            let want = key
                .expanded_key()
                .sign_deterministic(msg, &[])
                .unwrap()
                .encode()
                .to_vec();
            let sig = sign(&kp, msg);
            assert_eq!(sig, want);
            assert_eq!(sig.len(), 3309);
            verify(IdentityAlg::MlDsa65, &public(&kp), msg, &sig).unwrap();
        }
        // Hedged signing differs per `rnd` and still verifies.
        let mut a = vec![0u8; MAX_SIGNATURE_LEN];
        let mut b = vec![0u8; MAX_SIGNATURE_LEN];
        let n = kp.sign_with_rnd(b"m", &[1; 32], &mut a).unwrap();
        kp.sign_with_rnd(b"m", &[2; 32], &mut b).unwrap();
        assert_ne!(a, b);
        verify(IdentityAlg::MlDsa65, &public(&kp), b"m", &a[..n]).unwrap();
    });
}

#[test]
fn every_algorithm_round_trips_and_rejects_forgeries() {
    big(|| {
        for alg in ALL {
            let kp = Keypair::from_seed(alg, &seed_for(alg, 11)).unwrap();
            assert_eq!(kp.alg(), alg);
            let pk = public(&kp);
            assert_eq!(pk.len(), alg.public_key_len());
            let sig = sign(&kp, b"hello");
            assert_eq!(sig.len(), alg.signature_len());
            verify(alg, &pk, b"hello", &sig).unwrap();
            assert!(verify(alg, &pk, b"hellp", &sig).is_err(), "{alg:?}: wrong message");
            for i in [0, sig.len() / 2, sig.len() - 1] {
                let mut bad = sig.clone();
                bad[i] ^= 1;
                assert!(verify(alg, &pk, b"hello", &bad).is_err(), "{alg:?}: signature byte {i}");
            }
            let other = Keypair::from_seed(alg, &seed_for(alg, 12)).unwrap();
            assert!(
                verify(alg, &public(&other), b"hello", &sig).is_err(),
                "{alg:?}: wrong key"
            );
            // Wrong lengths are refused, never a panic.
            assert_eq!(verify(alg, &pk[1..], b"hello", &sig), Err(CryptoError::InvalidLength));
            assert_eq!(verify(alg, &pk, b"hello", &sig[1..]), Err(CryptoError::InvalidLength));
            assert_eq!(verify(alg, &[], b"hello", &[]), Err(CryptoError::InvalidLength));
            // Output buffers that are too small are refused.
            let mut small = vec![0u8; alg.signature_len() - 1];
            assert_eq!(kp.sign(b"x", &mut small), Err(CryptoError::InvalidLength));
            let mut small = vec![0u8; alg.public_key_len() - 1];
            assert_eq!(kp.public_key(&mut small), Err(CryptoError::InvalidLength));
            // A wrong-sized seed is refused.
            assert_eq!(
                Keypair::from_seed(alg, &[0; 5]).unwrap_err(),
                CryptoError::InvalidLength
            );
        }
    });
}

#[test]
fn a_hybrid_signature_needs_both_halves() {
    big(|| {
        let alg = IdentityAlg::Hybrid;
        let kp = Keypair::from_seed(alg, &seed_for(alg, 5)).unwrap();
        let pk = public(&kp);
        let sig = sign(&kp, b"both");
        verify(alg, &pk, b"both", &sig).unwrap();
        let mut ed_broken = sig.clone();
        ed_broken[10] ^= 1;
        assert!(verify(alg, &pk, b"both", &ed_broken).is_err());
        let mut ml_broken = sig.clone();
        ml_broken[64 + 100] ^= 1;
        assert!(verify(alg, &pk, b"both", &ml_broken).is_err());
        // Neither half is a valid plain signature on the message, and the hybrid is not a plain signature either.
        assert!(verify(IdentityAlg::Ed25519, &pk[..32], b"both", &sig[..64]).is_err());
        assert!(verify_ml_dsa_65(&pk[32..], &[], b"both", &sig[64..]).is_err());
        // The hybrid is made of the Ed25519 and ML-DSA keys of its two seeds.
        let seed = seed_for(alg, 5);
        let ed = Keypair::from_seed(IdentityAlg::Ed25519, &seed[..32]).unwrap();
        let ml = Keypair::from_seed(IdentityAlg::MlDsa65, &seed[32..]).unwrap();
        assert_eq!(&pk[..32], public(&ed).as_slice());
        assert_eq!(&pk[32..], public(&ml).as_slice());
    });
}

#[test]
fn wire_tags_are_stable_and_round_trip() {
    let tags: Vec<u8> = ALL.iter().map(|a| a.tag()).collect();
    assert_eq!(tags, [1, 2, 3, 4]);
    for alg in ALL {
        assert_eq!(IdentityAlg::from_tag(alg.tag()), Some(alg));
    }
    for t in [0u8, 5, 6, 255] {
        assert_eq!(IdentityAlg::from_tag(t), None);
    }
}

#[test]
fn node_ids_bind_the_algorithm_and_key() {
    big(|| {
        let ed = Keypair::from_seed(IdentityAlg::Ed25519, &seed_for(IdentityAlg::Ed25519, 1)).unwrap();
        let ed_pk = public(&ed);
        let id = NodeId::from_public(IdentityAlg::Ed25519, &ed_pk).unwrap();
        assert_eq!(id.bytes.to_vec(), ed_pk);
        assert!(id.matches(IdentityAlg::Ed25519, &ed_pk));

        for alg in [IdentityAlg::EcdsaP256, IdentityAlg::MlDsa65, IdentityAlg::Hybrid] {
            let kp = Keypair::from_seed(alg, &seed_for(alg, 2)).unwrap();
            let pk = public(&kp);
            let id = NodeId::from_public(alg, &pk).unwrap();
            assert_eq!(id, kp.node_id());
            let mut h = blake3::Hasher::new_derive_key("VINC 2026 v1 node id");
            h.update(&[alg.tag()]);
            h.update(&pk);
            assert_eq!(id.bytes, *h.finalize().as_bytes(), "{alg:?}");
            assert!(id.matches(alg, &pk));
            // A mismatch: another key, another algorithm, a truncated key.
            let other = Keypair::from_seed(alg, &seed_for(alg, 3)).unwrap();
            assert!(!id.matches(alg, &public(&other)));
            assert!(!id.matches(IdentityAlg::Ed25519, &ed_pk));
            assert!(!id.matches(alg, &pk[1..]));
            let sig = sign(&kp, b"m");
            verify_node(&id, &pk, b"m", &sig).unwrap();
            assert_eq!(
                verify_node(&id, &public(&other), b"m", &sig),
                Err(CryptoError::NodeIdMismatch)
            );
        }
        assert_eq!(
            NodeId::from_public(IdentityAlg::Ed25519, &[0; 31]),
            Err(CryptoError::InvalidLength)
        );
    });
}

#[test]
fn sign_and_verify_do_not_allocate() {
    for alg in ALL {
        let stats = std::thread::Builder::new()
            .stack_size(64 << 20)
            .spawn(move || {
                let kp = Keypair::from_seed(alg, &seed_for(alg, 9)).unwrap();
                let pk = public(&kp);
                let mut sig = vec![0u8; MAX_SIGNATURE_LEN];
                let mut pkbuf = vec![0u8; MAX_PUBLIC_KEY_LEN];
                vinc_tests::measure(|| {
                    let n = kp.sign(b"msg", &mut sig).unwrap();
                    verify(alg, &pk, b"msg", &sig[..n]).unwrap();
                    kp.public_key(&mut pkbuf).unwrap();
                    let _ = kp.node_id();
                })
            })
            .unwrap()
            .join()
            .unwrap();
        assert_eq!(stats.count(), 0, "{alg:?} allocated {stats:?}");
    }
}
