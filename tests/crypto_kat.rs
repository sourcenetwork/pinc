//! Known-answer, negative, round-trip and allocation tests of the `Provider` primitives.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use proptest::prelude::*;
use pinc_crypto::{Aead, CryptoError, Provider, Software};
use pinc_tests::SplitMix64;

mod hexutil;
use hexutil::{arr, hex};

pinc_tests::install_counting_allocator!();

const ALGS: [Aead; 2] = [Aead::ChaCha20Poly1305, Aead::Aes128Gcm];

fn key_for(alg: Aead, rng: &mut SplitMix64) -> Vec<u8> {
    let mut k = vec![0u8; alg.key_len()];
    rng.fill(&mut k);
    k
}

#[test]
fn x25519_rfc7748_scalar_multiplication() {
    let p = Software;
    // RFC 7748 section 5.2, both vectors: the secret is the scalar, the "peer" is the u-coordinate.
    for (scalar, u, out) in [
        (
            "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
            "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
            "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552",
        ),
        (
            "4b66e9d4d1b4673c5ad22691957d6af5c11b6421e0ea01d42ca4169e7918ba0d",
            "e5210f12786811d3f4b7959d0538ae2c31dbe7106fc03c3efc4cd549c715a493",
            "95cbde9476e8907d7aade45cb4b873f88b595a68799fa152e6f8f7647aac7957",
        ),
    ] {
        let secret = p.x25519_secret(&arr(scalar));
        let shared = p.x25519_dh(&secret, &arr(u)).unwrap();
        assert_eq!(shared.expose(), &arr::<32>(out));
    }
}

#[test]
fn x25519_rfc7748_diffie_hellman() {
    let p = Software;
    // RFC 7748 section 6.1.
    let alice = p.x25519_secret(&arr("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"));
    let bob = p.x25519_secret(&arr("5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb"));
    let alice_pub = p.x25519_public(&alice);
    let bob_pub = p.x25519_public(&bob);
    assert_eq!(
        alice_pub,
        arr::<32>("8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a")
    );
    assert_eq!(
        bob_pub,
        arr::<32>("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
    );
    let k1 = p.x25519_dh(&alice, &bob_pub).unwrap();
    let k2 = p.x25519_dh(&bob, &alice_pub).unwrap();
    let want = arr::<32>("4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742");
    assert_eq!(k1.expose(), &want);
    assert_eq!(k1, k2);
}

#[test]
fn x25519_rejects_low_order_points() {
    let p = Software;
    let secret = p.x25519_secret(&[7; 32]);
    let mut one = [0u8; 32];
    one[0] = 1;
    for low in [
        [0u8; 32],
        one,
        arr("e0eb7a7c3b41b8ae1656e3faf19fc46ada098deb9c32b1fd866205165f49b800"),
        arr("5f9c95bca3508c24b1d0b1559c83ef5b04445cc4581c8e86d8224eddd09f1157"),
    ] {
        assert_eq!(p.x25519_dh(&secret, &low).unwrap_err(), CryptoError::NonContributory);
    }
}

#[test]
fn sha256_known_answers() {
    let p = Software;
    assert_eq!(
        p.sha256(b"abc"),
        arr::<32>("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
    );
    assert_eq!(
        p.sha256(b""),
        arr::<32>("e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
    );
}

#[test]
fn chacha20_poly1305_rfc8439() {
    let p = Software;
    // RFC 8439 section 2.8.2.
    let key = hex("808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f");
    let nonce = arr::<12>("070000004041424344454647");
    let aad = hex("50515253c0c1c2c3c4c5c6c7");
    let plain = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
    let ct = hex(concat!(
        "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282fafb69da92728b",
        "1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc",
        "3ff4def08e4b7a9de576d26586cec64b6116"
    ));
    let k = p.aead_key(Aead::ChaCha20Poly1305, &key).unwrap();
    let mut buf = plain.to_vec();
    let tag = p.seal(&k, &nonce, &aad, &mut buf).unwrap();
    assert_eq!(buf, ct);
    assert_eq!(tag, arr::<16>("1ae10b594f09e26a7e902ecbd0600691"));
    p.open(&k, &nonce, &aad, &mut buf, &tag).unwrap();
    assert_eq!(buf, plain);
}

#[test]
fn aes_128_gcm_nist_vectors() {
    let p = Software;
    // The GCM specification's test cases 1 and 4 (AES-128).
    let k = p.aead_key(Aead::Aes128Gcm, &[0; 16]).unwrap();
    let mut empty: [u8; 0] = [];
    let tag = p.seal(&k, &[0; 12], &[], &mut empty).unwrap();
    assert_eq!(tag, arr::<16>("58e2fccefa7e3061367f1d57a4e7455a"));

    let key = hex("feffe9928665731c6d6a8f9467308308");
    let nonce = arr::<12>("cafebabefacedbaddecaf888");
    let aad = hex("feedfacedeadbeeffeedfacedeadbeefabaddad2");
    let plain = hex(concat!(
        "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a72",
        "1c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39"
    ));
    let ct = hex(concat!(
        "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e",
        "21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091"
    ));
    let k = p.aead_key(Aead::Aes128Gcm, &key).unwrap();
    let mut buf = plain.clone();
    let tag = p.seal(&k, &nonce, &aad, &mut buf).unwrap();
    assert_eq!(buf, ct);
    assert_eq!(tag, arr::<16>("5bc94fbc3221a5db94fae95ae7121a47"));
    p.open(&k, &nonce, &aad, &mut buf, &tag).unwrap();
    assert_eq!(buf, plain);
}

#[test]
fn header_protection_rfc9001_appendix_a() {
    let p = Software;
    // A.2: the client Initial packet, AES.
    let aes = p
        .hp_key(Aead::Aes128Gcm, &hex("9f50449e04a0e810283a1e9933adedd2"))
        .unwrap();
    assert_eq!(
        p.hp_mask(&aes, &arr("d1b1c98dd7689fb8ec11d242b123dc9b")),
        arr::<5>("437b9aec36")
    );
    // A.5: the ChaCha20-Poly1305 short header packet.
    let cc = p
        .hp_key(
            Aead::ChaCha20Poly1305,
            &hex("25a282b9e82f06f21f488917a4fc8f1b73573685608597d0efcb076b0ab7a7a4"),
        )
        .unwrap();
    assert_eq!(
        p.hp_mask(&cc, &arr("5e5cd55c41f69080575d7999c25a5bfb")),
        arr::<5>("aefefe7d03")
    );
}

/// The mask for the last counter of the 32-bit block counter is block 2^32 - 1 of the stream, not a zero mask. The
/// expected bytes come from the `OpenSSL` implementation of `ChaCha20` (counter and nonce as its 16-byte IV) for the key 0..31 and the nonce
/// 100..111.
#[test]
fn header_protection_chacha20_counter_edges() {
    let p = Software;
    let key: Vec<u8> = (0..32).collect();
    let cc = p.hp_key(Aead::ChaCha20Poly1305, &key).unwrap();
    let sample = |counter: u32| -> [u8; 16] {
        let mut s = [0u8; 16];
        s[..4].copy_from_slice(&counter.to_le_bytes());
        for (i, b) in s[4..].iter_mut().enumerate() {
            *b = 100 + i as u8;
        }
        s
    };
    assert_eq!(p.hp_mask(&cc, &sample(u32::MAX)), [175, 16, 59, 203, 205]);
    assert_eq!(p.hp_mask(&cc, &sample(u32::MAX - 1)), [183, 54, 238, 111, 28]);
}

#[test]
fn key_lengths_are_checked() {
    let p = Software;
    for alg in ALGS {
        for len in [0, 1, alg.key_len() - 1, alg.key_len() + 1, 64] {
            let key = vec![0u8; len];
            assert_eq!(p.aead_key(alg, &key).unwrap_err(), CryptoError::InvalidLength);
            assert_eq!(p.hp_key(alg, &key).unwrap_err(), CryptoError::InvalidLength);
        }
    }
}

#[test]
fn tampering_is_rejected_and_leaves_the_ciphertext() {
    let p = Software;
    let mut rng = SplitMix64::new(1);
    for alg in ALGS {
        let key = key_for(alg, &mut rng);
        let k = p.aead_key(alg, &key).unwrap();
        let nonce = [9u8; 12];
        let aad = b"header".to_vec();
        let plain = b"attack at dawn, bring the long ladder".to_vec();
        let mut ct = plain.clone();
        let tag = p.seal(&k, &nonce, &aad, &mut ct).unwrap();
        assert_ne!(ct, plain);

        let try_open =
            |key: &<Software as Provider>::AeadKey, nonce: &[u8; 12], aad: &[u8], ct: &[u8], tag: &[u8; 16]| {
                let mut buf = ct.to_vec();
                let r = p.open(key, nonce, aad, &mut buf, tag);
                if r.is_err() {
                    assert_eq!(buf, ct, "a failed open must not release plaintext");
                }
                r
            };
        assert_eq!(try_open(&k, &nonce, &aad, &ct, &tag), Ok(()));
        for i in 0..ct.len() {
            let mut bad = ct.clone();
            bad[i] ^= 1;
            assert_eq!(
                try_open(&k, &nonce, &aad, &bad, &tag),
                Err(CryptoError::Authentication),
                "ct byte {i}"
            );
        }
        for i in 0..16 {
            let mut bad = tag;
            bad[i] ^= 0x80;
            assert_eq!(
                try_open(&k, &nonce, &aad, &ct, &bad),
                Err(CryptoError::Authentication),
                "tag byte {i}"
            );
        }
        assert_eq!(
            try_open(&k, &nonce, b"headeR", &ct, &tag),
            Err(CryptoError::Authentication)
        );
        assert_eq!(try_open(&k, &nonce, b"", &ct, &tag), Err(CryptoError::Authentication));
        let mut other_nonce = nonce;
        other_nonce[11] ^= 1;
        assert_eq!(
            try_open(&k, &other_nonce, &aad, &ct, &tag),
            Err(CryptoError::Authentication)
        );
        let mut wrong = key.clone();
        wrong[0] ^= 1;
        let wk = p.aead_key(alg, &wrong).unwrap();
        assert_eq!(try_open(&wk, &nonce, &aad, &ct, &tag), Err(CryptoError::Authentication));
    }
}

#[test]
fn round_trip_at_every_length_up_to_2048() {
    let p = Software;
    let mut rng = SplitMix64::new(2);
    for alg in ALGS {
        let key = key_for(alg, &mut rng);
        let k = p.aead_key(alg, &key).unwrap();
        for len in 0..=2048usize {
            let mut plain = vec![0u8; len];
            rng.fill(&mut plain);
            let mut aad = vec![0u8; len % 37];
            rng.fill(&mut aad);
            let mut nonce = [0u8; 12];
            rng.fill(&mut nonce);
            let mut buf = plain.clone();
            let tag = p.seal(&k, &nonce, &aad, &mut buf).unwrap();
            p.open(&k, &nonce, &aad, &mut buf, &tag).unwrap();
            assert_eq!(buf, plain, "{alg:?} length {len}");
        }
    }
}

proptest! {
    #[test]
    fn seal_open_round_trip(
        plain in prop::collection::vec(any::<u8>(), 0..4096),
        aad in prop::collection::vec(any::<u8>(), 0..64),
        nonce in any::<[u8; 12]>(),
        key in any::<[u8; 32]>(),
        which in 0usize..2,
    ) {
        let p = Software;
        let alg = ALGS[which];
        let k = p.aead_key(alg, &key[..alg.key_len()]).unwrap();
        let mut buf = plain.clone();
        let tag = p.seal(&k, &nonce, &aad, &mut buf).unwrap();
        p.open(&k, &nonce, &aad, &mut buf, &tag).unwrap();
        prop_assert_eq!(buf, plain);
    }
}

#[test]
fn capabilities_match_the_cpu() {
    let caps = Software.capabilities();
    #[cfg(target_arch = "x86_64")]
    assert_eq!(
        caps.aes_gcm_hw,
        is_x86_feature_detected!("aes") && is_x86_feature_detected!("pclmulqdq")
    );
    #[cfg(target_arch = "x86_64")]
    assert!(caps.chacha20_simd, "SSE2 is part of the x86_64 baseline");
    let _ = caps;
}

#[test]
fn provider_operations_do_not_allocate() {
    let p = Software;
    for alg in ALGS {
        let key = vec![5u8; alg.key_len()];
        let k = p.aead_key(alg, &key).unwrap();
        let hp = p.hp_key(alg, &key).unwrap();
        let mut buf = [3u8; 1200];
        let mut tag = [0u8; 16];
        let mut mask = [0u8; 5];
        let stats = pinc_tests::measure(|| {
            tag = p.seal(&k, &[1; 12], b"aad", &mut buf).unwrap();
            p.open(&k, &[1; 12], b"aad", &mut buf, &tag).unwrap();
            mask = p.hp_mask(&hp, &[2; 16]);
        });
        assert_eq!(stats.count(), 0, "{alg:?} allocated {stats:?}");
        assert_eq!(buf, [3u8; 1200]);
        let _ = (tag, mask);
    }
    let secret = p.x25519_secret(&[8; 32]);
    let peer = p.x25519_public(&p.x25519_secret(&[9; 32]));
    let mut digest = [0u8; 32];
    let stats = pinc_tests::measure(|| {
        let _ = p.x25519_dh(&secret, &peer).unwrap();
        let _ = p.x25519_public(&secret);
        digest = p.sha256(b"abc");
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
    assert_ne!(digest, [0; 32]);
}
