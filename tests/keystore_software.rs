//! Tests of `SoftwareStore`: signing for every identity algorithm, ML-KEM decapsulation, sealing and randomness.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use vinc_crypto::identity::verify;
use vinc_crypto::{CryptoError, IdentityAlg, Keypair, NodeId, Provider, Software};
use vinc_keystore::{KeyStore, KeyStoreError, SoftwareStore};

const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

/// ML-DSA keys are large; run on a thread with room, as the crypto tests do.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(16 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn sign_verifies_for_every_algorithm() {
    big(|| {
        let mut store = SoftwareStore::new().unwrap();
        for alg in ALGS {
            let key = store.generate(alg).unwrap();
            let (got_alg, pk) = store.public(&key).unwrap();
            assert_eq!(got_alg, alg);
            assert_eq!(pk.len(), alg.public_key_len());
            let msg = format!("message for {alg:?}");
            let sig = store.sign(&key, msg.as_bytes()).unwrap();
            assert_eq!(sig.alg(), alg);
            assert_eq!(sig.as_bytes().len(), alg.signature_len());
            verify(alg, &pk, msg.as_bytes(), sig.as_bytes()).unwrap();
            assert_eq!(
                verify(alg, &pk, b"another message", sig.as_bytes()),
                Err(CryptoError::InvalidSignature)
            );
            assert_eq!(store.node_id(&key).unwrap(), NodeId::from_public(alg, &pk).unwrap());
        }
    });
}

#[test]
fn inserted_keypair_matches_its_own_signature() {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7; 32]).unwrap();
    let mut pk = [0u8; 32];
    kp.public_key(&mut pk).unwrap();
    let mut store = SoftwareStore::new().unwrap();
    let key = store.insert(kp);
    assert_eq!(store.public(&key).unwrap().1, pk);
}

#[test]
fn decapsulate_matches_encapsulate() {
    let mut store = SoftwareStore::new().unwrap();
    let (key, ek) = store.generate_kem().unwrap();
    let ek = Software.kem_encaps_key(&ek).unwrap();
    let (ct, shared) = Software.kem_encapsulate(&ek, &[9; 32]).unwrap();
    let got = store.decapsulate(&key, &Software.kem_ciphertext_bytes(&ct)).unwrap();
    assert_eq!(got, shared);
    // A forged ciphertext still decapsulates (implicit rejection) but to a different secret.
    let mut forged = Software.kem_ciphertext_bytes(&ct);
    forged[0] ^= 1;
    assert_ne!(store.decapsulate(&key, &forged).unwrap(), shared);
    assert_eq!(
        store.decapsulate(&key, &forged[..10]),
        Err(KeyStoreError::Crypto(CryptoError::InvalidLength))
    );
}

#[test]
fn key_kinds_and_handles_are_checked() {
    let mut store = SoftwareStore::new().unwrap();
    let id = store.generate(IdentityAlg::Ed25519).unwrap();
    let (kem, _) = store.generate_kem().unwrap();
    assert_eq!(store.sign(&kem, b"x"), Err(KeyStoreError::WrongKeyKind));
    assert_eq!(store.decapsulate(&id, &[0; 1088]), Err(KeyStoreError::WrongKeyKind));
    let mut other = SoftwareStore::new().unwrap();
    assert_eq!(other.sign(&id, b"x"), Err(KeyStoreError::UnknownKey));
    assert!(store.remove(&id));
    assert!(!store.remove(&id));
    assert_eq!(store.sign(&id, b"x"), Err(KeyStoreError::UnknownKey));
}

#[test]
fn seal_unseal_round_trip_and_tamper() {
    let mut store = SoftwareStore::new().unwrap();
    for plaintext in [&b""[..], b"ticket", &[0xA5; 4000]] {
        let sealed = store.seal(plaintext).unwrap();
        assert!(sealed.len() > plaintext.len());
        assert_eq!(store.unseal(&sealed).unwrap().as_slice(), plaintext);
        // Sealing twice gives different bytes (random nonce).
        assert_ne!(store.seal(plaintext).unwrap(), sealed);
        for i in 0..sealed.len() {
            let mut bad = sealed.clone();
            bad[i] ^= 0x01;
            assert_eq!(store.unseal(&bad), Err(KeyStoreError::InvalidSealed), "byte {i}");
        }
        for n in 0..sealed.len().min(40) {
            assert_eq!(store.unseal(&sealed[..n]), Err(KeyStoreError::InvalidSealed), "len {n}");
        }
    }
    // Another store has another sealing key.
    let sealed = store.seal(b"ticket").unwrap();
    let mut other = SoftwareStore::new().unwrap();
    assert_eq!(other.unseal(&sealed), Err(KeyStoreError::InvalidSealed));
}

#[test]
fn random_is_not_constant() {
    let mut store = SoftwareStore::new().unwrap();
    let (mut a, mut b) = ([0u8; 32], [0u8; 32]);
    store.random(&mut a).unwrap();
    store.random(&mut b).unwrap();
    assert_ne!(a, b);
    assert_ne!(a, [0; 32]);
    store.random(&mut []).unwrap();
}

#[test]
fn errors_are_short_and_carry_no_key_material() {
    for e in [
        KeyStoreError::UnknownKey,
        KeyStoreError::WrongKeyKind,
        KeyStoreError::Unsupported,
        KeyStoreError::Entropy,
        KeyStoreError::InvalidSealed,
        KeyStoreError::Crypto(CryptoError::HighS),
    ] {
        let msg = e.to_string();
        assert!(
            msg.len() < 100 && !msg.ends_with('.') && !msg.contains('\u{2014}'),
            "{msg}"
        );
    }
}
