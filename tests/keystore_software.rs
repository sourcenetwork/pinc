//! Tests of `SoftwareStore`: signing for every identity algorithm, ML-KEM decapsulation, sealing and randomness.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use pinc_crypto::identity::verify;
use pinc_crypto::{CryptoError, IdentityAlg, Keypair, NodeId, Provider, Software};
use pinc_keystore::{KeyStore, KeyStoreError, SoftwareStore};

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

/// A store whose every random byte comes from `entropy`: no operating system involved.
fn seeded(byte: u8) -> SoftwareStore {
    SoftwareStore::from_entropy([byte; 32])
}

#[test]
fn from_entropy_signs_and_verifies() {
    big(|| {
        let mut store = seeded(1);
        for alg in ALGS {
            let key = store.generate(alg).unwrap();
            let (_, pk) = store.public(&key).unwrap();
            let sig = store.sign(&key, b"entropy given by the host").unwrap();
            verify(alg, &pk, b"entropy given by the host", sig.as_bytes()).unwrap();
            assert_eq!(
                verify(alg, &pk, b"another message", sig.as_bytes()),
                Err(CryptoError::InvalidSignature)
            );
        }
    });
}

#[test]
fn from_entropy_kem_round_trips() {
    let mut store = seeded(2);
    let (key, ek) = store.generate_kem().unwrap();
    let ek = Software.kem_encaps_key(&ek).unwrap();
    let (ct, shared) = Software.kem_encapsulate(&ek, &[9; 32]).unwrap();
    assert_eq!(
        store.decapsulate(&key, &Software.kem_ciphertext_bytes(&ct)).unwrap(),
        shared
    );
}

#[test]
fn from_entropy_seals_and_unseals() {
    let mut store = seeded(3);
    let sealed = store.seal(b"ticket").unwrap();
    assert_eq!(store.unseal(&sealed).unwrap().as_slice(), b"ticket");
    // The nonce is drawn from the generator, so sealing twice differs.
    assert_ne!(store.seal(b"ticket").unwrap(), sealed);
    let mut tampered = sealed.clone();
    tampered[sealed.len() - 1] ^= 1;
    assert_eq!(store.unseal(&tampered), Err(KeyStoreError::InvalidSealed));
    // The sealing key follows the entropy: another seed cannot unseal, the same seed can.
    assert_eq!(seeded(4).unseal(&sealed), Err(KeyStoreError::InvalidSealed));
    assert_eq!(seeded(3).unseal(&sealed).unwrap().as_slice(), b"ticket");
}

#[test]
fn from_entropy_kem_key_follows_the_entropy() {
    let first = seeded(5).generate_kem().unwrap().1;
    assert_eq!(first, seeded(5).generate_kem().unwrap().1);
    assert_ne!(first, seeded(6).generate_kem().unwrap().1);
}

#[test]
fn from_entropy_draws_differ() {
    let mut store = seeded(7);
    let (mut a, mut b) = ([0u8; 32], [0u8; 32]);
    store.random(&mut a).unwrap();
    store.random(&mut b).unwrap();
    assert_ne!(a, b);
    assert_ne!(a, [0; 32]);
}

#[test]
fn reseed_diverges_two_stores_of_one_entropy() {
    let (mut a, mut b) = (seeded(8), seeded(8));
    let (mut x, mut y) = ([0u8; 32], [0u8; 32]);
    a.random(&mut x).unwrap();
    b.random(&mut y).unwrap();
    assert_eq!(x, y);
    a.reseed(&[1; 32]);
    b.reseed(&[2; 32]);
    a.random(&mut x).unwrap();
    b.random(&mut y).unwrap();
    assert_ne!(x, y);
}

#[test]
fn reseed_with_equal_entropy_keeps_stores_in_step() {
    let (mut a, mut b) = (seeded(9), seeded(9));
    a.reseed(&[3; 32]);
    b.reseed(&[3; 32]);
    let (mut x, mut y) = ([0u8; 32], [0u8; 32]);
    a.random(&mut x).unwrap();
    b.random(&mut y).unwrap();
    assert_eq!(x, y);
}

#[test]
fn os_random_fills_and_differs() {
    let (mut a, mut b) = ([0u8; 32], [0u8; 32]);
    pinc_keystore::os_random(&mut a).unwrap();
    pinc_keystore::os_random(&mut b).unwrap();
    assert_ne!(a, b);
    assert_ne!(a, [0; 32]);
}

/// The 32 bytes the next draw of `store` gives.
fn next_draw(store: &mut SoftwareStore) -> [u8; 32] {
    let mut out = [0u8; 32];
    store.random(&mut out).unwrap();
    out
}

#[test]
fn refresh_changes_what_a_generator_store_gives_next() {
    let (mut plain, mut a, mut b) = (seeded(7), seeded(7), seeded(7));
    a.refresh(&mut |out| {
        *out = [1; 32];
        true
    });
    b.refresh(&mut |out| {
        *out = [1; 32];
        true
    });
    let plain = next_draw(&mut plain);
    assert_ne!(next_draw(&mut a), plain, "the refreshed store left its stream");
    assert_eq!(
        next_draw(&mut seeded_refreshed(1)),
        next_draw(&mut b),
        "the same bytes agree"
    );
    // A refusal mixes nothing in.
    let mut c = seeded(7);
    c.refresh(&mut |_| false);
    assert_eq!(next_draw(&mut c), plain);
}

fn seeded_refreshed(fresh: u8) -> SoftwareStore {
    let mut s = seeded(7);
    s.refresh(&mut |out| {
        *out = [fresh; 32];
        true
    });
    s
}

#[test]
fn refresh_never_asks_for_bytes_for_an_operating_system_store() {
    let mut store = SoftwareStore::new().unwrap();
    let mut calls = 0;
    store.refresh(&mut |_| {
        calls += 1;
        true
    });
    assert_eq!(calls, 0);
}
