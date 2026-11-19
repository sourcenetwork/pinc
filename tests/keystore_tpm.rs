//! Tests of `TpmStore` against a software TPM (`swtpm`, package `swtpm`); see `pinc_tests::Swtpm`.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use pinc_crypto::identity::{verify, verify_node};
use pinc_crypto::{CryptoError, IdentityAlg, NodeId, Provider, Software};
use pinc_keystore::tpm::SimTransport;
use pinc_keystore::{KeyHandle, KeyStore, KeyStoreError, TpmConfig, TpmStore};
use pinc_tests::{SplitMix64, Swtpm};

const PERSISTENT_KEY: u32 = 0x8101_0001;
/// The order of the P-256 group, big-endian.
const N: [u8; 32] = [
    0xFF, 0xFF, 0xFF, 0xFF, 0x00, 0x00, 0x00, 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xBC, 0xE6, 0xFA,
    0xAD, 0xA7, 0x17, 0x9E, 0x84, 0xF3, 0xB9, 0xCA, 0xC2, 0xFC, 0x63, 0x25, 0x51,
];

fn messages(seed: u64, count: usize) -> Vec<Vec<u8>> {
    let mut rng = SplitMix64::new(seed);
    (0..count)
        .map(|_| {
            let mut m = vec![0u8; (rng.next_u64() % 300) as usize];
            rng.fill(&mut m);
            m
        })
        .collect()
}

/// `n - s` for a 32-byte big-endian `s` below `n`.
fn negate(s: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    let mut borrow = 0u8;
    for i in (0..32).rev() {
        let (d, b1) = N[i].overflowing_sub(s[i]);
        let (d, b2) = d.overflowing_sub(borrow);
        out[i] = d;
        borrow = u8::from(b1 || b2);
    }
    out
}

/// Whether `err` is a TPM refusal with exactly response code `code`.
fn is_code(err: KeyStoreError, code: u32) -> bool {
    err == KeyStoreError::Tpm { code }
}

/// Whether `err` is a format-1 TPM refusal with error number `error_number`, whatever handle, parameter or session
/// it names.
fn is_rc(err: KeyStoreError, error_number: u32) -> bool {
    matches!(err, KeyStoreError::Tpm { code } if code & 0xBF == 0x80 | error_number)
}

fn new_key(store: &mut TpmStore<SimTransport>) -> KeyHandle {
    store.generate(IdentityAlg::EcdsaP256).unwrap()
}

#[test]
fn get_random_returns_fresh_bytes() {
    let tpm = Swtpm::start();
    let mut store = tpm.open(TpmConfig::new());
    let (mut a, mut b) = ([0u8; 100], [0u8; 100]);
    store.random(&mut a).unwrap();
    store.random(&mut b).unwrap();
    assert_ne!(a, b);
    assert!(a.iter().any(|&x| x != 0));
    let raw = store.client_mut().get_random(16).unwrap();
    assert_eq!(raw.len(), 16);
    store.random(&mut []).unwrap();
}

#[test]
fn create_persist_sign_200_messages_low_s() {
    let tpm = Swtpm::start();
    let config = || TpmConfig::new().key_auth(b"key-auth");
    let mut store = tpm.open(config());
    let key = new_key(&mut store);
    store.persist(&key, PERSISTENT_KEY).unwrap();
    assert_eq!(store.tpm_handle(&key), Some(PERSISTENT_KEY));
    let (alg, pk) = store.public(&key).unwrap();
    assert_eq!((alg, pk.len()), (IdentityAlg::EcdsaP256, 33));

    // Raw TPM signatures: about half have a high s, which pinc_crypto rejects; n - s is the same signature.
    let handle = store.tpm_handle(&key).unwrap();
    let mut high = 0;
    for msg in messages(1, 40) {
        let digest = Software.sha256(&msg);
        let (r, s) = store.client_mut().sign_p256(handle, b"key-auth", &digest).unwrap();
        let mut sig = [r, s].concat();
        match verify(alg, &pk, &msg, &sig) {
            Ok(()) => {}
            Err(CryptoError::HighS) => {
                high += 1;
                sig[32..].copy_from_slice(&negate(&s));
                verify(alg, &pk, &msg, &sig).unwrap();
            }
            Err(e) => panic!("raw TPM signature rejected: {e}"),
        }
    }
    assert!(
        high > 0,
        "40 raw signatures with no high s: the low-s path was not exercised"
    );

    for msg in messages(2, 200) {
        let sig = store.sign(&key, &msg).unwrap();
        assert_eq!(sig.alg(), IdentityAlg::EcdsaP256);
        verify(alg, &pk, &msg, sig.as_bytes()).unwrap();
    }

    // A second store on the same TPM finds the persistent key and signs with it.
    drop(store);
    let mut again = tpm.open(config());
    let loaded = again.load_persistent(PERSISTENT_KEY).unwrap();
    assert_eq!(again.public(&loaded).unwrap().1, pk);
    let sig = again.sign(&loaded, b"after reload").unwrap();
    verify(alg, &pk, b"after reload", sig.as_bytes()).unwrap();

    // The persistent handle is taken now (TPM_RC_NV_DEFINED), and a bad or empty handle is refused.
    let other = new_key(&mut again);
    assert!(
        is_code(again.persist(&other, PERSISTENT_KEY).unwrap_err(), 0x14C),
        "TPM_RC_NV_DEFINED"
    );
    assert_eq!(again.persist(&other, 0x0100_0000), Err(KeyStoreError::InvalidHandle));
    assert_eq!(again.persist(&loaded, 0x8101_0002), Err(KeyStoreError::InvalidHandle));
    let missing = again.load_persistent(0x8100_0099).unwrap_err();
    assert!(
        is_rc(missing, 0x0B) || is_code(missing, 0x910),
        "an empty persistent handle must be refused, got {missing:?}"
    );
}

#[test]
fn public_key_and_node_id_agree_with_pinc_crypto() {
    let tpm = Swtpm::start();
    let mut store = tpm.open(TpmConfig::new());
    let key = new_key(&mut store);
    let handle = store.tpm_handle(&key).unwrap();
    let point = store.client_mut().read_public(handle).unwrap();
    let (alg, pk) = store.public(&key).unwrap();
    // Compressed SEC1: parity of y, then x.
    assert_eq!(pk[0], 2 + (point.y[31] & 1));
    assert_eq!(pk[1..], point.x);
    let id = store.node_id(&key).unwrap();
    assert_eq!(id, NodeId::from_public(alg, &pk).unwrap());
    let sig = store.sign(&key, b"who").unwrap();
    verify_node(&id, &pk, b"who", sig.as_bytes()).unwrap();
    // Two keys, two identities.
    let other = new_key(&mut store);
    assert_ne!(store.node_id(&other).unwrap(), id);
}

#[test]
fn seal_unseal_round_trip_and_wrong_auth() {
    let tpm = Swtpm::start();
    let config = || TpmConfig::new().key_auth(b"right");
    let mut store = tpm.open(config());
    let mut sealed = Vec::new();
    for plaintext in [&b""[..], b"resumption ticket", &[0x5A; 5000]] {
        let blob = store.seal(plaintext).unwrap();
        assert_eq!(store.unseal(&blob).unwrap().as_slice(), plaintext);
        assert_ne!(store.seal(plaintext).unwrap(), blob);
        sealed.push((plaintext, blob));
    }
    let blob = sealed[1].1.clone();

    // Altered ciphertext or tag, a truncated value and garbage are all refused.
    for i in [blob.len() - 1, blob.len() - 20] {
        let mut bad = blob.clone();
        bad[i] ^= 1;
        assert_eq!(store.unseal(&bad), Err(KeyStoreError::InvalidSealed), "byte {i}");
    }
    assert_eq!(store.unseal(&blob[..blob.len() - 1]), Err(KeyStoreError::InvalidSealed));
    assert_eq!(store.unseal(&[]), Err(KeyStoreError::InvalidSealed));
    assert_eq!(store.unseal(&[2, 0, 0]), Err(KeyStoreError::InvalidSealed));
    // Altered wrapped key: the TPM or the envelope refuses it, never a wrong plaintext.
    let mut bad = blob.clone();
    bad[10] ^= 1;
    assert!(store.unseal(&bad).is_err());

    // A later connection with the same auth unseals; a different auth value is refused by the TPM.
    drop(store);
    let mut same = tpm.open(config());
    assert_eq!(same.unseal(&blob).unwrap().as_slice(), b"resumption ticket");
    drop(same);
    let mut wrong = tpm.open(TpmConfig::new().key_auth(b"wrong"));
    let err = wrong.unseal(&blob).unwrap_err();
    assert!(
        is_code(err, 0x98E),
        "wrong auth must be TPM_RC_AUTH_FAIL on session 1, got {err:?}"
    );
}

#[test]
fn unsupported_algorithms_are_typed_errors() {
    let tpm = Swtpm::start();
    let mut store = tpm.open(TpmConfig::new());
    for alg in [IdentityAlg::Ed25519, IdentityAlg::MlDsa65, IdentityAlg::Hybrid] {
        assert_eq!(store.generate(alg), Err(KeyStoreError::Unsupported));
    }
    let key = new_key(&mut store);
    assert_eq!(store.decapsulate(&key, &[0; 1088]), Err(KeyStoreError::Unsupported));
    // A handle from a software store is not known here.
    let mut soft = pinc_keystore::SoftwareStore::new().unwrap();
    let (kem, _) = soft.generate_kem().unwrap();
    assert_eq!(store.decapsulate(&kem, &[0; 1088]), Err(KeyStoreError::Unsupported));
    assert_eq!(store.sign(&kem, b"x"), Err(KeyStoreError::UnknownKey));
}

#[test]
fn tpm_errors_carry_the_response_code() {
    let tpm = Swtpm::start();
    let mut store = tpm.open(TpmConfig::new());
    let key = new_key(&mut store);
    let handle = store.tpm_handle(&key).unwrap();
    store.client_mut().flush_context(handle).unwrap();
    let err = store.sign(&key, b"after flush").unwrap_err();
    assert!(
        is_code(err, 0x910),
        "signing with a flushed handle must be TPM_RC_REFERENCE_H0, got {err:?}"
    );
    let msg = err.to_string();
    assert!(msg.contains("response code") && msg.len() < 100, "{msg}");
    // Too long an auth value is refused before it reaches the TPM.
    let long = TpmConfig::new().key_auth(&[1; 65]);
    assert_eq!(
        TpmStore::connect_simulator(("127.0.0.1", tpm.port), None, long).unwrap_err(),
        KeyStoreError::InvalidAuth
    );
}

#[test]
fn transient_handles_are_flushed_on_drop() {
    // swtpm holds three transient objects; a store that kept its handles would exhaust them by the second round.
    let tpm = Swtpm::start();
    for round in 0..6 {
        let mut store = tpm.open(TpmConfig::new());
        let (a, b) = (new_key(&mut store), new_key(&mut store));
        let sig = store.sign(&a, b"round").unwrap();
        let (alg, pk) = store.public(&a).unwrap();
        verify(alg, &pk, b"round", sig.as_bytes()).unwrap_or_else(|e| panic!("round {round}: {e}"));
        assert_ne!(store.public(&a).unwrap().1, store.public(&b).unwrap().1);
    }
}

#[test]
fn missing_persistent_handle_leaves_the_store_usable() {
    // Loading a persistent handle that holds nothing fails; the store must stay usable afterwards.
    let tpm = Swtpm::start();
    let mut store = tpm.open(TpmConfig::new());
    for _ in 0..6 {
        assert!(store.load_persistent(0x8100_0001).is_err());
    }
    let key = new_key(&mut store);
    store.sign(&key, b"still works").unwrap();
}
