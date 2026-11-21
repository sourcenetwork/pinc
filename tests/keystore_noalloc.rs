//! The software key store allocates nothing on the operations that touch no output buffer of their own: prekey
//! decapsulation, random bytes, and the `KeyHost` path that answers the handshake's decapsulation request, each called
//! after the store and its keys exist. Signing, sealing and unsealing return owned buffers and are not in this test.
#![allow(clippy::unwrap_used, clippy::panic)]

use std::hint::black_box;

use pinc_crypto::{Provider, Software};
use pinc_keystore::{KeyHost, KeyStore, SoftwareStore};
use pinc_security::{KeyHandle as SecHandle, KeyRequest, KeyResponse};
use pinc_tests::measure;

pinc_tests::install_counting_allocator!();

const CALLS: u64 = 64;

fn prekey(
    store: &mut SoftwareStore,
) -> (
    pinc_keystore::KeyHandle,
    [u8; pinc_crypto::provider::KEM_CIPHERTEXT_LEN],
) {
    let (kem, ek) = store.generate_kem().unwrap();
    let ek = Software.kem_encaps_key(&ek).unwrap();
    let (ct, _) = Software.kem_encapsulate(&ek, &[3; 32]).unwrap();
    (kem, Software.kem_ciphertext_bytes(&ct))
}

#[test]
fn decapsulation_and_random_bytes_allocate_nothing() {
    let mut store = SoftwareStore::from_entropy([7; 32]);
    let (kem, ct) = prekey(&mut store);
    let mut buf = [0u8; 32];
    let st = measure(|| {
        for _ in 0..CALLS {
            black_box(store.decapsulate(&kem, &ct).unwrap());
            store.random(black_box(&mut buf)).unwrap();
        }
    });
    assert_eq!(st.count(), 0, "{st:?}");
}

#[test]
fn the_key_host_answers_a_decapsulation_request_without_allocating() {
    let mut store = SoftwareStore::from_entropy([7; 32]);
    let (kem, ct) = prekey(&mut store);
    let mut host = KeyHost::new(store);
    host.bind(SecHandle(1), kem);
    let req = KeyRequest::Decapsulate {
        key: SecHandle(1),
        ct: &ct,
    };
    let st = measure(|| {
        for _ in 0..CALLS {
            assert!(matches!(host.answer(&req), KeyResponse::SharedSecret(_)));
        }
    });
    assert_eq!(st.count(), 0, "{st:?}");
}
