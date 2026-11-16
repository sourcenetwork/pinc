//! The keys of the hash tables are drawn from the identity's key store when an endpoint is assembled, and a draw that is
//! not usable builds no endpoint.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use alloc::vec::Vec;

use vinc_crypto::IdentityAlg;
use vinc_keystore::{KeyHandle, KeyStore, SoftwareStore};

use super::{Builder, Vinc};
use crate::error::ErrorKind;
use crate::keys::Identity;

/// A key store whose randomness is fixed bytes, for the draw of the hash tables' keys.
struct Fixed(SoftwareStore, [u8; 64]);

impl KeyStore for Fixed {
    fn sign(&mut self, key: &KeyHandle, msg: &[u8]) -> vinc_keystore::Result<vinc_keystore::Signature> {
        self.0.sign(key, msg)
    }

    fn public(&self, key: &KeyHandle) -> vinc_keystore::Result<(IdentityAlg, Vec<u8>)> {
        self.0.public(key)
    }

    fn decapsulate(&mut self, key: &KeyHandle, ct: &[u8]) -> vinc_keystore::Result<vinc_crypto::Secret<32>> {
        self.0.decapsulate(key, ct)
    }

    fn random(&mut self, out: &mut [u8]) -> vinc_keystore::Result<()> {
        if out.len() == self.1.len() {
            out.copy_from_slice(&self.1);
            Ok(())
        } else {
            self.0.random(out)
        }
    }

    fn seal(&mut self, plaintext: &[u8]) -> vinc_keystore::Result<Vec<u8>> {
        self.0.seal(plaintext)
    }

    fn unseal(&mut self, sealed: &[u8]) -> vinc_keystore::Result<zeroize::Zeroizing<Vec<u8>>> {
        self.0.unseal(sealed)
    }
}

fn fixed(secrets: [u64; 7]) -> Builder<Fixed> {
    let mut bytes = [0u8; 64];
    bytes[..8].copy_from_slice(&1u64.to_le_bytes());
    for (i, w) in secrets.iter().enumerate() {
        bytes[8 + i * 8..16 + i * 8].copy_from_slice(&w.to_le_bytes());
    }
    let mut store = SoftwareStore::from_entropy([4; 32]);
    let handle = store.insert(vinc_crypto::Keypair::from_seed(IdentityAlg::Ed25519, &[5; 32]).unwrap());
    Vinc::builder().identity(Identity::from_store(Fixed(store, bytes), handle).unwrap())
}

const UNUSABLE: &str = "the key store's randomness is not usable";

#[test]
fn a_key_store_that_draws_a_zero_or_a_repeated_secret_builds_no_endpoint() {
    for secrets in [[1, 2, 3, 0, 5, 6, 7], [4, 2, 3, 4, 5, 6, 7]] {
        let e = fixed(secrets).assemble(1).err().unwrap();
        assert_eq!((e.kind(), e.message()), (ErrorKind::Config, UNUSABLE));
    }
    // A usable draw passes this check; a store the broadcast layer cannot sign with is refused for its own reason.
    let built = fixed([1, 2, 3, 4, 5, 6, 7]).assemble(1);
    assert!(built.err().is_none_or(|e| e.message() != UNUSABLE));
}
