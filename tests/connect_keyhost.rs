//! The connectivity layer with its identity key in the software key store, answered through `KeyHost`: the carrier
//! handshake, the published record, the sleep notice and the beacon.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod connect_common;
mod connect_keyhost_common;
mod connect_rig;

use vinc_crypto::IdentityAlg;
use vinc_keystore::{KeyHost, SoftwareStore};

#[test]
fn a_software_store_signs_the_handshake_the_record_the_notice_and_the_beacon() {
    connect_common::big_stack(|| {
        for alg in [IdentityAlg::Ed25519, IdentityAlg::EcdsaP256] {
            let mut store = SoftwareStore::new().unwrap();
            let key = store.generate(alg).unwrap();
            connect_keyhost_common::exercise(KeyHost::new(store), key);
        }
    });
}
