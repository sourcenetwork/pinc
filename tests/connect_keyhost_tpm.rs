//! The same exercise with the identity key in a TPM (a software TPM, `swtpm`): the node can publish its record and
//! send its sleep notice with the key never leaving the TPM. Needs the `hwenc` feature.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod connect_common;
mod connect_keyhost_common;

use vinc_crypto::IdentityAlg;
use vinc_keystore::{KeyHost, TpmConfig};
use vinc_tests::Swtpm;

#[test]
fn a_tpm_signs_the_handshake_the_record_the_notice_and_the_beacon() {
    connect_common::big_stack(|| {
        let tpm = Swtpm::start();
        let mut store = tpm.open(TpmConfig::new());
        let key = store.generate(IdentityAlg::EcdsaP256).unwrap();
        connect_keyhost_common::exercise(KeyHost::new(store), key);
    });
}
