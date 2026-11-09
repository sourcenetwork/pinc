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

#[test]
fn a_refused_or_malformed_signature_is_reported_and_asked_again_never_published() {
    use connect_common::SEC;
    use connect_rig::{Ans, Custody, Rig};
    use vinc_connect::client::Notice;
    use vinc_crypto::{Drbg, Software};
    use vinc_security::{
        Env, KeyHandle as SecHandle, KeyRequest, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys,
    };

    struct Keys(KeyHost<SoftwareStore>, SoftPrekeys<Software>, Drbg);
    impl Custody for Keys {
        fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans {
            match req {
                KeyRequest::Sign { .. } => match self.0.answer(req) {
                    KeyResponse::Signature(s) => Ans::Sig(s.to_vec()),
                    other => panic!("{other:?}"),
                },
                KeyRequest::Decapsulate { .. } => {
                    let soft = SoftKeys::<Software> {
                        signer: None,
                        prekeys: Some(&self.1),
                    };
                    let mut env = Env {
                        provider: &Software,
                        now,
                        drbg: &mut self.2,
                    };
                    match soft.answer(&mut env, req, &mut [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN]) {
                        KeyResponse::SharedSecret(s) => Ans::Secret(s),
                        other => panic!("{other:?}"),
                    }
                }
            }
        }
    }

    connect_common::big_stack(|| {
        let mut store = SoftwareStore::new().unwrap();
        let key = store.generate(IdentityAlg::Ed25519).unwrap();
        let (alg, pk) = vinc_keystore::KeyStore::public(&store, &key).unwrap();
        let mut host = KeyHost::new(store);
        host.bind(SecHandle(1), key);
        let identity = LocalIdentity::new(alg, &pk, SecHandle(1)).unwrap();
        let mut now = 1000 * SEC;
        let mut drbg = Drbg::new(&[0x71; 32]);
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        let prekey = prekeys.acquire(&mut env).unwrap();
        let mut keys = Keys(host, prekeys, Drbg::new(&[0x72; 32]));
        let mut rig = Rig::new(&identity, prekey);
        let mut answered = 0;
        now = rig.bring_up(&mut keys, now, &mut answered);
        while rig.conn.poll_notice().is_some() {}
        let tick = |rig: &mut Rig, now: u64| {
            let Rig { conn, drbg, .. } = rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.tick(now, &mut env, Some(now / 1_000_000));
        };
        // The key refuses: reported, nothing published.
        now += SEC;
        tick(&mut rig, now);
        assert!(rig.conn.sign_request().is_some(), "the record wants a signature");
        rig.conn.sign_response(now, vinc_security::KeyResponse::Failed);
        assert_eq!(rig.conn.poll_notice(), Some(Notice::SignFailed));
        assert!(rig.conn.sign_request().is_none());
        rig.shuttle(&mut keys, now, &mut answered);
        assert_eq!(rig.relay.record_count(), 0);
        // A signature of the wrong length is refused too, and never sent.
        now += 3 * SEC;
        tick(&mut rig, now);
        assert!(rig.conn.sign_request().is_some(), "asked again after the retry wait");
        rig.conn
            .sign_response(now, vinc_security::KeyResponse::Signature(&[1, 2, 3]));
        assert_eq!(rig.conn.poll_notice(), Some(Notice::SignFailed));
        rig.shuttle(&mut keys, now, &mut answered);
        assert_eq!(rig.relay.record_count(), 0);
        // The host answers properly the third time.
        now += 3 * SEC;
        tick(&mut rig, now);
        for _ in 0..10 {
            rig.shuttle(&mut keys, now, &mut answered);
        }
        assert_eq!(rig.relay.record_count(), 1);
    });
}
