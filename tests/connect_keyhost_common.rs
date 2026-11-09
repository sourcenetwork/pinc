//! A node whose identity key lives in a key store answers every signature of the connectivity layer through
//! `KeyHost`: the carrier handshake, the published record, the sleep notice and the beacon. Shared by the software
//! store test and the TPM test.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names
)]

use vinc_connect::client::Io;
use vinc_connect::local::Beacon;
use vinc_connect::record::Record;
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::{NodeState, Trace, sleep};
use vinc_crypto::{Drbg, Software};
use vinc_keystore::{KeyHandle, KeyHost, KeyStore};
use vinc_security::{
    Env, KeyHandle as SecHandle, KeyRequest, KeyResponse, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys,
};
use vinc_tests::Host;

use crate::connect_common::SEC;
use crate::connect_rig::{Ans, Custody, Rig};

/// The node's key custody: signatures from the key store through `KeyHost`, prekey decapsulation from the software
/// prekeys (a TPM holds no ML-KEM key).
struct Keys<S: KeyStore> {
    host: KeyHost<S>,
    prekeys: SoftPrekeys<Software>,
    drbg: Drbg,
}

impl<S: KeyStore> Custody for Keys<S> {
    fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans {
        match req {
            KeyRequest::Sign { .. } => match self.host.answer(req) {
                KeyResponse::Signature(s) => Ans::Sig(s.to_vec()),
                other => panic!("the host did not sign: {other:?}"),
            },
            KeyRequest::Decapsulate { .. } => {
                let soft = SoftKeys::<Software> {
                    signer: None,
                    prekeys: Some(&self.prekeys),
                };
                let mut env = Env {
                    provider: &Software,
                    now,
                    drbg: &mut self.drbg,
                };
                let mut sig = [0u8; vinc_crypto::identity::MAX_SIGNATURE_LEN];
                match soft.answer(&mut env, req, &mut sig) {
                    KeyResponse::SharedSecret(s) => Ans::Secret(s),
                    other => panic!("the prekeys did not decapsulate: {other:?}"),
                }
            }
        }
    }
}

/// Run the whole exercise with the identity key `key` of the store behind `host`.
pub fn exercise<S: KeyStore>(mut host: KeyHost<S>, key: KeyHandle) {
    let (alg, pk) = host.store().public(&key).unwrap();
    host.bind(SecHandle(1), key);
    let identity = LocalIdentity::new(alg, &pk, SecHandle(1)).unwrap();
    let me = identity.node_id();
    let mut now = 1000 * SEC;
    let mut drbg = Drbg::new(&[0x61; 32]);
    let mut env = Env {
        provider: &Software,
        now,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let mut keys = Keys {
        host,
        prekeys,
        drbg: Drbg::new(&[0x64; 32]),
    };
    let mut rig = Rig::new(identity, prekey);
    let (relay_id, udp) = (rig.relay_id, rig.udp);
    let wall = |now: u64| now / 1_000_000;
    let mut answered = 0;

    // Address discovery and the carrier handshake: every key operation of the handshake is answered by the host.
    now = rig.bring_up(&mut keys, now, &mut answered);
    assert!(answered >= 1, "the handshake asked the host to sign");
    assert_eq!(rig.relay.node_state(&me), NodeState::Open);

    // The record: the layer asks for a signature, the host answers, the relay stores a record that verifies.
    now += SEC;
    {
        let mut env = rig.env(now);
        // tick borrows the layer, so the environment is rebuilt from the rig's pieces
        let _ = &mut env;
    }
    {
        let Rig { conn, drbg, .. } = &mut rig;
        let mut env = Env {
            provider: &Software,
            now,
            drbg,
        };
        conn.tick(now, &mut env, Some(wall(now)));
    }
    for _ in 0..20 {
        rig.shuttle(&mut keys, now, &mut answered);
        if rig.relay.record_count() == 1 {
            break;
        }
    }
    assert_eq!(rig.relay.record_count(), 1, "the published record was stored");
    let bytes = rig.relay.lookup(now, &me).expect("the record").to_vec();
    let rec = Record::parse_verified(&bytes).unwrap();
    assert_eq!(rec.node, me);
    assert_eq!(rec.home, relay_id);
    let signed_for_record = answered;

    // The beacon: signed by the host too.
    let mut node = Host::new(0x66, "192.168.1.2:4433".parse().unwrap(), now);
    {
        let Rig { conn, drbg, .. } = &mut rig;
        let mut env = Env {
            provider: &Software,
            now,
            drbg,
        };
        conn.drive(now, &mut *node.ep, &mut env, Some(wall(now)));
    }
    rig.shuttle(&mut keys, now, &mut answered);
    let mut buf = vec![0u8; 2048];
    let mut beacon = None;
    let mut others = Vec::new();
    while let Some((to, n)) = rig.conn.poll_udp(&mut buf) {
        if to.port() == vinc_connect::local::PORT {
            beacon = Some(buf[..n].to_vec());
        } else {
            others.push((to, buf[..n].to_vec()));
        }
    }
    let b = beacon.expect("a beacon");
    assert_eq!(Beacon::parse_verified(&b).unwrap().node, me);
    assert!(answered > signed_for_record, "the beacon was signed by the host");

    // The sleep notice: signed by the host, accepted by the relay, then the carrier closes.
    now += SEC;
    rig.conn.suspend(now, wall(now));
    rig.shuttle(&mut keys, now, &mut answered);
    let mut notices = Vec::new();
    while let Some((to, n)) = rig.conn.poll_udp(&mut buf) {
        if to == udp {
            notices.push(buf[..n].to_vec());
        }
    }
    assert_eq!(notices.len(), 2, "the notice leaves twice");
    for d in &notices {
        let Ok(Datagram::Sleep { notice }) = Datagram::decode(d) else {
            panic!("not a sleep datagram")
        };
        sleep::Notice::parse(notice).unwrap().verify(&relay_id).unwrap();
    }
    let src = "198.51.100.5:20000".parse().unwrap();
    rig.relay.datagram(now, src, None, &notices[0], &mut rig.sink).unwrap();
    assert!(rig.traces().contains(&Trace::SleepAccepted { node: me }));
    now += 2;
    {
        let Rig { conn, drbg, .. } = &mut rig;
        let mut env = Env {
            provider: &Software,
            now,
            drbg,
        };
        conn.tick(now, &mut env, Some(wall(now)));
    }
    assert!(matches!(rig.conn.poll_io(), Some(Io::Close { relay: 0 })));
    let _ = others;
}
