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

use core::net::SocketAddr;

use vinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use vinc_connect::client::{Config, Connectivity, Io, Notice, RelayCfg};
use vinc_connect::local::Beacon;
use vinc_connect::record::Record;
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::sleep;
use vinc_connect::relay::{Relay, Trace};
use vinc_crypto::{Drbg, IdentityAlg, Software};
use vinc_keystore::{KeyHandle, KeyHost, KeyStore};
use vinc_security::{
    ConnId, Env, KeyHandle as SecHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys, SoftPrekeys,
};
use vinc_tests::Host;

use crate::connect_common::{Collect, Rec, SEC, dg, ed, id};

const RELAY_UDP: &str = "203.0.113.10:4433";
const RELAY_TCP: &str = "203.0.113.10:443";

type R = Relay<8, 8, 4, 4096>;

/// The relay and the node, shuttling bytes in memory.
struct Rig {
    conn: Box<Connectivity<Software, 1, 4>>,
    relay: Box<R>,
    rc: Box<ProtectedCarrier<Software>>,
    stores: ResponderStores<2, 2>,
    relay_kp: vinc_crypto::Keypair,
    drbg: Drbg,
    rdrbg: Drbg,
    sink: Collect,
    session: Option<vinc_connect::relay::SessionId>,
    peer: Option<vinc_crypto::NodeId>,
}

/// An answer that owns its bytes.
enum Ans {
    Sig(Vec<u8>),
    Secret(vinc_crypto::Secret<32>),
}

impl Ans {
    fn response(&self) -> vinc_security::KeyResponse<'_> {
        match self {
            Self::Sig(s) => vinc_security::KeyResponse::Signature(s),
            Self::Secret(s) => vinc_security::KeyResponse::SharedSecret(vinc_crypto::Secret::new(*s.expose())),
        }
    }
}

/// The node's key custody: signatures from the key store through `KeyHost`, prekey decapsulation from the software
/// prekeys (a TPM holds no ML-KEM key).
struct Custody<S: KeyStore> {
    host: KeyHost<S>,
    prekeys: SoftPrekeys<Software>,
    drbg: Drbg,
}

impl<S: KeyStore> Custody<S> {
    fn answer(&mut self, now: u64, req: &vinc_security::KeyRequest<'_>) -> Ans {
        match req {
            vinc_security::KeyRequest::Sign { .. } => match self.host.answer(req) {
                vinc_security::KeyResponse::Signature(s) => Ans::Sig(s.to_vec()),
                other => panic!("the host did not sign: {other:?}"),
            },
            vinc_security::KeyRequest::Decapsulate { .. } => {
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
                    vinc_security::KeyResponse::SharedSecret(s) => Ans::Secret(s),
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
    let relay_kp = ed(0x77);
    let relay_id = id(&relay_kp);
    let prov = Software;
    let mut drbg = Drbg::new(&[0x61; 32]);
    let mut env = Env {
        provider: &prov,
        now: 1000 * SEC,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let mut custody = Custody {
        host,
        prekeys,
        drbg: Drbg::new(&[0x64; 32]),
    };
    let host = &mut custody;
    let udp: SocketAddr = RELAY_UDP.parse().unwrap();
    let tcp: SocketAddr = RELAY_TCP.parse().unwrap();
    let mut relays = [None; 1];
    relays[0] = Some(RelayCfg {
        id: relay_id,
        udp: Some(udp),
        tcp: Some(tcp),
        ws: None,
    });
    let cfg = Config {
        me,
        identity,
        relays,
        phone: false,
        restarted: false,
        start: 1000 * SEC,
        v6: false,
        keep_learn: false,
    };
    let mut conn = Box::new(Connectivity::new(cfg, prekey, Software, 7));
    conn.set_local(&["192.168.1.2:4433".parse().unwrap()]);
    let relay = Box::new(R::new(vinc_connect::relay::Config::new(relay_id, 3)));
    let rcfg = session::responder_config(
        LocalIdentity::from_keypair(&relay_kp, SecHandle(1)).unwrap(),
        ConnId::new(b"relay000").unwrap(),
    )
    .unwrap();
    let mut rig = Rig {
        conn,
        relay,
        rc: Box::new(ProtectedCarrier::accept(rcfg)),
        stores: ResponderStores::default(),
        relay_kp,
        drbg: Drbg::new(&[0x62; 32]),
        rdrbg: Drbg::new(&[0x63; 32]),
        sink: Collect::default(),
        session: None,
        peer: None,
    };
    let mut now = 1000 * SEC;
    let wall = |now: u64| now / 1_000_000;

    // Address discovery: a QAD probe, answered by the relay, picks the home and the class.
    {
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut rig.drbg,
        };
        rig.conn.probe_all(now, &mut env);
    }
    let mut buf = vec![0u8; 2048];
    let (to, n) = rig.conn.poll_udp(&mut buf).expect("a probe");
    assert_eq!(to, udp);
    let src: SocketAddr = "198.51.100.5:20000".parse().unwrap();
    rig.relay.datagram(now, src, None, &buf[..n], &mut rig.sink).unwrap();
    let reply = rig
        .sink
        .effects()
        .into_iter()
        .find_map(|r| if let Rec::Udp(_, b) = r { Some(b) } else { None })
        .expect("the relay answers");
    assert!(rig.conn.handle_udp(now, udp, &reply));
    assert_eq!(rig.conn.home(), Some(0));

    // The carrier handshake: the relay dials back nothing; the node opens a stream, and every key operation of
    // its handshake is answered by the host.
    now += SEC;
    {
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut rig.drbg,
        };
        rig.conn.tick(now, &mut env, Some(wall(now)));
    }
    let io = rig.conn.poll_io().expect("a stream request");
    assert!(matches!(io, Io::Open { relay: 0, to, .. } if to == tcp));
    {
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut rig.drbg,
        };
        rig.conn.stream_opened(now, &mut env, 0);
    }
    let mut answered = 0;
    for _ in 0..40 {
        shuttle(&mut rig, host, &prov, now, &mut answered);
        if rig.session.is_some() && rig.conn.carrier_state(0) == vinc_connect::client::link::State::Open {
            break;
        }
    }
    assert_eq!(rig.session.is_some(), true, "the relay authenticated the node");
    assert!(answered >= 1, "the handshake asked the host to sign");
    assert_eq!(rig.relay.node_state(&me), vinc_connect::relay::NodeState::Open);

    // The record: the layer asks for a signature, the host answers, the relay stores a record that verifies.
    now += SEC;
    {
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut rig.drbg,
        };
        rig.conn.tick(now, &mut env, Some(wall(now)));
    }
    for _ in 0..20 {
        shuttle(&mut rig, host, &prov, now, &mut answered);
        if rig.relay.record_count() == 1 {
            break;
        }
    }
    assert_eq!(rig.relay.record_count(), 1, "the published record was stored");
    let bytes = rig.relay.lookup(now, &me).expect("the record").to_vec();
    let rec = Record::parse_verified(&bytes).unwrap();
    assert_eq!(rec.node, me);
    assert_eq!(rec.home, relay_id);
    let signed_by_host = answered;

    // The beacon: signed by the host too.
    let mut node = Host::new(0x66, "192.168.1.2:4433".parse().unwrap(), now);
    {
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut rig.drbg,
        };
        rig.conn.drive(now, &mut *node.ep, &mut env, Some(wall(now)));
    }
    shuttle(&mut rig, host, &prov, now, &mut answered);
    let mut beacon = None;
    while let Some((to, n)) = rig.conn.poll_udp(&mut buf) {
        if to.port() == vinc_connect::local::PORT {
            beacon = Some(buf[..n].to_vec());
        }
    }
    let b = beacon.expect("a beacon");
    assert_eq!(Beacon::parse_verified(&b).unwrap().node, me);
    assert!(answered > signed_by_host, "the beacon was signed by the host");

    // The sleep notice: signed by the host, accepted by the relay, then the carrier closes.
    now += SEC;
    rig.conn.suspend(now, wall(now));
    shuttle(&mut rig, host, &prov, now, &mut answered);
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
    rig.relay.datagram(now, src, None, &notices[0], &mut rig.sink).unwrap();
    assert!(rig.sink.traces().contains(&Trace::SleepAccepted { node: me }));
    now += 2;
    {
        let mut env = Env {
            provider: &prov,
            now,
            drbg: &mut rig.drbg,
        };
        rig.conn.tick(now, &mut env, Some(wall(now)));
    }
    assert!(matches!(rig.conn.poll_io(), Some(Io::Close { relay: 0 })));
    let _ = (Notice::SignFailed, alg == IdentityAlg::Ed25519, dg);
}

/// Move bytes between the node and the relay, and answer the node's key and signature requests from the host.
fn shuttle<S: KeyStore>(rig: &mut Rig, host: &mut Custody<S>, prov: &Software, now: u64, answered: &mut usize) {
    for _ in 0..16 {
        // key requests of the carrier handshake, and signatures of the layer
        loop {
            let sig = rig.conn.key_request(0).map(|r| host.answer(now, &r));
            let Some(sig) = sig else { break };
            *answered += 1;
            let mut env = Env {
                provider: prov,
                now,
                drbg: &mut rig.drbg,
            };
            rig.conn.key_response(now, &mut env, 0, sig.response());
        }
        loop {
            let sig = rig.conn.sign_request().map(|r| host.answer(now, &r));
            let Some(sig) = sig else { break };
            *answered += 1;
            rig.conn.sign_response(now, sig.response());
        }
        // node -> relay
        let mut out = vec![0u8; 32 * 1024];
        let n = rig.conn.poll_stream(0, &mut out);
        if n > 0 {
            let mut rest = &out[..n];
            while !rest.is_empty() {
                let took = rig.rc.receive(rest);
                rest = &rest[took..];
                relay_poll(rig, now);
                if took == 0 {
                    break;
                }
            }
        }
        // relay -> node
        let mut back = vec![0u8; 32 * 1024];
        let m = rig.rc.transmit(&mut back);
        if m > 0 {
            let mut env = Env {
                provider: prov,
                now,
                drbg: &mut rig.drbg,
            };
            rig.conn.stream_data(now, &mut env, 0, &back[..m]);
        }
        // frames the relay wants to send to the node
        for rec in rig.sink.take() {
            if let Rec::Carrier(_, plain) = rec {
                let mut sealed = vec![0u8; 20 * 1024];
                let k = rig.rc.seal_bytes(prov, &plain, &mut sealed).unwrap();
                let mut env = Env {
                    provider: prov,
                    now,
                    drbg: &mut rig.drbg,
                };
                rig.conn.stream_data(now, &mut env, 0, &sealed[..k]);
            }
        }
        if n == 0 && m == 0 {
            break;
        }
    }
}

fn relay_poll(rig: &mut Rig, now: u64) {
    for _ in 0..64 {
        let soft = SoftKeys::<Software> {
            signer: Some((SecHandle(1), &rig.relay_kp)),
            prekeys: None,
        };
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut rig.rdrbg,
        };
        let step = match rig.rc.poll(&mut env, &mut rig.stores).unwrap() {
            Poll::Idle => return,
            Poll::KeyRequest => {
                rig.rc.answer_soft(&mut env, &soft).unwrap();
                None
            }
            Poll::Open(peer) => Some(peer),
            Poll::Frame(f) => {
                if let (Some(sess), Some(peer)) = (rig.session, rig.peer) {
                    let _ = rig.relay.carrier_frame(now, &peer, sess, &f, &mut rig.sink);
                }
                None
            }
            Poll::Handshake => None,
        };
        if let Some(peer) = step {
            rig.peer = Some(peer);
            rig.session = Some(rig.relay.carrier_opened(now, peer, &mut rig.sink).unwrap());
        }
    }
}
