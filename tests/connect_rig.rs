//! An in-memory rig for the client connectivity layer: the layer, a relay and the relay side of the protected carrier,
//! with bytes shuttled between them, and the node's key custody left to the test.
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

use pinc_connect::carrier::session::{self, Poll, ProtectedCarrier};
use pinc_connect::client::{Config, Connectivity, Io, RelayCfg};
use pinc_connect::relay::{Relay, Trace};
use pinc_crypto::{Drbg, Software};
use pinc_security::{
    ConnId, Env, KeyHandle as SecHandle, KeyRequest, KeyResponse, LocalIdentity, ResponderStores, SoftKeys,
};

use crate::connect_common::{Collect, Rec, SEC, ed, id};

pub const RELAY_UDP: &str = "203.0.113.10:4433";
pub const RELAY_TCP: &str = "203.0.113.10:443";

pub type R = Relay<8, 8, 4, 4096>;
pub type Conn = Connectivity<Software, 1, 4>;

/// An answer that owns its bytes.
pub enum Ans {
    Sig(Vec<u8>),
    Secret(pinc_crypto::Secret<32>),
}

impl Ans {
    pub fn response(&self) -> KeyResponse<'_> {
        match self {
            Self::Sig(s) => KeyResponse::Signature(s),
            Self::Secret(s) => KeyResponse::SharedSecret(pinc_crypto::Secret::new(*s.expose())),
        }
    }
}

/// Who answers the key requests of the node.
pub trait Custody {
    fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans;
}

/// The relay and the node, shuttling bytes in memory.
pub struct Rig {
    pub conn: Box<Conn>,
    pub relay: Box<R>,
    pub rc: Box<ProtectedCarrier<Software>>,
    stores: ResponderStores<2, 2>,
    relay_kp: pinc_crypto::Keypair,
    pub drbg: Drbg,
    rdrbg: Drbg,
    pub sink: Collect,
    pub session: Option<pinc_connect::relay::SessionId>,
    peer: Option<pinc_crypto::NodeId>,
    pub relay_id: pinc_crypto::NodeId,
    pub udp: SocketAddr,
    pub tcp: SocketAddr,
}

impl Rig {
    pub fn new(identity: &LocalIdentity, prekey: pinc_security::PrekeyInfo) -> Self {
        Self::with_tcp(identity, prekey, Some(RELAY_TCP.parse().unwrap()))
    }

    /// A rig whose relay has `tcp` for its carrier address, or none (a relay reached over UDP only).
    pub fn with_tcp(identity: &LocalIdentity, prekey: pinc_security::PrekeyInfo, tcp: Option<SocketAddr>) -> Self {
        let relay_kp = ed(0x77);
        let relay_id = id(&relay_kp);
        let udp: SocketAddr = RELAY_UDP.parse().unwrap();
        let mut relays = [None; 1];
        relays[0] = Some(RelayCfg {
            id: relay_id,
            udp: Some(udp),
            tcp,
            ws: None,
        });
        let cfg = Config {
            me: identity.node_id(),
            identity: *identity,
            relays,
            phone: false,
            restarted: false,
            start: 1000 * SEC,
            v6: false,
            keep_learn: false,
        };
        let mut conn = Box::new(Connectivity::new(cfg, prekey, Software, 7));
        conn.set_local(&["192.168.1.2:4433".parse().unwrap()]);
        let relay = Box::new(R::new(pinc_connect::relay::Config::new(relay_id, 3)));
        let rcfg = session::responder_config(
            LocalIdentity::from_keypair(&relay_kp, SecHandle(1)).unwrap(),
            ConnId::new(b"relay000").unwrap(),
        )
        .unwrap();
        Self {
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
            relay_id,
            udp,
            tcp: tcp.unwrap_or_else(|| RELAY_TCP.parse().unwrap()),
        }
    }

    pub fn env(&mut self, now: u64) -> Env<'_, Software> {
        Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        }
    }

    /// Address discovery, the home relay and the carrier handshake, up to an open carrier. Returns the time after.
    pub fn bring_up<C: Custody>(&mut self, custody: &mut C, now: u64, answered: &mut usize) -> u64 {
        self.bring_up_after(custody, now, SEC, answered)
    }

    /// As [`Rig::bring_up`], with `step` between the address discovery and the carrier (0 keeps every call at `now`).
    pub fn bring_up_after<C: Custody>(
        &mut self,
        custody: &mut C,
        mut now: u64,
        step: u64,
        answered: &mut usize,
    ) -> u64 {
        let wall = |now: u64| now / 1_000_000;
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.probe_all(now, &mut env);
        let mut buf = vec![0u8; 2048];
        let (to, n) = self.conn.poll_udp(&mut buf).expect("a probe");
        assert_eq!(to, self.udp);
        let src: SocketAddr = "198.51.100.5:20000".parse().unwrap();
        self.relay.datagram(now, src, None, &buf[..n], &mut self.sink).unwrap();
        let reply = self
            .sink
            .effects()
            .into_iter()
            .find_map(|r| if let Rec::Udp(_, b) = r { Some(b) } else { None })
            .expect("the relay answers");
        assert!(self.conn.handle_udp(now, self.udp, &reply));
        assert_eq!(self.conn.home(), Some(0));
        now += step;
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.tick(now, &mut env, Some(wall(now)));
        let io = self.conn.poll_io().expect("a stream request");
        assert!(matches!(io, Io::Open { relay: 0, to, .. } if to == self.tcp));
        let mut env = Env {
            provider: &Software,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.stream_opened(now, &mut env, 0);
        for _ in 0..40 {
            self.shuttle(custody, now, answered);
            if self.session.is_some() && self.conn.carrier_state(0) == pinc_connect::client::link::State::Open {
                break;
            }
        }
        assert!(self.session.is_some(), "the relay authenticated the node");
        now
    }

    /// Move bytes between the node and the relay, and answer the node's key and signature requests.
    pub fn shuttle<C: Custody>(&mut self, custody: &mut C, now: u64, answered: &mut usize) {
        for _ in 0..16 {
            loop {
                let sig = self.conn.key_request(0).map(|r| custody.answer(now, &r));
                let Some(sig) = sig else { break };
                *answered += 1;
                let mut env = Env {
                    provider: &Software,
                    now,
                    drbg: &mut self.drbg,
                };
                self.conn.key_response(now, &mut env, 0, sig.response());
            }
            loop {
                let sig = self.conn.sign_request().map(|r| custody.answer(now, &r));
                let Some(sig) = sig else { break };
                *answered += 1;
                self.conn.sign_response(now, sig.response());
            }
            let mut out = vec![0u8; 32 * 1024];
            let n = self.conn.poll_stream(0, &mut out);
            if n > 0 {
                let mut rest = &out[..n];
                while !rest.is_empty() {
                    let took = self.rc.receive(rest);
                    rest = &rest[took..];
                    self.relay_poll(now);
                    if took == 0 {
                        break;
                    }
                }
            }
            let mut back = vec![0u8; 32 * 1024];
            let m = self.rc.transmit(&mut back);
            if m > 0 {
                let mut env = Env {
                    provider: &Software,
                    now,
                    drbg: &mut self.drbg,
                };
                self.conn.stream_data(now, &mut env, 0, &back[..m]);
            }
            for rec in self.sink.take() {
                if let Rec::Carrier(_, plain) = rec {
                    let mut sealed = vec![0u8; 20 * 1024];
                    let k = self.rc.seal_bytes(&Software, &plain, &mut sealed).unwrap();
                    let mut env = Env {
                        provider: &Software,
                        now,
                        drbg: &mut self.drbg,
                    };
                    self.conn.stream_data(now, &mut env, 0, &sealed[..k]);
                }
            }
            if n == 0 && m == 0 {
                break;
            }
        }
    }

    pub fn relay_poll(&mut self, now: u64) {
        for _ in 0..64 {
            let soft = SoftKeys::<Software> {
                signer: Some((SecHandle(1), &self.relay_kp)),
                prekeys: None,
            };
            let mut env = Env {
                provider: &Software,
                now,
                drbg: &mut self.rdrbg,
            };
            let step = match self.rc.poll(&mut env, &mut self.stores).unwrap() {
                Poll::Idle => return,
                Poll::KeyRequest => {
                    self.rc.answer_soft(&mut env, &soft).unwrap();
                    None
                }
                Poll::Open(peer) => Some(peer),
                Poll::Frame(f) => {
                    if let (Some(sess), Some(peer)) = (self.session, self.peer) {
                        let _ = self.relay.carrier_frame(now, &peer, sess, &f, &mut self.sink);
                    }
                    None
                }
                Poll::Handshake => None,
            };
            if let Some(peer) = step {
                self.peer = Some(peer);
                self.session = Some(self.relay.carrier_opened(now, peer, &mut self.sink).unwrap());
            }
        }
    }

    pub fn traces(&self) -> Vec<Trace> {
        self.sink.traces()
    }
}
