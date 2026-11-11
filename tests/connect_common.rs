//! Scaffolding shared by the connectivity tests: identities, a pair of protected carriers wired in memory, and an
//! effect collector for the relay.
#![allow(
    clippy::many_single_char_names,
    clippy::assert_is_empty,
    clippy::decimal_bitwise_operands,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::cast_lossless,
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements
)]

use vinc_connect::carrier::session::{self, ALPN, CarrierError, Poll, ProtectedCarrier};
use vinc_connect::carrier::{Frame, NODE_ID_LEN};
use vinc_connect::relay::datagram::Datagram;
use vinc_connect::relay::{CloseReason, Effect, Sink, Trace, UdpTarget};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId, Software};
use vinc_security::{
    ConnId, CreditRecord, Env, InitiatorParams, KeyHandle, LocalIdentity, PrekeyPolicy, ResponderStores, SoftKeys,
    SoftPrekeys,
};

pub const NOW: u64 = 1_000_000_000_000;
pub const SEC: u64 = 1_000_000_000;

/// Run `f` on a thread with a large stack: carriers hold their buffers inline.
pub fn big_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

pub fn keypair(alg: IdentityAlg, tag: u8) -> Keypair {
    Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap()
}

pub fn ed(tag: u8) -> Keypair {
    keypair(IdentityAlg::Ed25519, tag)
}

pub fn id(kp: &Keypair) -> NodeId {
    kp.node_id()
}

/// A node id from a tag byte, with no key behind it (for routing tests).
pub fn nid(tag: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [tag; 32],
    }
}

/// A frame as its owned encoding.
pub fn enc(f: &Frame<'_>) -> Vec<u8> {
    let mut b = vec![0u8; vinc_connect::carrier::MAX_FRAME_LEN];
    let n = f.encode(&mut b).unwrap();
    b.truncate(n);
    b
}

pub fn node_bytes(n: &NodeId) -> [u8; NODE_ID_LEN] {
    let mut out = [0u8; NODE_ID_LEN];
    out[0] = n.alg.tag();
    out[1..].copy_from_slice(&n.bytes);
    out
}

/// A dialer and a listener wired together in memory.
pub struct Rig {
    pub client: ProtectedCarrier<Software>,
    pub relay: ProtectedCarrier<Software>,
    pub client_kp: Keypair,
    pub relay_kp: Keypair,
    prov: Software,
    c_drbg: Drbg,
    r_drbg: Drbg,
    prekeys: SoftPrekeys<Software>,
    stores: ResponderStores<4, 4>,
}

impl Rig {
    /// A dialer that expects `expect` (the relay's node id; pass `None` for the real one).
    pub fn new(expect: Option<NodeId>) -> Box<Self> {
        Self::with_alpn(expect, ALPN)
    }

    /// As [`Rig::new`], with the dialer asking for `alpn`.
    pub fn with_alpn(expect: Option<NodeId>, alpn: &[u8]) -> Box<Self> {
        let prov = Software;
        let client_kp = ed(0x31);
        let relay_kp = ed(0x32);
        let mut c_drbg = Drbg::new(&[0x41; 32]);
        let r_drbg = Drbg::new(&[0x42; 32]);
        let cid = LocalIdentity::from_keypair(&client_kp, KeyHandle(1)).unwrap();
        let rid = LocalIdentity::from_keypair(&relay_kp, KeyHandle(1)).unwrap();
        let mut env = Env {
            provider: &prov,
            now: NOW,
            drbg: &mut c_drbg,
        };
        let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
        let prekey = prekeys.acquire(&mut env).unwrap();
        let client = ProtectedCarrier::dial(
            &mut env,
            InitiatorParams {
                peer: expect.unwrap_or_else(|| id(&relay_kp)),
                alpn,
                scid: ConnId::new(b"client00").unwrap(),
                identity: &cid,
                prekey: &prekey,
                peer_has_prekey: false,
                ticket: None,
                credit: CreditRecord::NONE,
            },
        )
        .unwrap();
        let relay =
            ProtectedCarrier::accept(session::responder_config(rid, ConnId::new(b"relay000").unwrap()).unwrap());
        Box::new(Self {
            client,
            relay,
            client_kp,
            relay_kp,
            prov,
            c_drbg,
            r_drbg,
            prekeys,
            stores: ResponderStores::default(),
        })
    }

    /// Poll the client side once; frames come back as their encoding.
    pub fn poll_client(&mut self) -> Result<Out, CarrierError> {
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &self.client_kp)),
            prekeys: Some(&self.prekeys),
        };
        let mut env = Env {
            provider: &self.prov,
            now: NOW,
            drbg: &mut self.c_drbg,
        };
        let mut stores = ResponderStores::<4, 4>::default();
        poll_soft(&mut self.client, &mut env, &mut stores, &soft)
    }

    pub fn poll_relay(&mut self) -> Result<Out, CarrierError> {
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &self.relay_kp)),
            prekeys: None,
        };
        let mut env = Env {
            provider: &self.prov,
            now: NOW,
            drbg: &mut self.r_drbg,
        };
        poll_soft(&mut self.relay, &mut env, &mut self.stores, &soft)
    }

    /// Move pending handshake bytes client to relay.
    pub fn flush_client(&mut self) -> usize {
        let mut buf = vec![0u8; 32 * 1024];
        let n = self.client.transmit(&mut buf);
        self.feed_relay(&buf[..n]);
        n
    }

    pub fn flush_relay(&mut self) -> usize {
        let mut buf = vec![0u8; 32 * 1024];
        let n = self.relay.transmit(&mut buf);
        self.feed_client(&buf[..n]);
        n
    }

    pub fn feed_relay(&mut self, mut bytes: &[u8]) {
        while !bytes.is_empty() {
            let n = self.relay.receive(bytes);
            bytes = &bytes[n..];
            assert!(n > 0, "the relay buffer is stuck");
        }
    }

    pub fn feed_client(&mut self, mut bytes: &[u8]) {
        while !bytes.is_empty() {
            let n = self.client.receive(bytes);
            bytes = &bytes[n..];
            assert!(n > 0, "the client buffer is stuck");
        }
    }

    /// Run the handshake to completion; returns the node ids each side authenticated (relay as seen by the client,
    /// client as seen by the relay).
    pub fn handshake(&mut self) -> (NodeId, NodeId) {
        let (mut seen_by_client, mut seen_by_relay) = (None, None);
        for _ in 0..64 {
            self.flush_client();
            loop {
                match self.poll_relay().unwrap() {
                    Out::Open(p) => seen_by_relay = Some(p),
                    Out::Idle => break,
                    _ => {}
                }
            }
            self.flush_relay();
            loop {
                match self.poll_client().unwrap() {
                    Out::Open(p) => seen_by_client = Some(p),
                    Out::Idle => break,
                    _ => {}
                }
            }
            if let (Some(a), Some(b)) = (seen_by_client, seen_by_relay) {
                return (a, b);
            }
        }
        panic!("the handshake did not complete");
    }

    pub fn seal_client(&mut self, f: &Frame<'_>) -> Vec<u8> {
        let mut b = vec![0u8; 20 * 1024];
        let n = self.client.seal(&self.prov, f, &mut b).unwrap();
        b.truncate(n);
        b
    }

    pub fn seal_relay(&mut self, f: &Frame<'_>) -> Vec<u8> {
        let mut b = vec![0u8; 20 * 1024];
        let n = self.relay.seal(&self.prov, f, &mut b).unwrap();
        b.truncate(n);
        b
    }

    /// Seal into a caller buffer (no allocation).
    pub fn seal_client_into(&mut self, f: &Frame<'_>, out: &mut [u8]) -> usize {
        self.client.seal(&self.prov, f, out).unwrap()
    }

    /// Poll the relay side and return the kind of the frame found (no allocation).
    pub fn relay_next_kind(&mut self) -> Option<u8> {
        let mut env = Env {
            provider: &self.prov,
            now: NOW,
            drbg: &mut self.r_drbg,
        };
        match self.relay.poll(&mut env, &mut self.stores).unwrap() {
            Poll::Frame(f) => Some(f.kind()),
            _ => None,
        }
    }

    pub fn seal_client_bytes(&mut self, plain: &[u8]) -> Result<Vec<u8>, CarrierError> {
        let mut b = vec![0u8; 20 * 1024];
        let n = self.client.seal_bytes(&self.prov, plain, &mut b)?;
        b.truncate(n);
        Ok(b)
    }
}

/// A poll result without borrows.
#[derive(Debug, PartialEq, Eq)]
pub enum Out {
    Idle,
    Handshake,
    KeyRequest,
    Open(NodeId),
    Frame(Vec<u8>),
}

/// Poll a carrier and answer its key requests from software keys, as a software node's host does.
pub fn poll_soft<const PK: usize, const TK: usize>(
    c: &mut ProtectedCarrier<Software>,
    env: &mut Env<'_, Software>,
    stores: &mut ResponderStores<PK, TK>,
    soft: &SoftKeys<'_, Software>,
) -> Result<Out, CarrierError> {
    let mut r = out(c.poll(env, stores))?;
    while r == Out::KeyRequest {
        r = out(c.answer_soft(env, soft))?;
    }
    Ok(r)
}

fn out(r: Result<Poll<'_>, CarrierError>) -> Result<Out, CarrierError> {
    r.map(|p| match p {
        Poll::Idle => Out::Idle,
        Poll::Handshake => Out::Handshake,
        Poll::KeyRequest => Out::KeyRequest,
        Poll::Open(n) => Out::Open(n),
        Poll::Frame(f) => Out::Frame(enc(&f)),
    })
}

/// What the relay asked the host to do, owned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rec {
    Carrier(NodeId, Vec<u8>),
    Peer(NodeId, Vec<u8>),
    Udp(UdpTarget, Vec<u8>),
    Local(NodeId, Vec<u8>),
    Close(NodeId, CloseReason),
    Wake(NodeId),
    Trace(Trace),
}

#[derive(Debug, Default)]
pub struct Collect(pub Vec<Rec>, pub Vec<Trace>);

impl Sink for Collect {
    fn emit(&mut self, e: Effect<'_>) {
        self.0.push(match e {
            Effect::Carrier { to, frame } => Rec::Carrier(to, enc(&frame)),
            Effect::PeerRelay { to, frame } => Rec::Peer(to, enc(&frame)),
            Effect::Udp { to, datagram } => {
                let mut b = vec![0u8; 2048];
                let n = datagram.encode(&mut b).unwrap();
                b.truncate(n);
                Rec::Udp(to, b)
            }
            Effect::Local { from, packet } => Rec::Local(from, packet.to_vec()),
            Effect::Close { node, reason, .. } => Rec::Close(node, reason),
            Effect::Wake { node } => Rec::Wake(node),
            Effect::Trace(t) => {
                self.1.push(t);
                Rec::Trace(t)
            }
        });
    }
}

impl Collect {
    pub fn take(&mut self) -> Vec<Rec> {
        std::mem::take(&mut self.0)
    }

    /// The effects without the trace events.
    pub fn effects(&mut self) -> Vec<Rec> {
        self.take()
            .into_iter()
            .filter(|r| !matches!(r, Rec::Trace(_)))
            .collect()
    }

    /// Every trace event so far (effect calls do not clear it).
    pub fn traces(&self) -> Vec<Trace> {
        self.1.clone()
    }
}

pub fn dg(d: &Datagram<'_>) -> Vec<u8> {
    let mut b = vec![0u8; 2048];
    let n = d.encode(&mut b).unwrap();
    b.truncate(n);
    b
}

// ---- the relay fixture ----

use core::net::SocketAddr;
use vinc_connect::record::{self, MAX_RECORD_LEN, Reach, RecordFields};
use vinc_connect::relay::sleep;
use vinc_connect::relay::{Config, RecordOrigin, Reject, Relay, SessionId};

pub type R = Relay<16, 16, 8, 4096>;

pub const T0: u64 = 1_000 * SEC;

pub struct Fx {
    pub r: Box<R>,
    pub s: Collect,
    pub me: NodeId,
    pub kp: Keypair,
}

impl Fx {
    pub fn new() -> Self {
        Self::with(|_| {})
    }

    pub fn with(tune: impl FnOnce(&mut Config)) -> Self {
        let kp = ed(0x10);
        let me = id(&kp);
        let mut cfg = Config::new(me, 0x5eed);
        tune(&mut cfg);
        Self {
            r: Box::new(R::new(cfg)),
            s: Collect::default(),
            me,
            kp,
        }
    }

    pub fn open(&mut self, now: u64, node: NodeId) -> SessionId {
        self.r.carrier_opened(now, node, &mut self.s).unwrap()
    }

    pub fn send(&mut self, now: u64, node: NodeId, sess: SessionId, f: &Frame<'_>) -> Result<(), Reject> {
        self.r.carrier_frame(now, &node, sess, f, &mut self.s)
    }

    pub fn peer(&mut self, now: u64, from: NodeId, f: &Frame<'_>) -> Result<(), Reject> {
        self.r.peer_frame(now, &from, f, &mut self.s)
    }

    pub fn fx(&mut self) -> Vec<Rec> {
        self.s.effects()
    }
}

pub fn rec_fields(home: NodeId, seq: u64) -> RecordFields<'static> {
    RecordFields {
        home,
        seq,
        reach: Reach::Public,
        addrs: &[],
        hints: b"",
    }
}

pub fn record_bytes(kp: &Keypair, home: NodeId, seq: u64) -> Vec<u8> {
    let mut b = vec![0u8; MAX_RECORD_LEN];
    let n = record::sign(kp, &rec_fields(home, seq), &mut b).unwrap();
    b.truncate(n);
    b
}

pub fn addr() -> SocketAddr {
    "198.51.100.9:40000".parse().unwrap()
}

pub fn traces_of(fx: &Fx) -> Vec<Trace> {
    fx.s.traces()
}

impl Fx {
    pub fn traces_has_replica(&self, n: NodeId) -> bool {
        self.s.traces().contains(&Trace::RecordStored {
            node: n,
            seq: 3,
            origin: RecordOrigin::Replica,
        })
    }
}

pub trait ReplicaForTest {
    fn replica_for_test(&mut self, now: u64, rec: &[u8], s: &mut Collect) -> Result<(), Reject>;
}

impl<const C: usize, const RR: usize, const MN: usize, const MB: usize> ReplicaForTest for Relay<C, RR, MN, MB> {
    fn replica_for_test(&mut self, now: u64, rec: &[u8], s: &mut Collect) -> Result<(), Reject> {
        let peer = nid(0x91);
        self.add_peer(peer);
        self.peer_frame(now, &peer, &Frame::Sync { record: rec }, s)
    }
}

pub fn notice(kp: &Keypair, relay: &NodeId, ts_ms: u64) -> Vec<u8> {
    let mut b = vec![0u8; sleep::MAX_LEN];
    let n = sleep::sign(kp, relay, ts_ms, &mut b).unwrap();
    b.truncate(n);
    b
}
