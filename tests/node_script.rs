//! A node over a scripted endpoint: the endpoint hands the node exactly the events a test queues, accepts every command
//! and records the sessions the node closed and the dials it made. For tests of how the node routes and bounds what an
//! endpoint tells it, which a real endpoint's own ordering would hide.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    dead_code,
    clippy::cast_possible_truncation,
    missing_docs,
    reason = "a test support module"
)]

use std::collections::VecDeque;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use vinc_broadcast::Limits;
use vinc_connect::client::{Config as ConnCfg, Port, RelayCfg};
use vinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use vinc_node::{Apps, Config as NodeConfig, Ep, HUB_ALPN, Node, StartError};
use vinc_security::{Alpn, Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use vinc_tests::Caps;
use vinc_transport::stream::{NoSource, StreamId};

/// The first session id the script gives a dial the node makes.
pub(crate) const DIALED: u64 = 1 << 40;

/// An endpoint that hands out scripted events. It records the sessions the node closed and the dials it made.
#[derive(Default)]
pub(crate) struct Script {
    pub(crate) events: VecDeque<Event>,
    pub(crate) closed: Vec<SessionId>,
    pub(crate) dials: Vec<NodeId>,
}

impl Port for Script {
    type Src = NoSource;
    fn command(&mut self, _now: u64, cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let mut value = Value::None;
        match cmd {
            Command::Close { session, .. } => self.closed.push(session),
            Command::Connect { node, .. } => {
                value = Value::Session(SessionId(DIALED + self.dials.len() as u64));
                self.dials.push(node);
            }
            _ => {}
        }
        Ok(Reply {
            value,
            events: Events::default(),
        })
    }
    fn stats(&self, _session: SessionId) -> Option<SessionStats> {
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn peer(&self, _node: &NodeId) -> Option<vinc_core::PeerInfo> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; vinc_core::REACH_BODY_MAX]) -> usize {
        0
    }
    fn by_conn_id(&self, _cid: &vinc_security::ConnId) -> Option<SessionStats> {
        None
    }
}

impl Ep for Script {
    fn handle_datagram(&mut self, _now: u64, _local: SocketAddr, _remote: SocketAddr, _buf: &mut [u8]) {}
    fn poll_transmit(&mut self, _now: u64, _out: &mut [u8]) -> Option<Transmit> {
        None
    }
    fn poll_event(&mut self) -> Option<Event> {
        self.events.pop_front()
    }
    fn poll_timeout(&self) -> Option<u64> {
        None
    }
    fn handle_timeout(&mut self, _now: u64) {}
    fn register_alpn(&mut self, _alpn: &[u8]) -> bool {
        true
    }
    fn read_chunk(&self, _session: SessionId, _stream: StreamId) -> Option<&[u8]> {
        None
    }
    fn read_at(&self, _session: SessionId, _stream: StreamId, _offset: u64) -> Option<&[u8]> {
        None
    }
    fn stored_after(&self, _session: SessionId, _stream: StreamId, _from: u64) -> Option<Range<u64>> {
        None
    }
    fn send_state(&self, _session: SessionId, _stream: StreamId) -> Option<SendState> {
        None
    }
    fn in_flight(&self, _session: SessionId) -> Option<u64> {
        None
    }
    fn read_extension(&mut self, _out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
        Ok(None)
    }
    fn session_at(&self, _n: usize) -> Option<SessionStats> {
        None
    }
    fn session_from(&self, _remote: &SocketAddr, _keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
        None
    }
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
    fn add_iface(&mut self, _local: SocketAddr) -> Option<IfaceId> {
        None
    }
    fn iface_event(&mut self, _now: u64, _id: IfaceId, _ev: IfaceEvent) {}
}

pub(crate) type ScriptNode<A> = Node<Script, Caps, (), 4, 32, A>;

/// The identity a test node or peer of seed byte `n` has.
pub(crate) fn id_of(n: u8) -> NodeId {
    Keypair::from_seed(IdentityAlg::Ed25519, &[n; 32]).unwrap().node_id()
}

/// A node of seed byte `0x11` over a scripted endpoint, listing `hubs` as its relays and speaking `alpn` on the hub
/// stream. It is large: build and drive it on a thread with a big stack.
pub(crate) fn node_with<A: Apps<Caps>>(
    is_hub: bool,
    hubs: &[NodeId],
    alpn: &'static [u8],
    apps: A,
) -> Result<Box<ScriptNode<A>>, StartError> {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Caps(vinc_crypto::Software, true);
    let mut drbg = Drbg::new(&[0x21; 32]);
    let mut env = Env {
        provider: &prov,
        now: 0,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let local = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);
    let mut relays = [None; 4];
    for (i, (slot, hub)) in relays.iter_mut().zip(hubs).enumerate() {
        let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 20 + i as u8)), 4433);
        *slot = Some(RelayCfg {
            id: *hub,
            udp: Some(addr),
            tcp: Some(addr),
            ws: Some(addr),
        });
    }
    let cfg = NodeConfig {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays,
            phone: false,
            restarted: false,
            start: 0,
            v6: false,
            keep_learn: false,
        },
        is_hub,
        version: 1,
        alpn,
        limits: Limits::default(),
        wall_ms: 1_700_000_000_000,
        local,
        trace: false,
    };
    Node::with_apps(
        &cfg,
        Script::default(),
        prekey,
        prov,
        Drbg::new(&[0x31; 32]),
        Box::new(Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap()),
        (),
        7,
        apps,
    )
    .map(Box::new)
}

/// The hub protocol id as a session's protocol.
pub(crate) fn hub_alpn() -> Alpn {
    Alpn::new(HUB_ALPN).unwrap()
}
