//! A hub finds the member a datagram came from without visiting its member sessions: `Node::member_at` asks the
//! endpoint's table of sessions by address once and reads no session's stats, however many members the hub holds.
//!
//! The endpoint is scripted: it raises an `Incoming` hub-protocol session for each of 300 members, answers
//! `session_from` from its table of addresses, and counts every `stats` call (and answers none, so a walk of the
//! sessions finds no one). A member the walk would reach only after visiting every other session is found with no
//! visit, a session the node does not hold as incoming is not an answer, and an address nobody holds gives none. A
//! timer call reads no member's stats: the node used to sample every member session's packet count on each one.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::cast_possible_truncation,
    missing_docs
)]

use std::cell::Cell;
use std::collections::VecDeque;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use pinc_broadcast::Limits;
use pinc_connect::client::{Config as ConnCfg, Port};
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use pinc_node::{Config as NodeConfig, Ep, HUB_ALPN, Node};
use pinc_security::{Alpn, Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_tests::Caps;
use pinc_transport::stream::{NoSource, StreamId};

const MEMBERS: u64 = 300;

#[derive(Default)]
struct Script {
    events: VecDeque<Event>,
    /// The validated direct address of each session.
    routes: Vec<(SessionId, SocketAddr)>,
    /// `stats` calls so far.
    visits: Cell<usize>,
}

impl Port for Script {
    type Src = NoSource;
    fn command(&mut self, _now: u64, _cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        Ok(Reply {
            value: Value::None,
            events: Events::default(),
        })
    }
    fn stats(&self, _session: SessionId) -> Option<SessionStats> {
        self.visits.set(self.visits.get() + 1);
        None
    }
    fn node(&self) -> Option<NodeStats> {
        None
    }
    fn peer(&self, _node: &NodeId) -> Option<pinc_core::PeerInfo> {
        None
    }
    fn reach_body(&self, _session: SessionId, _out: &mut [u8; pinc_core::REACH_BODY_MAX]) -> usize {
        0
    }
    fn by_conn_id(&self, _cid: &pinc_security::ConnId) -> Option<SessionStats> {
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
    fn session_from(&self, remote: &SocketAddr, keep: &dyn Fn(SessionId) -> bool) -> Option<SessionId> {
        self.routes
            .iter()
            .filter(|(s, a)| a == remote && keep(*s))
            .map(|(s, _)| *s)
            .min()
    }
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
    fn add_iface(&mut self, _local: SocketAddr) -> Option<IfaceId> {
        None
    }
    fn iface_event(&mut self, _now: u64, _id: IfaceId, _ev: IfaceEvent) {}
}

type Hub = Node<Script, Caps, (), 4, 32>;

fn hub() -> Box<Hub> {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &[0x11; 32]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Caps(pinc_crypto::Software, true);
    let mut drbg = Drbg::new(&[0x21; 32]);
    let mut env = Env {
        provider: &prov,
        now: 0,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let local = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);
    let cfg = NodeConfig {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays: [None; 4],
            phone: false,
            restarted: false,
            start: 0,
            v6: false,
            keep_learn: false,
        },
        is_hub: true,
        version: 1,
        alpn: HUB_ALPN,
        limits: Limits::default(),
        map_keys: pinc_tests::id_key(0x5eed),
        wall_ms: 1_700_000_000_000,
        local,
        trace: false,
    };
    let key = Keypair::from_seed(alg, &[0x11; 32]).unwrap();
    Box::new(
        Node::new(
            &cfg,
            Script::default(),
            prekey,
            prov,
            Drbg::new(&[0x31; 32]),
            Box::new(key),
            (),
            7,
        )
        .expect("the node starts"),
    )
}

fn member(i: u64) -> NodeId {
    let mut seed = [0x40; 32];
    seed[..8].copy_from_slice(&i.to_le_bytes());
    Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap().node_id()
}

fn addr(i: u64) -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(10, 1, (i >> 8) as u8, i as u8)), 4433)
}

#[test]
fn a_hub_finds_the_sender_of_a_datagram_without_visiting_its_member_sessions() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = hub();
            let alpn = Alpn::new(HUB_ALPN).unwrap();
            for i in 0..MEMBERS {
                let session = SessionId(i);
                node.endpoint_mut().events.push_back(Event::Incoming {
                    session,
                    node: member(i),
                    alpn,
                });
                node.endpoint_mut().routes.push((session, addr(i)));
            }
            // A session the endpoint holds at an address but the node never heard of is no member.
            node.endpoint_mut().routes.push((SessionId(MEMBERS), addr(MEMBERS)));
            node.poll(1_000_000_000);
            while node.poll_event().is_some() {}
            node.endpoint_mut().visits.set(0);
            for i in [0, MEMBERS / 2, MEMBERS - 1] {
                assert_eq!(node.member_at(&addr(i)), Some(member(i)), "member {i}");
            }
            assert_eq!(node.member_at(&addr(MEMBERS)), None, "a session the node does not hold");
            assert_eq!(node.member_at(&addr(MEMBERS + 1)), None, "an address nobody holds");
            assert_eq!(
                node.endpoint_mut().visits.get(),
                0,
                "member sessions visited to find a sender"
            );
            // A timer call reads no member's stats either: when a member was last heard is read when it is needed.
            node.handle_timeout(2_000_000_000);
            assert_eq!(
                node.endpoint_mut().visits.get(),
                0,
                "member sessions visited by a timer call"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
