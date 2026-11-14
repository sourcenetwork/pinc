//! The node's port-mapping client: the host turns it on, the node sends the gateway's requests from its own socket,
//! takes the gateway's answers before the endpoint sees them, puts the mapped address first among the addresses it
//! offers (and so in its record), renews, and releases the mapping when told to stop.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    missing_docs
)]

use std::collections::VecDeque;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use vinc_broadcast::Limits;
use vinc_connect::client::{Config as ConnCfg, Port};
use vinc_connect::record::MAX_ADDRS;
use vinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use vinc_node::{Config as NodeConfig, Ep, HUB_ALPN, Node};
use vinc_portmap::{Proto, pcp};
use vinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use vinc_tests::Caps;
use vinc_transport::stream::{NoSource, StreamId};

/// An endpoint that hands out scripted events and accepts every command with an empty reply. It records the sessions
/// the node closed, and drops every later event of one but its close: a closed session's packets are not read.
#[derive(Default)]
struct Script {
    events: VecDeque<Event>,
    closed: Vec<SessionId>,
}

impl Port for Script {
    type Src = NoSource;
    fn command(&mut self, _now: u64, cmd: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        if let Command::Close { session, .. } = cmd {
            self.closed.push(session);
        }
        Ok(Reply {
            value: Value::None,
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
        while let Some(ev) = self.events.pop_front() {
            if matches!(ev, Event::Closed { .. }) || !ev.session().is_some_and(|s| self.closed.contains(&s)) {
                return Some(ev);
            }
        }
        None
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
    fn poll_trace(&mut self) -> Option<TraceRecord> {
        None
    }
    fn add_iface(&mut self, _local: SocketAddr) -> Option<IfaceId> {
        None
    }
    fn iface_event(&mut self, _now: u64, _id: IfaceId, _ev: IfaceEvent) {}
}

type Member = Node<Script, Caps, (), 4, 32>;

const SEC: u64 = 1_000_000_000;

fn local() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 5)), 4433)
}

fn gw() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)), 5351)
}

fn ext() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 9)), 4433)
}

fn member() -> Box<Member> {
    let alg = IdentityAlg::Ed25519;
    let kp = Keypair::from_seed(alg, &[0x12; 32]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Caps(vinc_crypto::Software, true);
    let mut drbg = Drbg::new(&[0x22; 32]);
    let mut env = Env {
        provider: &prov,
        now: 0,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
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
        is_hub: false,
        version: 1,
        alpn: HUB_ALPN,
        limits: Limits::default(),
        wall_ms: 1_700_000_000_000,
        local: local(),
        trace: false,
    };
    let key = Keypair::from_seed(alg, &[0x12; 32]).unwrap();
    Box::new(
        Node::new(
            &cfg,
            Script::default(),
            prekey,
            prov,
            Drbg::new(&[0x32; 32]),
            Box::new(key),
            (),
            7,
        )
        .expect("the node starts"),
    )
}

/// Every datagram the node wants sent to the gateway now.
fn to_gateway(node: &mut Member) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut b = [0u8; 2048];
    while let Some((to, n)) = node.poll_udp(&mut b) {
        if to == gw() {
            out.push(b[..n].to_vec());
        }
    }
    out
}

fn offered(node: &Member) -> Vec<SocketAddr> {
    let mut out = [local(); MAX_ADDRS];
    let n = node.connectivity().candidates(&mut out);
    out[..n].to_vec()
}

fn grant(nonce: [u8; 12], epoch: u32) -> Vec<u8> {
    let r = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime: 120,
        epoch,
        nonce,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: ext().port(),
        external_ip: ext().ip(),
    };
    let mut b = [0u8; 60];
    pcp::encode_response(&r, &mut b).unwrap();
    b.to_vec()
}

#[test]
fn a_mapping_leads_the_offered_addresses_until_it_is_released() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            node.set_local(&[local()]);
            let now = SEC;
            assert!(
                to_gateway(&mut node).is_empty(),
                "nothing is asked before the host turns it on"
            );
            assert!(node.port_mapping_done());
            node.start_port_mapping(now, Some(gw().ip()), local(), 120);
            let asked = to_gateway(&mut node);
            assert_eq!(asked.len(), 1);
            let req = pcp::decode_request(&asked[0]).unwrap();
            assert_eq!((req.client, req.internal_port, req.lifetime), (local().ip(), 4433, 120));
            assert!(
                node.poll_timeout().is_some_and(|t| t <= now + SEC),
                "the retry is armed"
            );
            // the gateway's answer goes to the port-mapping client, not to the endpoint
            let mut g = grant(req.nonce, 7);
            node.handle_datagram(now, local(), gw(), &mut g);
            assert_eq!(node.port_mapping(), Some((ext(), Proto::Pcp)));
            assert_eq!(
                offered(&node).first(),
                Some(&ext()),
                "the mapping leads what the node offers"
            );
            assert!(offered(&node).contains(&local()));
            // half way through the lease the node renews
            node.handle_timeout(now + 60 * SEC);
            let renew = to_gateway(&mut node);
            assert_eq!(renew.len(), 1);
            assert_eq!(pcp::decode_request(&renew[0]).unwrap().nonce, req.nonce);
            let mut g = grant(req.nonce, 67);
            node.handle_datagram(now + 60 * SEC, local(), gw(), &mut g);
            assert_eq!(node.port_mapping(), Some((ext(), Proto::Pcp)));
            // stop: the mapping is no longer offered and its release goes out
            node.stop_port_mapping(now + 70 * SEC);
            assert_eq!(node.port_mapping(), None);
            assert!(!offered(&node).contains(&ext()));
            assert!(!node.port_mapping_done(), "the release is not sent yet");
            let release = to_gateway(&mut node);
            assert_eq!(release.len(), 1);
            assert_eq!(pcp::decode_request(&release[0]).unwrap().lifetime, 0);
            assert!(node.port_mapping_done());
        })
        .unwrap()
        .join()
        .unwrap();
}
