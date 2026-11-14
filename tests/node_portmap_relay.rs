//! The port-mapping client on a node with a real relay that reports the node's reflexive address: what the node
//! publishes and offers while the gateway's answers are spoofed, when the client starts again, and when the link changes.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::type_complexity,
    dead_code,
    missing_docs
)]

mod connect_common;
mod connect_rig;

use std::collections::VecDeque;
use std::net::SocketAddr;
use std::ops::Range;

use connect_common::{Collect, Rec, ed, id};
use connect_rig::{R, RELAY_UDP};
use vinc_broadcast::Limits;
use vinc_connect::client::{Config as ConnCfg, Port, RelayCfg};
use vinc_connect::record::MAX_ADDRS;
use vinc_connect::record::Reach;
use vinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use vinc_node::{Config as NodeConfig, Ep, HUB_ALPN, Node};
use vinc_portmap::{natpmp, pcp};
use vinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use vinc_tests::Caps;
use vinc_transport::stream::{NoSource, StreamId};

#[derive(Default)]
struct Script {
    events: VecDeque<Event>,
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

fn a(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

fn local() -> SocketAddr {
    a("192.168.1.5:4433")
}

fn gw() -> SocketAddr {
    a("192.168.1.1:5351")
}

fn ru() -> SocketAddr {
    RELAY_UDP.parse().unwrap()
}

struct World {
    node: Box<Member>,
    relay: Box<R>,
    sink: Collect,
    /// Datagrams the node sent to the gateway, in order.
    to_gw: Vec<Vec<u8>>,
}

fn world() -> World {
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
    let relay_kp = ed(0x77);
    let relay_id = id(&relay_kp);
    let mut relays = [None; 4];
    relays[0] = Some(RelayCfg {
        id: relay_id,
        udp: Some(ru()),
        tcp: None,
        ws: None,
    });
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
        is_hub: false,
        version: 1,
        alpn: HUB_ALPN,
        limits: Limits::default(),
        wall_ms: 1_700_000_000_000,
        local: local(),
        trace: false,
    };
    let key = Keypair::from_seed(alg, &[0x12; 32]).unwrap();
    let mut node = Box::new(
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
    );
    node.set_local(&[local()]);
    World {
        node,
        relay: Box::new(R::new(vinc_connect::relay::Config::new(relay_id, 3))),
        sink: Collect::default(),
        to_gw: Vec::new(),
    }
}

impl World {
    /// Drain what the node sends: the gateway's datagrams are kept, a relay probe is answered as seen from `src`.
    /// Returns whether a probe was answered.
    fn drain(&mut self, now: u64, src: Option<SocketAddr>) -> bool {
        let mut answered = false;
        let mut b = [0u8; 2048];
        while let Some((to, n)) = self.node.poll_udp(&mut b) {
            if to == gw() {
                self.to_gw.push(b[..n].to_vec());
            } else if to == ru()
                && let Some(src) = src
                && self.relay.datagram(now, src, None, &b[..n], &mut self.sink).is_ok()
            {
                for e in self.sink.effects() {
                    if let Rec::Udp(_, mut d) = e {
                        self.node.handle_datagram(now, local(), ru(), &mut d);
                        answered = true;
                    }
                }
            }
        }
        answered
    }

    /// Run until the relay answered a probe, the node seen at `src`. Returns the time.
    fn discover(&mut self, mut now: u64, src: &str) -> u64 {
        let src = a(src);
        for _ in 0..400 {
            if self.drain(now, Some(src)) {
                return now;
            }
            now = self.node.poll_timeout().map_or(now + SEC, |t| t.max(now + 1));
            self.node.handle_timeout(now);
        }
        panic!("no probe was answered");
    }

    fn deliver(&mut self, now: u64, from: SocketAddr, mut d: Vec<u8>) {
        self.node.handle_datagram(now, local(), from, &mut d);
        self.drain(now, None);
    }

    fn offered(&self) -> Vec<SocketAddr> {
        let mut out = [local(); MAX_ADDRS];
        let n = self.node.connectivity().candidates(&mut out);
        out[..n].to_vec()
    }

    fn last_pcp_nonce(&self) -> [u8; 12] {
        self.to_gw
            .iter()
            .rev()
            .find_map(|b| pcp::decode_request(b).ok())
            .map(|r| r.nonce)
            .expect("a PCP request")
    }
}

fn nat(r: natpmp::Response) -> Vec<u8> {
    let mut b = [0u8; 16];
    let n = natpmp::encode_response(&r, &mut b).unwrap();
    b[..n].to_vec()
}

fn grant(nonce: [u8; 12], epoch: u32, ext: SocketAddr) -> Vec<u8> {
    let r = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime: 7200,
        epoch,
        nonce,
        protocol: pcp::UDP,
        internal_port: 4433,
        external_port: ext.port(),
        external_ip: ext.ip(),
    };
    let mut b = [0u8; 60];
    pcp::encode_response(&r, &mut b).unwrap();
    b.to_vec()
}

fn announce(epoch: u32) -> Vec<u8> {
    let mut b = [0u8; 24];
    let n = pcp::encode_response(
        &pcp::Response::Header {
            opcode: pcp::OP_ANNOUNCE,
            result: 0,
            lifetime: 0,
            epoch,
        },
        &mut b,
    )
    .unwrap();
    b[..n].to_vec()
}

fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

fn live() -> (World, u64, SocketAddr) {
    let mut w = world();
    let ext = a("198.51.100.5:4433");
    w.node.start_port_mapping(SEC, Some(gw().ip()), local(), 7200);
    w.drain(SEC, None);
    let nonce = w.last_pcp_nonce();
    w.deliver(SEC, gw(), grant(nonce, 5000, ext));
    assert_eq!(w.offered(), [local()], "held, no relay has reported yet");
    let now = w.discover(SEC, "198.51.100.5:20000");
    assert_eq!(
        w.offered().first(),
        Some(&ext),
        "published once the relay saw the node at its IP"
    );
    assert_eq!(w.node.connectivity().class(), Some(Reach::PortMapped));
    (w, now, ext)
}

#[test]
fn spoofed_announces_change_neither_what_is_offered_nor_the_class() {
    big(|| {
        let (mut w, mut now, ext) = live();
        let nonce = w.last_pcp_nonce();
        let before = w.to_gw.len();
        for i in 0..20u32 {
            now += SEC / 100;
            w.deliver(now, gw(), announce(0));
            assert_eq!(w.offered().first(), Some(&ext), "announce {i} withdrew the address");
            assert_eq!(
                w.node.connectivity().class(),
                Some(Reach::PortMapped),
                "announce {i} changed the class"
            );
            w.deliver(now, gw(), grant(nonce, 5001 + i, ext));
        }
        let asked = w.to_gw.len() - before;
        assert!(asked <= 20, "{asked} requests for 20 announces");
        assert_eq!(w.node.port_mapping().map(|(a, _)| a), Some(ext));
    });
}

#[test]
fn a_second_start_withdraws_what_the_first_published_and_releases_it() {
    big(|| {
        let (mut w, now, ext) = live();
        let before = w.to_gw.len();
        w.node.start_port_mapping(now + SEC, Some(gw().ip()), local(), 7200);
        w.drain(now + SEC, None);
        assert_eq!(w.node.port_mapping(), None);
        assert!(!w.offered().contains(&ext), "the old address is still offered");
        assert_ne!(
            w.node.connectivity().class(),
            Some(Reach::PortMapped),
            "the class is still port-mapped"
        );
        let sent: Vec<_> = w.to_gw[before..]
            .iter()
            .filter_map(|b| pcp::decode_request(b).ok())
            .collect();
        assert!(
            sent.iter().any(|r| r.lifetime == 0 && r.external_ip == ext.ip()),
            "no release for the old mapping left: {sent:?}"
        );
        // stop: nothing is offered and nothing comes back later
        w.node.stop_port_mapping(now + 2 * SEC);
        w.drain(now + 2 * SEC, None);
        assert!(!w.offered().contains(&ext));
        let later = now + 600 * SEC;
        w.node.handle_timeout(later);
        w.drain(later, None);
        assert!(!w.offered().contains(&ext), "600 s later");
        assert!(w.node.port_mapping_done());
    });
}

#[test]
fn a_changed_address_withdraws_the_class_with_the_address() {
    big(|| {
        let (mut w, now, _) = live();
        w.node.address_changed(now + SEC);
        w.drain(now + SEC, None);
        assert_eq!(w.offered(), [local()]);
        assert_ne!(
            w.node.connectivity().class(),
            Some(Reach::PortMapped),
            "the class stays port-mapped after the address was withdrawn"
        );
    });
}

#[test]
fn an_endpoint_without_a_client_does_not_clear_the_cached_deadline() {
    big(|| {
        let mut w = world();
        let _ = w.node.poll_timeout();
        assert!(w.node.deadline_cached());
        let mut b = [0u8; 2048];
        assert!(w.node.poll_http(&mut b).is_none());
        assert!(!w.node.has_port_mapping());
        assert!(
            w.node.deadline_cached(),
            "poll_http cleared the cached deadline of a node with no client"
        );
    });
}
