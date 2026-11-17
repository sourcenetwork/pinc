//! The node's port-mapping client: the host turns it on, the node sends the gateway's requests from its own socket,
//! takes the gateway's answers before the endpoint sees them, holds the mapped address and offers it only once a relay
//! saw the node at its IP, renews, and releases the mapping when told to stop.
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
use vinc_portmap::{Proto, natpmp, pcp};
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
        map_keys: vinc_tests::id_key(0x5eed),
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
fn a_mapping_no_relay_saw_is_held_and_not_offered_until_it_is_released() {
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
            assert!(
                !offered(&node).contains(&ext()),
                "a mapping no relay vouched for is held and not offered"
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

fn nat(r: natpmp::Response) -> Vec<u8> {
    let mut b = [0u8; 16];
    let n = natpmp::encode_response(&r, &mut b).unwrap();
    b[..n].to_vec()
}

/// Hand `node` a datagram from `from` at `now`.
fn deliver(node: &mut Member, now: u64, from: SocketAddr, mut d: Vec<u8>) {
    node.handle_datagram(now, local(), from, &mut d);
}

#[test]
fn an_address_a_spoofed_gateway_names_is_held_and_never_offered() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            node.set_local(&[local()]);
            node.start_port_mapping(SEC, Some(gw().ip()), local(), 120);
            to_gateway(&mut node);
            // a NAT-PMP error during the PCP step, then an address and a mapping: nothing a nonce could tell apart
            deliver(
                &mut node,
                SEC,
                gw(),
                nat(natpmp::Response::Error {
                    opcode: 1,
                    result: 1,
                    epoch: 1,
                }),
            );
            let victim = Ipv4Addr::new(1, 2, 3, 4);
            deliver(
                &mut node,
                SEC,
                gw(),
                nat(natpmp::Response::Address {
                    result: 0,
                    epoch: 1,
                    ip: victim,
                }),
            );
            deliver(
                &mut node,
                SEC,
                gw(),
                nat(natpmp::Response::Map {
                    result: 0,
                    epoch: 1,
                    internal_port: 4433,
                    external_port: 53,
                    lifetime: 120,
                }),
            );
            let spoofed = SocketAddr::new(victim.into(), 53);
            assert_eq!(
                node.port_mapping(),
                Some((spoofed, Proto::NatPmp)),
                "the client holds what it was told"
            );
            assert_eq!(
                offered(&node),
                [local()],
                "no relay saw the node at {victim}: it is not offered"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn an_address_a_lan_host_names_over_upnp_is_held_and_never_offered() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            node.set_local(&[local()]);
            node.start_port_mapping(SEC, None, local(), 120);
            let host = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 77)), 1900);
            deliver(
                &mut node,
                SEC,
                host,
                b"HTTP/1.1 200 OK\r\nLOCATION: http://192.168.1.77:5000/d.xml\r\n\r\n".to_vec(),
            );
            let desc = b"HTTP/1.1 200 OK\r\n\r\n<service><serviceType>urn:schemas-upnp-org:service:WANIPConnection:1</serviceType><controlURL>/ctl</controlURL></service>";
            let answers: [&[u8]; 3] = [
                desc,
                b"HTTP/1.1 200 OK\r\n\r\n<NewExternalIPAddress>1.2.3.4</NewExternalIPAddress>",
                b"HTTP/1.1 200 OK\r\n\r\n<u:AddPortMappingResponse/>",
            ];
            for a in answers {
                let mut buf = [0u8; 2048];
                assert!(node.poll_http(&mut buf).is_some(), "the client asks");
                node.handle_http(SEC, Some(a));
            }
            let spoofed = SocketAddr::new(Ipv4Addr::new(1, 2, 3, 4).into(), 4433);
            assert_eq!(node.port_mapping(), Some((spoofed, Proto::Upnp)));
            assert_eq!(offered(&node), [local()], "no relay saw the node at 1.2.3.4: it is not offered");
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A node holding a PCP mapping at `T = 1 s`, its request drained; the request's nonce.
fn held_node() -> (Box<Member>, [u8; 12]) {
    let mut node = member();
    node.set_local(&[local()]);
    node.start_port_mapping(SEC, Some(gw().ip()), local(), 120);
    let req = pcp::decode_request(&to_gateway(&mut node)[0]).unwrap();
    deliver(&mut node, SEC, gw(), grant(req.nonce, 7));
    assert_eq!(node.port_mapping(), Some((ext(), Proto::Pcp)));
    (node, req.nonce)
}

#[test]
fn a_changed_address_withdraws_the_mapping_at_once_and_asks_again() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let (mut node, nonce) = held_node();
            node.address_changed(2 * SEC);
            assert_eq!(node.port_mapping(), None, "the old mapping is still held");
            let sent = to_gateway(&mut node);
            let asked: Vec<_> = sent.iter().map(|b| pcp::decode_request(b).unwrap()).collect();
            assert_eq!(asked.iter().map(|r| r.lifetime).collect::<Vec<_>>(), [0, 120]);
            assert!(asked.iter().all(|r| r.nonce == nonce));
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_resume_that_moved_withdraws_the_mapping_and_one_that_did_not_keeps_it() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let (mut node, _) = held_node();
            node.resume(2 * SEC, false);
            assert_eq!(node.port_mapping(), Some((ext(), Proto::Pcp)));
            node.resume(3 * SEC, true);
            assert_eq!(node.port_mapping(), None);
            assert_eq!(pcp::decode_request(&to_gateway(&mut node)[0]).unwrap().lifetime, 0);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn every_request_carries_a_nonce_that_was_drawn() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            let mut nonces = Vec::new();
            for i in 0..3u64 {
                node.start_port_mapping(SEC * (i + 1), Some(gw().ip()), local(), 120);
                // a start while one runs releases the request the old client had in flight first
                let asked: Vec<_> = to_gateway(&mut node)
                    .iter()
                    .map(|b| pcp::decode_request(b).unwrap())
                    .filter(|r| r.lifetime > 0)
                    .collect();
                assert_eq!(asked.len(), 1, "a request is out at once");
                nonces.push(asked[0].nonce);
            }
            assert!(
                nonces.iter().all(|n| *n != [0; 12]),
                "a request went out with an all-zero nonce"
            );
            assert!(
                nonces[0] != nonces[1] && nonces[1] != nonces[2],
                "the nonce repeats: {nonces:?}"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn the_node_exposes_what_the_client_dropped() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            assert_eq!(
                node.port_mapping_stats(),
                vinc_node::PortMapStats::default(),
                "nothing before it is on"
            );
            node.start_port_mapping(SEC, Some(gw().ip()), local(), 120);
            let req = pcp::decode_request(&to_gateway(&mut node)[0]).unwrap();
            // an answer from the gateway with another nonce is dropped and counted
            deliver(&mut node, SEC, gw(), grant([9; 12], 7));
            assert_eq!(node.port_mapping(), None);
            assert_eq!(node.port_mapping_stats().client.wrong_nonce, 1);
            assert_eq!(node.port_mapping_stats().nonce_failures, 0);
            // one with its own nonce is held and counts nothing more
            deliver(&mut node, SEC, gw(), grant(req.nonce, 7));
            assert_eq!(node.port_mapping_stats().client.wrong_nonce, 1);
            assert!(node.port_mapping().is_some());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn a_third_start_does_not_drop_the_release_of_the_first() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            node.set_local(&[local()]);
            for i in 0..3u64 {
                node.start_port_mapping(SEC * (i + 1), Some(gw().ip()), local(), 120);
            }
            // nothing was polled between the starts: two releases wait, and the third client's request
            let asked: Vec<_> = to_gateway(&mut node)
                .iter()
                .map(|b| pcp::decode_request(b).unwrap())
                .collect();
            let releases: std::collections::BTreeSet<[u8; 12]> =
                asked.iter().filter(|r| r.lifetime == 0).map(|r| r.nonce).collect();
            assert_eq!(releases.len(), 2, "the releases of the first two clients: {asked:?}");
            assert_eq!(asked.iter().filter(|r| r.lifetime > 0).count(), 1);
            assert_eq!(node.port_mapping_stats().release_overflows, 0);
            node.stop_port_mapping(5 * SEC);
            to_gateway(&mut node);
            assert!(node.port_mapping_done(), "done once every release was sent");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn more_unsent_releases_than_the_queue_holds_are_counted() {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(|| {
            let mut node = member();
            node.set_local(&[local()]);
            for i in 0..6u64 {
                node.start_port_mapping(SEC * (i + 1), Some(gw().ip()), local(), 120);
            }
            // five clients were stopped unsent; the queue holds four
            let asked: Vec<_> = to_gateway(&mut node)
                .iter()
                .map(|b| pcp::decode_request(b).unwrap())
                .collect();
            assert_eq!(asked.iter().filter(|r| r.lifetime == 0).count(), 4);
            assert_eq!(node.port_mapping_stats().release_overflows, 1);
        })
        .unwrap()
        .join()
        .unwrap();
}
