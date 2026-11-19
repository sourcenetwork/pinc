//! Trace generation for the node's port-mapping client: a real node (the member of `node_portmap.rs`, built with the
//! `trace` feature) driven through starts, stops, restarts, the gateway's answers, HTTP answers and timeouts, at times
//! up to `u64::MAX`, recorded as ndjson (`node_portmap.ndjson`) for the TLA+ trace check (`TraceNodePortMap.tla`).
//!
//! After every call one line carries the view of the probe `Node::pm_view`: whether the host turned port mapping on,
//! whether the client has its nonce, the address it holds, the one the connectivity client was given, the one that
//! client holds, the retiring slots taken, the release overflows, whether the client is halted, whether it arms a
//! timer, the failed draws of the nonce, and how many datagrams the call gave the gateway (only a poll drains them).
//! Addresses are small numbers assigned in the order first seen, 0 for none.
//!
//! Runs: script A is the specification's boundary script (six starts, each polled and answered, a stop, the releases
//! answered, a timeout at the maximum); script A2 starts six times without a poll in between, so that the retiring
//! queue fills and overflows, then polls (the four releases first, then the new client's request), answers and stops;
//! and 40 seeded runs of 80 calls. Each run is a fresh node and starts with the view of a node never started.
//!
//! The test checks without the model, after every call: the connectivity client holds the address the port-mapping
//! client holds when the host turned it on, and none (no timer) when it did not; the queue is within 4; the overflow
//! count never decreases and grows by at most one, only on a start that finds the queue full before and after; a poll
//! with no port mapping before and after sends nothing; a halted client with no start starts no client. Script A2
//! ends with an overflow, else it did not fill the queue.
//!
//! The trace spec compares each line with the one before it, runs included: a run that ends with an overflow count
//! above 0 cannot be followed by the first line of another (the count of a new node is 0). So the file holds the runs
//! that end with no overflow first and script A2 last; a seeded run that ends with an overflow is run and checked but
//! not recorded (the number is printed). Script A is placed by the same rule.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::cognitive_complexity,
    missing_docs,
    clippy::single_match_else
)]

use std::collections::VecDeque;
use std::fmt::Write as _;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::ops::Range;

use pinc_broadcast::Limits;
use pinc_connect::client::{Config as ConnCfg, Port};
use pinc_core::{
    Command, CommandError, Event, Events, IfaceEvent, IfaceId, NodeStats, Reply, SendState, SessionId, SessionStats,
    TraceRecord, Transmit, Value,
};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, NodeId};
use pinc_node::{Config as NodeConfig, Ep, HUB_ALPN, Node, PmView};
use pinc_portmap::pcp;
use pinc_security::{Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_tests::{Caps, SplitMix64};
use pinc_transport::stream::{NoSource, StreamId};

/// An endpoint that hands out scripted events and accepts every command with an empty reply (the one of
/// `node_portmap.rs`).
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

/// The most stopped clients whose release waits (`RETIRING`, `portmap.rs`).
const RETIRING: usize = 4;

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
    let prov = Caps(pinc_crypto::Software, true);
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
        map_keys: pinc_tests::id_key(0x5eed),
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

/// The gateway's answer to the request with `nonce`: a grant of `lifetime` seconds.
fn answer_of(nonce: [u8; 12], epoch: u32, lifetime: u32) -> Vec<u8> {
    let r = pcp::Response::Map {
        result: pcp::SUCCESS,
        lifetime,
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

fn grant(nonce: [u8; 12], epoch: u32) -> Vec<u8> {
    answer_of(nonce, epoch, 120)
}

/// The gateway's answer to a release: the grant with a lifetime of 0.
fn release_ack(nonce: [u8; 12]) -> Vec<u8> {
    answer_of(nonce, 7, 0)
}

/// Hand `node` a datagram from `from` at `now`.
fn deliver(node: &mut Member, now: u64, from: SocketAddr, mut d: Vec<u8>) {
    node.handle_datagram(now, local(), from, &mut d);
}

/// One run: a fresh node, the lines it recorded, and what is known of its calls.
struct Run {
    node: Box<Member>,
    out: String,
    prev: PmView,
    addrs: Vec<SocketAddr>,
    /// The nonces seen in the node's requests, in the order seen (one per client).
    nonces: Vec<[u8; 12]>,
}

impl Run {
    /// A node built and never started, with its first line.
    fn new() -> Self {
        let node = member();
        let prev = node.pm_view();
        let mut r = Self {
            node,
            out: String::new(),
            prev,
            addrs: Vec::new(),
            nonces: Vec::new(),
        };
        r.write("init", 0, prev);
        r
    }

    /// The number of an address: from 1 in the order first seen, 0 for none.
    fn num(&mut self, a: Option<SocketAddr>) -> usize {
        let Some(a) = a else { return 0 };
        match self.addrs.iter().position(|x| *x == a) {
            Some(i) => i + 1,
            None => {
                self.addrs.push(a);
                self.addrs.len()
            }
        }
    }

    fn write(&mut self, call: &str, sent: usize, v: PmView) {
        let (held, given, conn) = (self.num(v.held), self.num(v.given), self.num(v.conn));
        let _ = writeln!(
            self.out,
            r#"{{"t":"pm","call":"{call}","v":{{"on":{},"cli":{},"held":{held},"given":{given},"conn":{conn},"ret":{},"ovf":{},"halted":{},"dl":{},"nf":{},"sent":{sent}}}}}"#,
            v.on, v.client, v.retiring, v.overflows, v.halted, v.timer, v.nonce_failures
        );
    }

    /// The checks of a call, then its line.
    fn record(&mut self, call: &str, sent: usize) {
        let (a, b) = (self.prev, self.node.pm_view());
        if b.on {
            assert_eq!(
                (b.conn, b.given),
                (b.held, b.held),
                "{call}: the connectivity client does not hold the address"
            );
        } else {
            assert!(
                b.conn.is_none() && !b.timer,
                "{call}: no port mapping, yet an address or a timer"
            );
        }
        assert!(b.retiring <= RETIRING, "{call}: the retiring queue passed its bound");
        if a.on {
            assert!(
                b.overflows == a.overflows || b.overflows == a.overflows + 1,
                "{call}: the overflow count moved by other than 0 or 1"
            );
        }
        if b.overflows > a.overflows {
            assert!(
                call == "start" && a.retiring == RETIRING && b.retiring == RETIRING,
                "{call}: an overflow with no start on a full queue"
            );
        }
        if call == "poll" && !a.on && !b.on {
            assert_eq!(sent, 0, "a poll with no port mapping sent something");
        }
        if a.halted && b.halted && call != "start" {
            assert!(!b.client, "{call}: a halted client started");
        }
        self.write(call, sent, b);
        self.prev = b;
    }

    fn start(&mut self, now: u64) {
        self.node.start_port_mapping(now, Some(gw().ip()), local(), 120);
        self.record("start", 0);
    }

    fn stop(&mut self, now: u64) {
        self.node.stop_port_mapping(now);
        self.record("stop", 0);
    }

    fn restart(&mut self, now: u64) {
        self.node.address_changed(now);
        self.record("restart", 0);
    }

    fn answer(&mut self, now: u64, d: Vec<u8>) {
        deliver(&mut self.node, now, gw(), d);
        self.record("answer", 0);
    }

    fn http(&mut self, now: u64) {
        self.node.handle_http(now, None);
        self.record("http", 0);
    }

    fn timeout(&mut self, now: u64) {
        self.node.handle_timeout(now);
        self.record("timeout", 0);
    }

    /// Drains the datagrams to the gateway and keeps the nonces of their requests.
    fn poll(&mut self) -> usize {
        let sent = to_gateway(&mut self.node);
        for req in sent.iter().filter_map(|d| pcp::decode_request(d).ok()) {
            if !self.nonces.contains(&req.nonce) {
                self.nonces.push(req.nonce);
            }
        }
        self.record("poll", sent.len());
        sent.len()
    }

    /// The newest client's nonce.
    fn newest(&self) -> [u8; 12] {
        *self.nonces.last().unwrap()
    }

    /// Answers every release with the gateway's acknowledgement, for each nonce seen.
    fn ack_all(&mut self, now: u64) {
        for n in self.nonces.clone() {
            self.answer(now, release_ack(n));
        }
    }
}

/// The specification's boundary script.
fn script_a() -> Run {
    let mut r = Run::new();
    let now = SEC;
    r.poll();
    r.start(now);
    r.poll();
    let first = r.nonces[0];
    r.answer(now, grant(first, 7));
    for _ in 0..5 {
        r.start(now);
        r.poll();
        let n = r.newest();
        r.answer(now, grant(n, 7));
    }
    r.stop(now);
    r.poll();
    r.ack_all(now);
    r.poll();
    r.timeout(u64::MAX);
    r
}

/// Six starts with no poll between, so that the stopped clients' releases wait and the queue fills and overflows.
fn script_a2() -> Run {
    let mut r = Run::new();
    let now = SEC;
    for _ in 0..=RETIRING + 1 {
        r.start(now);
    }
    assert!(
        r.prev.overflows >= 1,
        "six starts with no poll did not overflow the retiring queue"
    );
    assert_eq!(r.prev.retiring, RETIRING);
    r.poll();
    let n = r.newest();
    r.answer(now, grant(n, 7));
    r.stop(now);
    r.poll();
    r.ack_all(now);
    r.poll();
    r.timeout(u64::MAX);
    r
}

/// A seeded run of 80 calls.
fn seeded(seed: u64) -> Run {
    let mut rng = SplitMix64::new(seed);
    let mut r = Run::new();
    let mut now = SEC;
    for _ in 0..80 {
        match rng.next_u64() % 20 {
            0 => now = u64::MAX,
            1..=10 => {}
            _ => now = now.saturating_add(SEC),
        }
        match rng.next_u64() % 16 {
            0 | 1 => r.start(now),
            2 => r.stop(now),
            3 => r.restart(now),
            4..=7 => {
                let nonce = if r.nonces.is_empty() || rng.next_u64().is_multiple_of(8) {
                    [0xEE; 12]
                } else {
                    r.nonces[(rng.next_u64() % r.nonces.len() as u64) as usize]
                };
                let d = if rng.next_u64().is_multiple_of(2) {
                    grant(nonce, 7)
                } else {
                    release_ack(nonce)
                };
                r.answer(now, d);
            }
            8 => r.http(now),
            9..=12 => {
                r.poll();
            }
            _ => r.timeout(now),
        }
    }
    r
}

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn the_port_mapping_client_matches_the_model() {
    let (out, skipped) = big(|| {
        let (mut quiet, mut skipped) = (String::new(), 0u32);
        let runs = std::iter::once(script_a()).chain((1..=40u64).map(seeded));
        for r in runs {
            if r.prev.overflows == 0 {
                quiet.push_str(&r.out);
            } else {
                skipped += 1;
            }
        }
        quiet.push_str(&script_a2().out);
        (quiet, skipped)
    });
    if skipped > 0 {
        eprintln!("trace_node_portmap: {skipped} runs ended with an overflow and are not recorded");
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("node_portmap.ndjson"), &out).unwrap();
    }
}
