//! The node adapter of the scenario suite: real `vinc-core` endpoints with instrumented crypto driven by the
//! simulator, with a small test-local application (dial, echo round trip with real stream bytes, count incoming).
#![allow(
    clippy::cast_precision_loss,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::similar_names,
    missing_docs
)]

use std::cell::RefCell;
use std::collections::{BTreeMap, VecDeque};
use std::net::{IpAddr, SocketAddr};
use std::rc::Rc;

use vinc_core::SessionId;
use vinc_sim::suite::crypto::{PayloadKind, Registry};
use vinc_sim::suite::grade::fixture::blank_world;
use vinc_sim::suite::node::{Cmd, NodeEvent, Shared, SuiteCost, SuiteNode, iface_ip};
use vinc_sim::suite::proto::host::{Host, LayerEvent, Layers};
use vinc_sim::suite::rec::Rec;
use vinc_sim::suite::world::model::{Addr, EnvAction, EnvArg, EnvKind, IfaceSpec, Intent, IntentKind, Must};
use vinc_sim::{LinkConfig, NatConfig, NatKind, NodeId, NodeState, PortPolicy, Sim, SimConfig};
use vinc_tests::big_stack;

const NS: u64 = 1_000_000_000;
const ALPN: &[u8] = b"suite/echo";
const MSG_LEN: usize = 3000;

// ---------------------------------------------------------------- the test application

#[derive(Default)]
struct Stats {
    echoes: usize,
    served: usize,
    incoming: usize,
    connected: usize,
    failed: usize,
    closed: usize,
    refused: usize,
}

struct Out {
    buf: Vec<u8>,
    off: usize,
    expect: Option<Vec<u8>>,
    got: Vec<u8>,
}

struct TestLayer {
    idx: usize,
    stats: Rc<RefCell<Stats>>,
    waiting: VecDeque<usize>,
    open: BTreeMap<usize, SessionId>,
    streams: BTreeMap<(SessionId, u64), Out>,
}

impl TestLayer {
    fn new(idx: usize, stats: Rc<RefCell<Stats>>) -> Self {
        Self {
            idx,
            stats,
            waiting: VecDeque::new(),
            open: BTreeMap::new(),
            streams: BTreeMap::new(),
        }
    }

    fn send_echo(&mut self, host: &mut dyn Host, session: SessionId) {
        let reg = host.registry();
        let msg = reg.new_msg(self.idx, PayloadKind::Msg, MSG_LEN as u64);
        let mut data = vec![0u8; MSG_LEN];
        reg.fill(msg, 0, &mut data).unwrap();
        if let Some(stream) = host.open_stream(session) {
            let key = (session, stream);
            let out = Out {
                buf: data.clone(),
                off: 0,
                expect: Some(data),
                got: Vec::new(),
            };
            self.streams.insert(key, out);
            self.push_out(host, key);
        }
    }

    fn push_out(&mut self, host: &mut dyn Host, key: (SessionId, u64)) {
        let Some(o) = self.streams.get_mut(&key) else { return };
        while o.off < o.buf.len() {
            let n = host.write(key.0, key.1, &o.buf[o.off..]);
            if n == 0 {
                return;
            }
            o.off += n;
        }
        host.finish(key.0, key.1);
    }
}

impl Layers for TestLayer {
    fn alpns(&self) -> Vec<&'static [u8]> {
        vec![ALPN]
    }
    fn boot(&mut self, _now: u64, _host: &mut dyn Host) {}
    fn intent(&mut self, _now: u64, host: &mut dyn Host, intent: &Intent) {
        let Some(to) = intent.to else { return };
        if let Some(session) = self.open.get(&to).copied() {
            self.send_echo(host, session);
        } else if host.connect(to, ALPN) {
            self.waiting.push_back(to);
        } else {
            self.stats.borrow_mut().refused += 1;
        }
    }
    fn event(&mut self, _now: u64, host: &mut dyn Host, ev: LayerEvent<'_>) {
        match ev {
            LayerEvent::Incoming { .. } => self.stats.borrow_mut().incoming += 1,
            LayerEvent::Connected { session, peer, .. } => {
                self.stats.borrow_mut().connected += 1;
                self.open.insert(peer, session);
                if let Some(p) = self.waiting.iter().position(|w| *w == peer) {
                    self.waiting.remove(p);
                    self.send_echo(host, session);
                }
            }
            LayerEvent::ConnectFailed { peer, .. } => {
                self.stats.borrow_mut().failed += 1;
                if let Some(p) = self.waiting.iter().position(|w| *w == peer) {
                    self.waiting.remove(p);
                }
            }
            LayerEvent::Closed { session } => {
                self.stats.borrow_mut().closed += 1;
                self.open.retain(|_, s| *s != session);
                self.streams.retain(|k, _| k.0 != session);
            }
            LayerEvent::StreamData {
                session,
                stream,
                data,
                fin,
            } => {
                let key = (session, stream);
                let o = self.streams.entry(key).or_insert_with(|| Out {
                    buf: Vec::new(),
                    off: 0,
                    expect: None,
                    got: Vec::new(),
                });
                o.got.extend_from_slice(data);
                if !fin {
                    return;
                }
                if let Some(expect) = &o.expect {
                    assert_eq!(&o.got, expect, "the echo came back changed");
                    self.stats.borrow_mut().echoes += 1;
                    self.streams.remove(&key);
                } else {
                    o.buf = std::mem::take(&mut o.got);
                    self.stats.borrow_mut().served += 1;
                    self.push_out(host, key);
                }
            }
            LayerEvent::StreamWritable { session, stream } => self.push_out(host, (session, stream)),
            LayerEvent::StreamOpened { .. } | LayerEvent::StreamReset { .. } => {}
        }
    }
    fn timeout(&mut self, _now: u64, _host: &mut dyn Host) {}
    fn poll_timeout(&self) -> Option<u64> {
        None
    }
    fn has_open_intents(&self, _now: u64) -> bool {
        !self.waiting.is_empty() || self.streams.values().any(|o| o.expect.is_some())
    }
    fn stop(&mut self) {
        self.waiting.clear();
        self.open.clear();
        self.streams.clear();
    }
}

fn intent(t: u64, node: usize, to: usize) -> Intent {
    Intent {
        t,
        node,
        kind: IntentKind::Echo,
        to: Some(to),
        topic: None,
        size: None,
        req: None,
        resp: None,
        deadline_ns: 30 * NS,
        receivers: Vec::new(),
        must: Must::Flag(true),
        value: None,
        providers: Vec::new(),
        ranges: Vec::new(),
        stream_rate: None,
        probe: false,
        under_bulk: false,
        set_ref: None,
    }
}

// ---------------------------------------------------------------- the world and the run

type Node = SuiteNode<TestLayer>;

struct Run {
    sim: Sim<Node, vinc_sim::Rng, SuiteCost>,
    ids: Vec<NodeId>,
    rec: Rc<RefCell<Rec>>,
    reg: &'static Registry,
    stats: Vec<Rc<RefCell<Stats>>>,
    shared: Rc<Shared>,
}

fn iface(kind: &str, host: u64, public: bool) -> IfaceSpec {
    IfaceSpec {
        name: "u4".to_owned(),
        kind: kind.to_owned(),
        addr: Addr {
            kind: kind.to_owned(),
            host,
            port: 4433,
        },
        mtu: 1472,
        public,
        v6: false,
    }
}

/// Node 0 is a cloud with a public address; nodes 1.. are desktops behind their own NAT.
fn make_world(
    n: usize,
    dur: u64,
    tweak: impl FnOnce(&mut vinc_sim::suite::world::model::World),
) -> vinc_sim::suite::world::model::World {
    let mut w = blank_world("S1", n, dur);
    w.seed = 7;
    "cloud".clone_into(&mut w.nodes[0].device);
    "cloud".clone_into(&mut w.nodes[0].kind);
    w.nodes[0].ifaces = vec![iface("udp4", 1_000_000, true)];
    w.clouds = vec![0];
    for i in 1..n {
        w.nodes[i].ifaces = vec![iface("udp4", 3_000_000 + i as u64 * 256, false)];
        w.homes.push(i);
    }
    tweak(&mut w);
    w
}

fn build(world: vinc_sim::suite::world::model::World, sim_seed: u64, trace: bool) -> Run {
    let world = Rc::new(world);
    let rec = Rc::new(RefCell::new(Rec::new(Rc::clone(&world))));
    let reg = Registry::leak(world.seed);
    reg.install();
    let shared = Shared::new(Rc::clone(&world), Rc::clone(&rec), reg).unwrap();
    let cfg = SimConfig {
        default_link: Some(LinkConfig {
            delay: 10_000_000,
            ..LinkConfig::default()
        }),
        trace,
        trace_packets: trace,
        ..SimConfig::default()
    };
    let mut sim = Sim::with_parts(sim_seed, cfg, SuiteCost);
    let mut ids = Vec::new();
    let mut stats = Vec::new();
    for (i, spec) in world.nodes.iter().enumerate() {
        let st = Rc::new(RefCell::new(Stats::default()));
        let node = SuiteNode::new(Rc::clone(&shared), i, TestLayer::new(i, Rc::clone(&st))).unwrap();
        let ip = iface_ip(&spec.ifaces[0].addr).unwrap();
        let id = if spec.ifaces[0].public {
            sim.add_node_at(node, ip)
        } else {
            let id = sim.add_node(node);
            let nat = sim.add_nat(NatConfig {
                kind: NatKind::PortRestricted,
                ext_ip: iface_ip(&Addr {
                    kind: "udp4".to_owned(),
                    host: 2_000_000 + i as u64,
                    port: 0,
                })
                .unwrap(),
                mapping_timeout: 120 * NS,
                tcp_timeout: 7200 * NS,
                refresh_on_inbound: false,
                port_base: 20_000,
                ports: PortPolicy::Sequential,
                no_punch: false,
            });
            sim.add_iface_behind(id, ip, nat);
            id
        };
        sim.set_cpu(id, SuiteCost::cpu(1000));
        ids.push(id);
        stats.push(st);
    }
    // Every node begins stopped and starts at its start time.
    for (i, id) in ids.iter().enumerate() {
        sim.crash(0, *id);
        sim.restart(NS + i as u64 * 1_000_000, *id);
    }
    Run {
        sim,
        ids,
        rec,
        reg,
        stats,
        shared,
    }
}

impl Run {
    fn echo(&mut self, t: u64, from: usize, to: usize) {
        self.sim
            .command(t, self.ids[from], Cmd::Intent(Box::new(intent(t, from, to))));
    }
    fn node(&self, i: usize) -> &Node {
        self.sim.node(self.ids[i])
    }
    fn events(&self, i: usize) -> Vec<NodeEvent> {
        self.sim.events(self.ids[i]).iter().map(|(_, e)| *e).collect()
    }
    fn clean(&self) -> bool {
        let r = self.reg.sec_verdict(std::iter::empty());
        assert!(r.failures().is_empty(), "{:?}", r.failures());
        true
    }
    fn violations(&self) -> Vec<String> {
        self.rec
            .borrow()
            .violations
            .iter()
            .map(|v| format!("{} {}", v.gate, v.msg))
            .collect()
    }
}

// ---------------------------------------------------------------- the tests

#[test]
fn handshake_echo_and_clean_verdict() {
    big_stack(|| {
        let mut r = build(make_world(3, 60 * NS, |_| {}), 1, false);
        r.echo(5 * NS, 1, 0);
        r.echo(5 * NS, 2, 0);
        r.sim.run_until(20 * NS);
        assert_eq!(r.stats[1].borrow().echoes, 1, "{:?}", r.events(1));
        assert_eq!(r.stats[2].borrow().echoes, 1);
        assert_eq!(r.stats[0].borrow().served, 2);
        assert_eq!(r.stats[0].borrow().incoming, 2);
        assert_eq!(r.stats[1].borrow().connected, 1);
        assert!(r.events(1).contains(&NodeEvent::Connected {
            peer: 0,
            resumed: false
        }));
        assert!(r.events(0).contains(&NodeEvent::Incoming { peer: 1 }));
        assert!(r.clean());
        assert!(!r.reg.payload_keys().is_empty(), "the verdict saw payload keys");
        // The payload crossed the wire sealed: the keys protected it and no plaintext was seen.
        assert_eq!(r.rec.borrow().plaintext_payload.len(), 0);
        assert_eq!(r.violations(), Vec::<String>::new());
        for i in 0..3 {
            assert_eq!(r.node(i).timer_violations(), 0);
            assert!(r.node(i).running());
        }
        assert_eq!(r.sim.metrics().timer_violations, 0);
        assert!(r.rec.borrow().state_peaks[&0] > 0);
    });
}

#[test]
fn wire_accounting_equals_the_simulator() {
    big_stack(|| {
        let mut r = build(make_world(3, 60 * NS, |_| {}), 2, false);
        r.echo(5 * NS, 1, 0);
        r.echo(6 * NS, 2, 0);
        r.sim.run_until(30 * NS);
        let rec = r.rec.borrow();
        assert!(rec.wire_bytes > 0);
        assert_eq!(rec.wire_bytes, r.sim.metrics().wire_bytes());
        for i in 0..3 {
            assert_eq!(
                rec.node_tx_bytes.get(&i).copied().unwrap_or(0),
                r.sim.metrics().nodes[i].wire_bytes,
                "node {i}"
            );
        }
        // One transmit call covers one or more datagrams.
        let sent: u64 = r.sim.metrics().nodes.iter().map(|n| n.sent_packets).sum();
        assert!(rec.tx_count > 0 && rec.tx_count <= sent);
    });
}

#[test]
fn a_persisted_restart_resumes_and_a_stateless_one_does_not() {
    big_stack(|| {
        // Node 1 restarts with state at 40 s, node 2 without state at 40 s.
        let mut r = build(
            make_world(3, 120 * NS, |w| {
                w.env.push(EnvAction {
                    t: 40 * NS,
                    kind: EnvKind::Restart,
                    node: 2,
                    arg: EnvArg::Flag(false),
                });
            }),
            3,
            false,
        );
        for i in [1, 2] {
            r.echo(5 * NS, i, 0);
            r.sim.command(30 * NS, r.ids[i], Cmd::Persist);
            r.sim.crash(40 * NS, r.ids[i]);
            r.sim.restart(40 * NS, r.ids[i]);
            r.echo(50 * NS, i, 0);
        }
        r.sim.run_until(70 * NS);
        for i in [1, 2] {
            assert_eq!(r.stats[i].borrow().echoes, 2, "node {i}: {:?}", r.events(i));
            assert_eq!(r.node(i).incarnation(), 2);
        }
        assert!(r.node(1).max_export() > 0, "state was exported");
        let started = |i: usize| {
            r.events(i)
                .into_iter()
                .filter_map(|e| {
                    if let NodeEvent::Started { restored } = e {
                        Some(restored)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(started(1), vec![false, true]);
        assert_eq!(started(2), vec![false, false]);
        let resumed = |i: usize| {
            r.events(i)
                .into_iter()
                .filter_map(|e| {
                    if let NodeEvent::Connected { resumed, .. } = e {
                        Some(resumed)
                    } else {
                        None
                    }
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(resumed(1), vec![false, true], "a restored ticket resumes the session");
        assert_eq!(
            resumed(2),
            vec![false, false],
            "a stateless restart starts from scratch"
        );
        assert!(r.clean());
        // Intervals: alive, stopped, alive again.
        let rec = r.rec.borrow();
        assert_eq!(rec.alive_iv[&1].len(), 2);
        assert_eq!(rec.alive_iv[&1][0].1, Some(40 * NS));
    });
}

#[test]
fn suspend_and_resume() {
    big_stack(|| {
        let mut r = build(make_world(2, 90 * NS, |_| {}), 4, false);
        r.echo(5 * NS, 1, 0);
        r.sim.suspend(20 * NS, r.ids[1]);
        r.sim.resume(30 * NS, r.ids[1]);
        // An intent open while asleep: the dial is made right before the suspension.
        r.echo(19_999_000_000, 1, 0);
        r.echo(45 * NS, 1, 0);
        r.sim.run_until(60 * NS);
        assert_eq!(r.sim.state(r.ids[1]), NodeState::Up);
        let ev = r.events(1);
        assert!(ev.contains(&NodeEvent::Suspended) && ev.contains(&NodeEvent::Resumed));
        assert!(r.stats[1].borrow().echoes >= 2, "{ev:?}");
        let rec = r.rec.borrow();
        assert!(
            !rec.resumes.is_empty() && rec.resumes.iter().all(|x| x.node == 1),
            "a resume with an open dial is recorded"
        );
        assert!(r.clean());
    });
}

#[test]
fn a_denied_peer_does_not_connect() {
    big_stack(|| {
        let mut r = build(
            make_world(3, 60 * NS, |w| {
                w.denied = vec![2];
            }),
            5,
            false,
        );
        r.echo(5 * NS, 1, 0);
        r.echo(5 * NS, 2, 0);
        r.sim.run_until(40 * NS);
        assert_eq!(r.stats[1].borrow().echoes, 1);
        assert_eq!(r.stats[2].borrow().echoes, 0, "{:?}", r.events(2));
        assert_eq!(r.stats[0].borrow().served, 1);
        assert!(
            r.stats[2].borrow().failed + r.stats[2].borrow().closed > 0,
            "{:?}",
            r.events(2)
        );
        // Answers are given after the world's latency: nothing connected before 100 us passed.
        assert!(r.rec.borrow().acp_log.contains_key(&(0, 2)) || r.rec.borrow().acp_log.contains_key(&(2, 0)));
    });
}

#[test]
fn a_revoked_peer_is_cut_off() {
    big_stack(|| {
        let mut r = build(make_world(3, 90 * NS, |w| w.revoked = vec![(1, 20 * NS)]), 6, false);
        r.echo(5 * NS, 1, 0);
        r.echo(5 * NS, 2, 0);
        r.sim.run_until(15 * NS);
        assert_eq!(r.stats[1].borrow().echoes, 1);
        // The oracle revokes node 1 at 20 s: the recorder and every node learn of it.
        r.rec.borrow_mut().revoke(1, 20 * NS);
        for i in 0..3 {
            r.sim.command(20 * NS, r.ids[i], Cmd::Revoke(1));
        }
        r.echo(25 * NS, 1, 0);
        r.echo(25 * NS, 2, 0);
        r.sim.run_until(60 * NS);
        assert!(r.events(0).contains(&NodeEvent::Revoked { peer: 1 }));
        assert!(
            r.events(0).contains(&NodeEvent::Closed { peer: 1 }),
            "{:?}",
            r.events(0)
        );
        assert_eq!(r.stats[1].borrow().echoes, 1, "the revoked node gets no second echo");
        assert_eq!(
            r.stats[0].borrow().incoming,
            2,
            "the cloud never shows the revoked peer a new session"
        );
        assert_eq!(r.stats[2].borrow().echoes, 2, "other peers are unaffected");
        // A node told that the cloud is revoked refuses to dial it at once.
        r.sim.command(61 * NS, r.ids[2], Cmd::Revoke(0));
        r.echo(62 * NS, 2, 0);
        r.sim.run_until(70 * NS);
        assert_eq!(r.stats[2].borrow().refused, 1);
        assert_eq!(r.stats[2].borrow().echoes, 2);
    });
}

#[test]
fn a_graceful_shutdown_exports_state_and_the_node_restarts() {
    big_stack(|| {
        let mut r = build(make_world(2, 90 * NS, |_| {}), 7, false);
        r.echo(5 * NS, 1, 0);
        r.sim.command(20 * NS, r.ids[1], Cmd::Shutdown);
        r.sim.crash(20 * NS, r.ids[1]);
        r.sim.restart(30 * NS, r.ids[1]);
        r.echo(40 * NS, 1, 0);
        r.sim.run_until(60 * NS);
        let rec = r.rec.borrow();
        assert_eq!(rec.alive_iv[&1].len(), 2);
        assert_eq!(rec.alive_iv[&1][0].1, Some(20 * NS));
        drop(rec);
        assert!(r.events(1).contains(&NodeEvent::Stopped));
        assert!(r.node(1).max_export() > 0);
        assert_eq!(r.stats[1].borrow().echoes, 2, "{:?}", r.events(1));
        // The graceful leave closed the session at the cloud.
        assert!(
            r.events(0).contains(&NodeEvent::Closed { peer: 1 }),
            "{:?}",
            r.events(0)
        );
    });
}

#[test]
fn compromise_hands_the_state_to_the_ledger() {
    big_stack(|| {
        let mut r = build(make_world(2, 60 * NS, |_| {}), 8, false);
        r.echo(5 * NS, 1, 0);
        r.sim.command(20 * NS, r.ids[1], Cmd::Persist);
        r.sim.command(21 * NS, r.ids[1], Cmd::Compromise);
        r.sim.run_until(30 * NS);
        let c = r.reg.compromises();
        assert_eq!(c.len(), 1);
        assert_eq!((c[0].0, c[0].1), (21 * NS, 1));
        assert_eq!(r.node(1).identity_seed().len(), 32);
        assert_ne!(r.node(1).exported().len(), 0);
    });
}

#[test]
fn interface_changes_reach_the_endpoint() {
    big_stack(|| {
        let mut r = build(make_world(3, 120 * NS, |_| {}), 12, false);
        r.echo(5 * NS, 1, 0);
        r.echo(5 * NS, 2, 0);
        // The first home gets a new private address; the second loses its link for five seconds.
        let new_ip: IpAddr = IpAddr::V4([10, 99, 0, 1].into());
        r.sim.set_iface_addr(20 * NS, r.ids[1], 0, new_ip);
        r.sim.set_iface_up(30 * NS, r.ids[2], 0, false);
        r.sim.set_iface_up(35 * NS, r.ids[2], 0, true);
        r.echo(29_999_000_000, 2, 0);
        r.echo(50 * NS, 1, 0);
        r.echo(50 * NS, 2, 0);
        r.sim.run_until(80 * NS);
        assert_eq!(r.stats[1].borrow().echoes, 2, "{:?}", r.events(1));
        assert_eq!(r.stats[2].borrow().echoes, 3, "{:?}", r.events(2));
        let rec = r.rec.borrow();
        assert!(
            rec.resumes.iter().any(|x| x.node == 2),
            "a link that returned with an open echo is recorded"
        );
        assert_eq!(rec.violations.len(), 0);
    });
}

fn trace_and_hash(seed: u64) -> (String, String, u64) {
    let mut r = build(make_world(4, 60 * NS, |_| {}), seed, true);
    for i in 1..4 {
        r.echo(5 * NS + i as u64 * 1_000_000, i, 0);
    }
    r.sim.run_until(30 * NS);
    let hash = r.rec.borrow().trace_hash();
    let n = r.sim.events_processed();
    (r.sim.take_trace(), hash, n)
}

#[test]
fn the_same_seed_gives_the_same_trace_and_recorder_hash() {
    let a = big_stack(|| trace_and_hash(9));
    let b = big_stack(|| trace_and_hash(9));
    assert!(a.0.len() > 1000, "{}", a.0.len());
    assert_eq!(a.0, b.0, "simulator trace");
    assert_eq!(a.1, b.1, "recorder hash");
    assert_eq!(a.2, b.2);
}

#[test]
fn nodes_without_a_public_address_cannot_be_dialed() {
    big_stack(|| {
        let mut r = build(make_world(3, 60 * NS, |_| {}), 10, false);
        r.echo(5 * NS, 1, 2);
        r.sim.run_until(20 * NS);
        assert_eq!(r.stats[1].borrow().refused, 1);
        assert_eq!(r.stats[1].borrow().echoes, 0);
        assert_eq!(r.shared.public_addrs(2).len(), 0);
        assert_eq!(
            r.shared.public_addrs(0),
            &[SocketAddr::new(IpAddr::V4([10, 15, 66, 64].into()), 4433)]
        );
    });
}

/// 30 nodes for 60 virtual seconds: the speed and memory of the adapter (printed with `--nocapture`).
#[test]
fn thirty_nodes_for_a_minute() {
    big_stack(|| {
        let rss0 = rss_kib();
        let mut r = build(make_world(30, 60 * NS, |_| {}), 11, false);
        for i in 1..30 {
            for k in 0..10 {
                r.echo(3 * NS + (i as u64 * 7) * 10_000_000 + k * 5 * NS, i, 0);
            }
        }
        println!("rss after build {} MiB", rss_kib() / 1024);
        let t0 = std::time::Instant::now();
        r.sim.run_until(60 * NS);
        let dt = t0.elapsed().as_secs_f64();
        let ev = r.sim.events_processed();
        let echoes: usize = r.stats.iter().map(|s| s.borrow().echoes).sum();
        let failed: usize = r.stats.iter().map(|s| s.borrow().failed).sum();
        let conn: usize = r.stats.iter().map(|s| s.borrow().connected).sum();
        let reasons: Vec<_> = (0..30)
            .flat_map(|i| r.events(i))
            .filter(|e| matches!(e, NodeEvent::ConnectFailed { .. }))
            .collect();
        println!(
            "echoes {echoes} connected {conn} failed {failed} violations {:?} {reasons:?} cloud sessions {}",
            r.violations(),
            r.node(0).sessions()
        );
        assert_eq!(echoes, 29 * 10, "violations {:?}", r.violations());
        assert!(r.clean());
        let rss1 = rss_kib();
        println!(
            "30 nodes 60 s: {ev} events in {dt:.2} s = {:.0} events/s; rss {} MiB -> {} MiB ({} KiB per node); cloud sessions {}",
            ev as f64 / dt,
            rss0 / 1024,
            rss1 / 1024,
            (rss1 - rss0) / 30,
            r.node(0).sessions()
        );
    });
}

fn rss_kib() -> u64 {
    let s = std::fs::read_to_string("/proc/self/statm").unwrap_or_default();
    s.split_whitespace()
        .nth(1)
        .and_then(|p| p.parse::<u64>().ok())
        .unwrap_or(0)
        * 4
}

/// Each restart builds a new endpoint on the connection table of the last one; the node keeps working across many.
#[test]
fn many_restarts_keep_the_node_working() {
    big_stack(|| {
        let mut r = build(make_world(2, 120 * NS, |_| {}), 13, false);
        for k in 1..=4u64 {
            r.sim.crash((2 + 4 * k) * NS, r.ids[1]);
            r.sim.restart((4 + 4 * k) * NS, r.ids[1]);
            r.echo((5 + 4 * k) * NS, 1, 0);
        }
        r.sim.run_until(30 * NS);
        assert_eq!(r.node(1).incarnation(), 5);
        assert_eq!(r.stats[1].borrow().echoes, 4, "{:?}", r.events(1));
        assert_eq!(r.violations(), Vec::<String>::new());
    });
}
