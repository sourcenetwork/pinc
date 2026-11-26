//! Reproducing tests of findings of the `world` property in `pinc-sim`'s suite node. Each fails on the unmodified code.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::net::SocketAddr;
use std::rc::Rc;

use pinc_core::SessionId;
use pinc_sim::suite::crypto::Registry;
use pinc_sim::suite::grade::fixture::blank_world;
use pinc_sim::suite::node::{Cmd, Shared, SuiteCost, SuiteNode, iface_ip};
use pinc_sim::suite::proto::host::{Host, LayerEvent, Layers};
use pinc_sim::suite::rec::Rec;
use pinc_sim::suite::world::model::{Addr, IfaceSpec, Intent};
use pinc_sim::{LinkConfig, Loss, NatConfig, NatKind, Node, NodeId, PortPolicy, Sim, SimConfig, StreamKind};
use pinc_transport::stream::StreamId;
use world_harness::{AppNode, AppOp, Shape, Spec, Step};

mod world_harness;

const NS: u64 = 1_000_000_000;
const ALPN: &[u8] = b"pbt/world";
const DIAL_AT: u64 = 32 * NS;

/// The ends of streams each layer was told of: (node, session, stream) to how many times.
type Fins = Rc<RefCell<BTreeMap<(usize, SessionId, StreamId), u32>>>;

/// Nodes 0 and 1 dial each other once, each from its own timer at `DIAL_AT`; with `send`, each then writes one
/// 3000-byte message on a stream and finishes it. Every end of stream it is told of is counted.
struct Dialer {
    idx: usize,
    done: bool,
    send: bool,
    /// Subscribe to a topic at boot, as the property's application does.
    sub: bool,
    fins: Fins,
}

impl Layers for Dialer {
    fn alpns(&self) -> Vec<&'static [u8]> {
        vec![ALPN]
    }
    fn boot(&mut self, _now: u64, host: &mut dyn Host) {
        if self.sub {
            let _ = host.subscribe(b"pbt-topic");
        }
    }
    fn intent(&mut self, _now: u64, _host: &mut dyn Host, _intent: &Intent) {}
    fn event(&mut self, _now: u64, host: &mut dyn Host, ev: LayerEvent<'_>) {
        match ev {
            LayerEvent::Connected { session, alpn, .. } if self.send && alpn == ALPN => {
                if let Some(st) = host.open_stream(session) {
                    let msg = vec![0x5a; 3000];
                    assert_eq!(host.write(session, st, &msg), msg.len(), "the stream took the message");
                    host.finish(session, st);
                }
            },
            LayerEvent::StreamData {
                session,
                stream,
                fin: true,
                ..
            } => *self.fins.borrow_mut().entry((self.idx, session, stream)).or_insert(0) += 1,
            _ => {},
        }
    }
    fn timeout(&mut self, now: u64, host: &mut dyn Host) {
        if now >= DIAL_AT && !self.done {
            self.done = true;
            assert!(host.connect(1 - self.idx, ALPN), "the dial was refused");
        }
    }
    fn poll_timeout(&self) -> Option<u64> {
        (self.idx < 2 && !self.done).then_some(DIAL_AT)
    }
    fn has_open_intents(&self, _now: u64) -> bool {
        false
    }
    fn stop(&mut self) {}
}

fn iface(name: &str, kind: &str, host: u64, port: u16, public: bool) -> IfaceSpec {
    IfaceSpec {
        name: name.to_owned(),
        kind: kind.to_owned(),
        addr: Addr {
            kind: if kind == "udp4" { "udp4" } else { "tcp4" }.to_owned(),
            host,
            port,
        },
        mtu: if kind == "udp4" { 1472 } else { 1 << 20 },
        public,
        v6: false,
    }
}

type World = Sim<SuiteNode<Dialer>, pinc_sim::Rng, SuiteCost>;

/// The world of the property's shrunk cases: 10 ms links with 0.1 % loss, every node booted at 1 s; node `i` is public
/// when `public[i]` (else behind its own full-cone NAT); the nodes in `bootstrap` carry the relay and hub roles.
fn build(public: &[bool], bootstrap: &[usize], send: bool, sub: bool, fins: &Fins) -> (World, Vec<NodeId>) {
    let n = public.len();
    let mut w = blank_world("S1", n, 50 * NS);
    w.seed = 1;
    for (i, node) in w.nodes.iter_mut().enumerate() {
        let p = public[i];
        let h = if p { 1_000_000 + i as u64 } else { 3_000_000 + i as u64 * 256 };
        let (tp, wp) = if p { (443, 8443) } else { (50_000, 50_001) };
        node.ifaces = vec![iface("u4", "udp4", h, 4433, p), iface("t", "tcp", h, tp, p), iface("w", "ws", h, wp, p)];
        if p {
            "cloud".clone_into(&mut node.device);
            "cloud".clone_into(&mut node.kind);
        }
    }
    w.clouds = (0..n).filter(|&i| public[i]).collect();
    w.homes = (0..n).filter(|&i| !public[i]).collect();
    w.bootstrap = bootstrap.to_vec();
    let world = Rc::new(w);
    let rec = Rc::new(RefCell::new(Rec::new(Rc::clone(&world))));
    let reg = Registry::leak(world.seed);
    reg.install();
    let shared = Shared::new(Rc::clone(&world), rec, reg).unwrap();
    let cfg = SimConfig {
        default_link: Some(LinkConfig {
            delay: 10_000_000,
            loss: Loss::Bernoulli(0.001),
            ..LinkConfig::default()
        }),
        ..SimConfig::default()
    };
    let mut sim: World = Sim::with_parts(0, cfg, SuiteCost);
    let ids: Vec<_> = (0..n)
        .map(|i| {
            let layer = Dialer {
                idx: i,
                done: false,
                send,
                sub,
                fins: Rc::clone(fins),
            };
            let node = SuiteNode::new(Rc::clone(&shared), i, layer).unwrap();
            let ip = iface_ip(&world.nodes[i].ifaces[0].addr).unwrap();
            let id = if public[i] {
                let id = sim.add_node_at(node, ip);
                sim.listen(id, SocketAddr::new(ip, 443), StreamKind::Tcp);
                sim.listen(id, SocketAddr::new(ip, 8443), StreamKind::Ws);
                id
            } else {
                let id = sim.add_node(node);
                let ext = Addr {
                    kind: "udp4".to_owned(),
                    host: 2_000_000 + i as u64,
                    port: 0,
                };
                let nat = sim.add_nat(NatConfig {
                    kind: NatKind::FullCone,
                    ext_ip: iface_ip(&ext).unwrap(),
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
            id
        })
        .collect();
    for (i, id) in ids.iter().enumerate() {
        sim.crash(0, *id);
        sim.restart(NS + i as u64 * 1_000_000, *id);
    }
    (sim, ids)
}

/// A suite node whose application dials from its own timer is left due at once by that timer call, and the simulator
/// counts it as a late timer (and delays the node by 1 ms).
///
/// Expected: no late timer. The simulator's rule (crates/pinc-sim/src/metrics.rs, `Metrics::timer_violations`):
/// "Timeouts a node returned that were not strictly after a timer call (each was replaced by now plus 1 ms)", a counter
/// the suite holds at 0 (tests/scenario_node.rs:390, tests/node_leave_timer.rs). The layers' timer is part of the node
/// (`Layers::timeout`, "The layers' deadlines have come"), and a dial from it is an ordinary host call
/// (`Host::connect`).
///
/// Actual: after the timer call at 32 s in which a layer dials, `SuiteNode::poll_timeout` returns 32 s (the layer's
/// own deadline is gone: the deadline is the node's), and `timer_violations` counts it. In the `world` property it
/// fires on every case at the start of the final round (`EPHYRA_REPLAY=10062744908822254377:0`, `EPHYRA_REPLAY=5:0`),
/// where every application node dials from its timer; the same dial made from a scenario intent (a command call) is
/// not counted, since the simulator checks only timer calls.
///
/// Suspected fault: `SuiteNode::handle_timeout` (crates/pinc-sim/src/suite/node/mod.rs:431-443) runs the node's timers
/// (`core.run_timers`) before the layers' `timeout`, then only settles (`pump`, which calls `Node::poll`, not
/// `Node::handle_timeout`). A dial (`pinc_node::Node::dial`, node.rs:674) leaves the node with a deadline at the
/// current time, which only a timer call serves; so the timer call returns a deadline that is not after it. Running
/// the layers' timeout before the node's timers, or the node's timers again when the layers made calls, would serve it.
///
/// Who: any application layer on a suite node that acts from its own timer (the suite's own protocol stack does,
/// `suite/proto/stack.rs` `timeout`). The effect is a 1 ms delay of that work and a polluted violation counter.
///
/// Verdict: a conflict between two contracts of the project, for the maintainers to settle. pinc-node allows what the
/// simulator counts: "A layer may name the time of a timer call as its next deadline: the endpoint does when a layer
/// that ran after it in the same call gave it something to send ... That is a layer asking to be called again at once,
/// and the next call moves it" (crates/pinc-node/src/timers.rs, module doc). The `world` property also sees the count
/// rise with no application timer at all (its application is driven by intents), in a first run of its process:
/// `EPHYRA_REPLAY=5:0` gives 3 at 32.001 s, 32.053 s and 32.943 s after dials made from intents. So the zero that
/// tests/scenario_node.rs asserts holds for its worlds, not as a rule of pinc-node.
#[test]
fn a_dial_from_an_application_timer_leaves_no_late_timer() {
    // The shrunk case: node 0 public (a relay-role node), node 1 behind a full-cone NAT, node 2 a dedicated relay-role
    // node.
    let fins = Fins::default();
    let (mut sim, ids) = build(&[true, false, true], &[0, 2], false, false, &fins);
    sim.run_until(DIAL_AT - 1);
    assert_eq!(sim.metrics().timer_violations, 0, "control: no late timer before the dials");
    let late = sim.run_until_pred(DIAL_AT + NS, |s| s.metrics().timer_violations != 0);
    let due = Node::poll_timeout(sim.node_mut(ids[0]));
    assert!(sim.node(ids[0]).layers().done && sim.node(ids[1]).layers().done, "the layers dialed");
    assert!(!late, "a timer call in which the layer dialed left the node due ({due:?} for node 0, now {})", sim.now());
}

/// The suite node tells its layers twice that one stream ended: once with its last bytes, then again with no bytes.
///
/// Expected (crates/pinc-sim/src/suite/proto/host.rs, `LayerEvent::StreamData`): "Bytes arrived on a stream (already
/// consumed); `fin` says the peer finished it with these bytes." A stream is finished once, so `fin` comes once.
///
/// Actual: in the property's shrunk case (`EPHYRA_REPLAY=5:2` and `5:41` of
/// `every_shape_of_network_reaches_every_pair_and_keeps_every_byte`: two public nodes that both carry the relay and hub
/// roles, node 0 persisted and restarted at 5 s for 1 s, a 3000-byte message each way at 32 s) node 1 got
/// `StreamData { 3000 bytes, fin: true }` and then, at the same instant, `StreamData { 0 bytes, fin: true }` on the
/// same stream.
///
/// Suspected fault: `read_stream` (crates/pinc-sim/src/suite/node/events.rs:447-485) runs on every `StreamReadable`
/// event and reports `fin` whenever `Command::Consume` answers `RecvStatus::Finished`, which is a state ("The end was
/// received and every byte consumed", pinc-transport stream/mod.rs:220), not an edge. pinc-core may say a stream is
/// readable twice before the host reads it (`Event::lossy`: the event is a hint that the state answers), so a second
/// notification after the first read took the bytes and the end reports the end again. The adapter should report the
/// end once per stream.
///
/// Who: the remote peer's ordinary traffic, through any layer of the suite (the protocol stack, the tests' layers) that
/// acts on the end of a stream: it acts twice.
#[test]
fn a_finished_stream_is_reported_finished_once() {
    let fins = Fins::default();
    let (mut sim, ids) = build(&[true, true], &[0, 1], true, false, &fins);
    sim.command(5 * NS - 1_000_000, ids[0], Cmd::Persist);
    sim.crash(5 * NS, ids[0]);
    sim.restart(6 * NS, ids[0]);
    sim.run_until(DIAL_AT + 10 * NS);
    let fins = fins.borrow();
    assert!(!fins.is_empty(), "control: a message arrived whole");
    let twice: Vec<_> = fins.iter().filter(|(_, n)| **n > 1).collect();
    assert!(twice.is_empty(), "streams whose end was reported more than once: {twice:?}");
}

fn spec_stuck() -> Spec {
    let app = |public, nat| AppNode { public, nat };
    let step = |t_ms, node, op| Step { t_ms, node, op };
    Spec {
        shape: Shape::Ordinary,
        apps: vec![app(false, 0), app(false, 4), app(false, 0), app(false, 4)],
        dedicated: 1,
        loss_pm: 0,
        reorder: true,
        partition: None,
        restart: None,
        script: vec![
            step(19_850, 10, AppOp::Publish(605)),
            step(5_516, 242, AppOp::Dial(255)),
            step(6_259, 255, AppOp::Dial(253)),
            step(18_468, 250, AppOp::Dial(175)),
            step(17_687, 145, AppOp::Close(255)),
        ],
        seed: 1_334_464_112_475_711_700,
    }
}

fn on_big_stack(f: impl FnOnce() + Send + 'static) {
    if let Err(e) = std::thread::Builder::new().stack_size(256 << 20).spawn(f).unwrap().join() {
        std::panic::resume_unwind(e);
    }
}

/// A session whose peer stopped answering stays open with no path, takes the application's writes, and delivers
/// none of them: the final message from node 3 to node 2 never arrives within 40 s, and there is no fault at all.
///
/// Expected: every pair reaches each other (the application dials by node id alone, "the connectivity layer finds
/// the way", pinc-sim suite/node/events.rs `connect`), and a connection whose path is dead ends: "`Dead` needs 10
/// probe timeouts and silence of at least `max(20 s if the minimum round trip is 250 ms or more or the node is thin,
/// 8 x smoothed round trip)`" (pinc-transport recovery/engine.rs `health`), after which it closes silently
/// (conn/timer.rs:137) and the application dials again.
///
/// Actual (`EPHYRA_REPLAY=11:1689` of `every_shape_of_network_reaches_every_pair_and_keeps_every_byte`; Ordinary shape,
/// four private nodes behind full-cone and endpoint-dependent NATs, node 0 forced public and carrying the relay and
/// hub roles, one dedicated relay-role node added, 2 % reordering, no loss, no fault): at 72 s node 3 still holds its
/// session with node 2 as established, with no route (`route None`), `pto_count` 20, last heard at about 10.6 s.
/// Node 3 wrote the final message (3003 bytes, finished) on it at 32 s; node 2 never got it and no `Closed` came.
///
/// Suspected fault, not located: with no route nothing is sent, so the recovery timer that judges `health` may not
/// run, which leaves the idle timeout (75 s after the last activity, conn/life.rs `idle_deadline`) as the only end;
/// the application's writes may count as activity too (conn/life.rs: "Fold the application's writes since the last
/// clock reading into the activity times"). Why the session lost every path while the relay-role nodes were up is
/// open. The failing run is the one with the dedicated node added, which the property runs second in its thread; this
/// test runs it first, on a fresh thread.
///
/// Who: no adversary: ordinary traversal between private nodes.
#[test]
fn a_session_with_no_path_ends_and_the_pair_reaches_each_other() {
    on_big_stack(|| world_harness::run_and_check(&spec_stuck(), 1));
}
