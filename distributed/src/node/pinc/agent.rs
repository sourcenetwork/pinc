//! The PINC node program: the host core, its sockets and the workload commands, in one task on the nuclei runtime.
//!
//! One loop owns the core and everything else: it waits for a datagram, the next deadline (the node's, a publication's
//! or a wait's), a request of the orchestrator or an event of a stream task, applies it, then drains what the node
//! produced (stream operations, datagrams, application events) until nothing moves. No lock, no thread of PINC's own:
//! the runtime's tasks are the stream readers and writers, and they only exchange messages with the loop.
//!
//! Invariants: every request is answered exactly once, even when the node stops first; a publication run never sends a
//! message before its scheduled time and never more than a bounded burst per turn; a wait ends at its deadline with an
//! error that says what was missing.

use std::net::{IpAddr, SocketAddr};

use nuclei::sync::mpsc::UnboundedReceiver;
use pinc_node::trace::btag;
use pinc_node::{DtnPlan, NodeEvent};
use serde_json::{Value, json};

use super::core::{Core, HubAddr, NCmd, Op, Spec, StreamEv, Tx, node_id};
use super::dtn::{DtnStore, opener};
use super::dtnlog::{DtnLog, payload};
use super::net::{Net, Streams, Wire};
use crate::node::app::emit;
use crate::node::data::{Content, item, wall_ns};
use crate::node::proto::{Cmd, DtnReport, Init, Ready, Reply, Request};
use crate::node::stats::PubSubStats;
use crate::scenario::Role;

/// The UDP port of every PINC node.
pub const UDP_PORT: u16 = 4433;
/// The TCP port of a hub's relay carriers.
pub const TCP_PORT: u16 = 4434;
/// The most messages one publication run sends in one turn of the loop.
const BURST: u32 = 64;
/// Ids of streams the listener accepted start here, apart from those the core opens.
const ACCEPT_BASE: u64 = 1 << 32;

struct PubRun {
    req: u64,
    topic: Vec<u8>,
    count: u32,
    size: usize,
    interval_ns: u64,
    /// The wall clock time the run's first message is meant to go, in nanoseconds.
    start_wall: u64,
    sent: u32,
    next: u64,
    /// A message the node had no room to track, with the time in its header unchanged: it is offered again first.
    held: Option<Vec<u8>>,
    /// The run waits for one of the node's publishes to end before it offers `held` again.
    blocked: bool,
}

struct Wait {
    req: u64,
    deadline: u64,
    started: u64,
    size: u64,
    kind: Kind,
    /// The node's id of the fetch or round this waits for; zero for a join.
    id: u32,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Join,
    Fetch,
    Round,
}

/// A reach test in flight: the session dialed, when, and what was seen of its path once it came up.
struct ReachRun {
    req: u64,
    session: pinc_core::SessionId,
    started: u64,
    deadline: u64,
    hold_ns: u64,
    /// When the session came up and its path then.
    up: Option<(u64, super::portmap::PathSeen)>,
}

/// The workload state of the node program.
struct Agent<const K: usize, const D: usize> {
    reach: Vec<ReachRun>,
    core: Core<K, D>,
    me: u16,
    hubs: Vec<[u8; 32]>,
    stats: PubSubStats,
    pubs: Vec<PubRun>,
    waits: Vec<Wait>,
    dtn: DtnLog,
    stopping: bool,
}

fn hex(b: &[u8]) -> String {
    use std::fmt::Write as _;
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{x:02x}");
        s
    })
}

fn unhex32(s: &str) -> Option<[u8; 32]> {
    let mut out = [0u8; 32];
    if s.len() != 64 {
        return None;
    }
    for (i, o) in out.iter_mut().enumerate() {
        *o = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(out)
}

impl<const K: usize, const D: usize> Agent<K, D> {
    fn new(init: &Init, mtu: u16, batch: usize) -> Result<(Self, Ready), String> {
        let me_spec = init
            .me()
            .ok_or_else(|| format!("{} is not a node of the scenario", init.name))?
            .clone();
        let addr = SocketAddr::new(IpAddr::V4(me_spec.ip), me_spec.port(UDP_PORT));
        // Relay servers first, on their one port: a node reaches a peer through its first relay until a direct path
        // works. A relay server is a hub too (pinc_relay's default), so the node joins through it like any hub.
        let mut hubs = Vec::new();
        for p in init.peers.iter().filter(|p| p.role == Role::RelayServer) {
            let at = SocketAddr::new(IpAddr::V4(p.public_ip), p.port(UDP_PORT));
            hubs.push(HubAddr {
                id: node_id(&p.name)?,
                udp: at,
                tcp: at,
            });
        }
        for p in init.peers.iter().filter(|p| matches!(p.role, Role::Hub | Role::Relay)) {
            hubs.push(HubAddr {
                id: node_id(&p.name)?,
                udp: SocketAddr::new(IpAddr::V4(p.public_ip), p.port(UDP_PORT)),
                tcp: SocketAddr::new(IpAddr::V4(p.public_ip), p.port(TCP_PORT)),
            });
        }
        if hubs.is_empty() {
            return Err(
                "the PINC workloads need a node with the role hub or relay for the others to join through".into(),
            );
        }
        let spec = Spec {
            name: init.name.clone(),
            addr,
            hubs,
            is_hub: me_spec.role != Role::Peer,
            mtu,
            trace: init.trace,
            topic_log_bytes: super::core::topic_log_bytes(init.pinc_library_topic_log),
            batch,
            pool_chunks: 1024,
            portmap: init.portmap,
        };
        let mut apps = super::apps::VApps::default();
        if let Some(d) = init.dtn.clone() {
            apps.dtn = DtnStore::new(&init.name, d)?;
        }
        let mut core = Core::<K, D>::new(&spec, apps)?;
        // A harness built with PINC_REACH=mesh measures delivery scoped to the connected component (pinc#86): every
        // member names every other member as a session peer, as replicators that all hold sessions with each other
        // would, so the hubs hand each message to the same subscribers as without the scope and pay its checks.
        let mesh = option_env!("PINC_REACH") == Some("mesh");
        if mesh && !spec.is_hub {
            let mut peers = Vec::new();
            for p in init
                .peers
                .iter()
                .filter(|p| p.role == Role::Peer && p.name != init.name)
            {
                peers.push(node_id(&p.name)?.bytes);
            }
            core.set_adjacent(&peers)
                .map_err(|e| format!("the adjacency record was refused: {e}"))?;
        }
        let hub_ids = spec.hubs.iter().map(|h| h.id.bytes).collect();
        let ready = Ready {
            stack: "pinc".into(),
            id: hex(&core.me.bytes),
            config: format!(
                "the PINC node over its UDP endpoint (up to {K} sessions, 1 MiB stream windows, {} streams each way, {batch} datagrams per send, interface size {mtu}, a topic log of {} MiB on a hub) with relay carriers over TCP; {}",
                super::core::stream_limit(),
                spec.topic_log_bytes >> 20,
                if spec.is_hub {
                    "this node is a hub"
                } else {
                    "it joins through the hubs"
                }
            ),
        };
        let mut ready = ready;
        if mesh {
            ready
                .config
                .push_str("; topics scoped to the connected component, every member naming the others");
        }
        if let Some(d) = &init.dtn {
            use std::fmt::Write as _;
            let _ = write!(
                ready.config,
                "; delay-tolerant delivery on (pinc-node's layer, a {} KiB bundle budget)",
                d.budget >> 10
            );
        }
        let me = me_spec.index;
        Ok((
            Self {
                core,
                me,
                hubs: hub_ids,
                stats: PubSubStats::new(me),
                pubs: Vec::new(),
                waits: Vec::new(),
                reach: Vec::new(),
                dtn: DtnLog::new(init.peers.iter().map(|p| p.name.as_str())),
                stopping: false,
            },
            ready,
        ))
    }

    fn hub_up(&self, now: u64) -> bool {
        self.core.is_hub() || self.hubs.iter().any(|h| self.core.node.membership().hub_is_up(now, h))
    }

    /// A request of the orchestrator; replies it can give at once go to `out`.
    #[allow(
        clippy::too_many_lines,
        reason = "one match over the protocol's requests, read top to bottom"
    )]
    fn request(&mut self, now: u64, req: Request, out: &mut Vec<Reply>) {
        let id = req.id;
        match req.cmd {
            Cmd::Join { topic, wait_ms } => {
                if let Err(e) = self.core.command(now, NCmd::Subscribe(topic.into_bytes())) {
                    out.push(Reply::fail(id, e));
                    return;
                }
                if self.hub_up(now) {
                    out.push(Reply::ok(id, Value::Null));
                } else {
                    self.waits.push(Wait {
                        req: id,
                        deadline: now + wait_ms * 1_000_000,
                        started: now,
                        size: 0,
                        kind: Kind::Join,
                        id: 0,
                    });
                }
            }
            Cmd::Publish {
                topic,
                count,
                size,
                interval_us,
                start_ns,
            } => {
                let now_wall = wall_ns();
                let lead = start_ns.saturating_sub(now_wall);
                self.pubs.push(PubRun {
                    req: id,
                    topic: topic.into_bytes(),
                    count,
                    size: size as usize,
                    interval_ns: interval_us * 1000,
                    start_wall: start_ns.max(now_wall),
                    sent: 0,
                    next: now + lead,
                    held: None,
                    blocked: false,
                });
            }
            Cmd::Provide { size, seed } => {
                let content = Content::new(seed, size);
                match self.core.values().provide(&content) {
                    Ok(root) => match self.core.command(now, NCmd::Provide(root)) {
                        Ok(_) => out.push(Reply::ok(id, json!({ "root": hex(&root), "size": size }))),
                        Err(e) => out.push(Reply::fail(id, e)),
                    },
                    Err(e) => out.push(Reply::fail(id, e)),
                }
            }
            Cmd::Fetch {
                value,
                providers,
                timeout_ms,
            } => self.fetch(now, id, &value, &providers, timeout_ms, out),
            Cmd::HoldSet {
                set,
                items,
                seed,
                different,
                other_seed,
            } => {
                let shared = items.saturating_sub(different);
                let all: Vec<[u8; 32]> = (0..items)
                    .map(|i| item(if i < shared { seed } else { other_seed }, u64::from(i)))
                    .collect();
                match self.core.hold_set(set.as_bytes(), all) {
                    Ok(()) => out.push(Reply::ok(id, Value::Null)),
                    Err(e) => out.push(Reply::fail(id, e)),
                }
            }
            Cmd::Reconcile { peer, set, timeout_ms } => {
                let Ok(peer_id) = node_id(&peer) else {
                    out.push(Reply::fail(id, format!("{peer} has no identity")));
                    return;
                };
                match self.core.command(
                    now,
                    NCmd::Reconcile {
                        peer: peer_id.bytes,
                        set: set.into_bytes(),
                    },
                ) {
                    Ok(round) => self.waits.push(Wait {
                        req: id,
                        deadline: now + timeout_ms * 1_000_000,
                        started: now,
                        size: 0,
                        kind: Kind::Round,
                        id: round,
                    }),
                    Err(e) => out.push(Reply::fail(id, e)),
                }
            }
            Cmd::DtnContacts { t0_ms, windows } => {
                out.push(
                    match self.core.node.apps_mut().dtn.set_contacts(t0_ms, windows.as_deref()) {
                        Ok(()) => Reply::ok(id, Value::Null),
                        Err(e) => Reply::fail(id, e),
                    },
                );
            }
            Cmd::DtnSend {
                to,
                size,
                seed,
                copies,
                lifetime_ms,
                k,
                m,
                slice_log,
            } => {
                let plan = DtnPlan {
                    lifetime_ms,
                    copies,
                    k,
                    m,
                    slice_log,
                };
                let sent = opener(&to).and_then(|o| self.core.dtn_send(now, &o.keys, &payload(seed, size), &plan));
                out.push(match sent {
                    Ok(b) => Reply::ok(id, json!({ "bundle": format!("{:016x}", btag(&b)) })),
                    Err(e) => Reply::fail(id, format!("the bundle was not made: {e}")),
                });
            }
            Cmd::Suspend => out.push(match self.core.command(now, NCmd::Suspend) {
                Ok(_) => Reply::ok(id, Value::Null),
                Err(e) => Reply::fail(id, e),
            }),
            Cmd::Resume => out.push(match self.core.command(now, NCmd::Resume) {
                Ok(_) => Reply::ok(id, Value::Null),
                Err(e) => Reply::fail(id, e),
            }),
            Cmd::Reach {
                peer,
                timeout_ms,
                hold_ms,
            } => {
                let Ok(peer_id) = node_id(&peer) else {
                    out.push(Reply::fail(id, format!("{peer} has no identity")));
                    return;
                };
                match self.core.reach_dial(now, peer_id) {
                    Ok(session) => self.reach.push(ReachRun {
                        req: id,
                        session,
                        started: now,
                        deadline: now + timeout_ms * 1_000_000,
                        hold_ns: hold_ms * 1_000_000,
                        up: None,
                    }),
                    Err(e) => out.push(Reply::fail(id, e)),
                }
            }
            Cmd::Report => {
                self.drain_dtn_trace();
                let (peak_bytes, budget) = self.core.node.apps().dtn.peak_and_budget();
                let r = self.core.restored;
                let dtn = DtnReport {
                    log: self.dtn.log.clone(),
                    held: self.core.node.dtn_held() as u64,
                    peak_bytes,
                    budget,
                    restored: [r.held, r.partial, r.received, r.dropped].map(|n| n as u64),
                    lost: self.dtn.lost,
                };
                let (max, mean) = super::net::SENT.read();
                let mut v = json!({
                    "pubsub": self.stats.report(),
                    "counters": self.core.counters,
                    "members": self.core.node.membership().member_count(),
                    "dtn": dtn,
                    "portmap": self.core.portmap_report(),
                    // Every UDP payload the node's socket sent since its program started.
                    "wire": {"max_udp_payload": max, "mean_udp_payload": mean},
                });
                if let (Some(l), Some(m)) = (self.core.tlog.as_ref(), v.as_object_mut()) {
                    m.insert("trace".into(), l.report());
                }
                out.push(Reply::ok(id, v));
            }
            Cmd::Stop => {
                // Leaving tells the hubs this node is gone for good; the loop ends after the farewell is sent.
                let _ = self.core.command(now, NCmd::Leave);
                self.stopping = true;
                out.push(Reply::ok(id, Value::Null));
            }
        }
    }

    fn fetch(&mut self, now: u64, id: u64, value: &Value, providers: &[String], timeout_ms: u64, out: &mut Vec<Reply>) {
        let root = value.get("root").and_then(Value::as_str).and_then(unhex32);
        let size = value.get("size").and_then(Value::as_u64);
        let (Some(root), Some(size)) = (root, size) else {
            out.push(Reply::fail(id, "the value to fetch needs a root and a size"));
            return;
        };
        let ids: Result<Vec<[u8; 32]>, String> = providers.iter().map(|p| node_id(p).map(|n| n.bytes)).collect();
        let Ok(ids) = ids else {
            out.push(Reply::fail(id, "a provider has no identity"));
            return;
        };
        let Ok(n) = usize::try_from(size) else {
            out.push(Reply::fail(id, "the value is larger than this machine can hold"));
            return;
        };
        self.core.values().reserve(&root, n);
        match self.core.command(
            now,
            NCmd::Fetch {
                root,
                length: size,
                providers: ids,
            },
        ) {
            Ok(fetch) => self.waits.push(Wait {
                req: id,
                deadline: now + timeout_ms * 1_000_000,
                started: now,
                size,
                kind: Kind::Fetch,
                id: fetch,
            }),
            Err(e) => out.push(Reply::fail(id, e)),
        }
    }

    /// Move the delay-tolerant layer's trace records into its log.
    fn drain_dtn_trace(&mut self) {
        while let Some((ms, t)) = self.core.dtn_trace.pop_front() {
            self.dtn.trace(ms, t);
        }
    }

    /// The application events the node produced.
    fn events(&mut self, now: u64, out: &mut Vec<Reply>) {
        self.drain_dtn_trace();
        while let Some(ev) = self.core.events.pop_front() {
            self.dtn.event(wall_ns() / 1_000_000, &ev);
            match ev {
                NodeEvent::Message { body, .. } => self.stats.record(&body, wall_ns()),
                // The node tracks one publish fewer: a run that waited for room offers its message again.
                NodeEvent::PublishAcked { .. }
                | NodeEvent::PublishGaveUp { .. }
                | NodeEvent::PublishFull { .. }
                | NodeEvent::PublishRoom => {
                    for run in &mut self.pubs {
                        run.blocked = false;
                    }
                }
                NodeEvent::ValueComplete { fetch } => {
                    if let Some(w) = self.finish(Kind::Fetch, fetch) {
                        out.push(Reply::ok(
                            w.req,
                            json!({ "bytes": w.size, "ms": ms(now.saturating_sub(w.started)) }),
                        ));
                    }
                }
                NodeEvent::ValueFailed { fetch, reason } => {
                    if let Some(w) = self.finish(Kind::Fetch, fetch) {
                        out.push(Reply::fail(
                            w.req,
                            format!("the value could not be fetched ({reason:?})"),
                        ));
                    }
                }
                NodeEvent::ReconcileDone {
                    round,
                    missing_here,
                    missing_there,
                    ..
                } => {
                    if let Some(w) = self.finish(Kind::Round, round) {
                        out.push(Reply::ok(
                            w.req,
                            json!({
                                "missing_here": missing_here.len(),
                                "missing_there": missing_there.len(),
                                "ms": ms(now.saturating_sub(w.started)),
                            }),
                        ));
                    }
                }
                NodeEvent::ReconcileFailed { round, reason, .. } => {
                    if let Some(w) = self.finish(Kind::Round, round) {
                        out.push(Reply::fail(
                            w.req,
                            format!("the sets could not be reconciled ({reason:?})"),
                        ));
                    }
                }
                _ => {}
            }
        }
    }

    /// Take the wait of a fetch or a round out of the list.
    fn finish(&mut self, kind: Kind, id: u32) -> Option<Wait> {
        let pos = self.waits.iter().position(|w| w.kind == kind && w.id == id)?;
        Some(self.waits.swap_remove(pos))
    }

    /// Publications due, waits satisfied or timed out; the next time anything needs the loop.
    fn tick(&mut self, now: u64, out: &mut Vec<Reply>) {
        let mut finished = Vec::new();
        for (i, run) in self.pubs.iter_mut().enumerate() {
            let mut burst = 0;
            while run.sent < run.count && run.next <= now && burst < BURST && !run.blocked {
                let body = run.held.take().unwrap_or_else(|| {
                    crate::node::data::Header {
                        origin: self.me,
                        seq: run.sent,
                        sent_ns: wall_ns(),
                        intended_ns: run
                            .start_wall
                            .saturating_add(run.interval_ns.saturating_mul(u64::from(run.sent))),
                    }
                    .body(run.size)
                });
                match self.core.publish(now, &run.topic, &body) {
                    Ok(()) => self.stats.published(),
                    // The publisher waits as a caller of an awaited publish does: the same message, with the time
                    // it was first offered, goes again when the node has room to track it.
                    Err(pinc_broadcast::Refused::Backlog) => {
                        *self.core.counters.entry("publish_waited").or_insert(0) += 1;
                        run.held = Some(body);
                        run.blocked = true;
                        break;
                    }
                    Err(_) => *self.core.counters.entry("publish_refused").or_insert(0) += 1,
                }
                run.sent += 1;
                run.next += run.interval_ns;
                burst += 1;
            }
            if run.sent >= run.count {
                finished.push(i);
            }
        }
        for i in finished.into_iter().rev() {
            let run = self.pubs.swap_remove(i);
            out.push(Reply::ok(run.req, json!({ "published": run.count })));
        }
        let up = self.hub_up(now);
        let mut keep = Vec::new();
        for w in std::mem::take(&mut self.waits) {
            match w.kind {
                Kind::Join if up => out.push(Reply::ok(w.req, Value::Null)),
                _ if w.deadline <= now => out.push(Reply::fail(
                    w.req,
                    match w.kind {
                        Kind::Join => "no hub answered in time; check that a hub or relay node is reachable",
                        Kind::Fetch => "the value did not arrive in time",
                        Kind::Round => "the sets did not reconcile in time",
                    },
                )),
                _ => keep.push(w),
            }
        }
        self.waits = keep;
        self.reach_tick(now, out);
    }

    /// Reach tests: note when a session came up and its path, answer once it was held, fail one that never came up.
    fn reach_tick(&mut self, now: u64, out: &mut Vec<Reply>) {
        let mut keep = Vec::new();
        for mut r in std::mem::take(&mut self.reach) {
            let seen = self.core.reach_path(r.session);
            match (r.up, seen) {
                (None, Some(p)) if p.established => {
                    r.up = Some((now, p));
                    keep.push(r);
                }
                (Some((at, first)), Some(p)) if now >= at + r.hold_ns => out.push(Reply::ok(
                    r.req,
                    json!({
                        "ms": ms(at.saturating_sub(r.started)),
                        "first": first.json(),
                        "held": p.json(),
                        "portmap": self.core.portmap_report(),
                    }),
                )),
                (Some((at, first)), None) => out.push(Reply::fail(
                    r.req,
                    format!(
                        "the session ended while it was held; it came up after {:.1} ms on {}",
                        ms(at.saturating_sub(r.started)),
                        first.json()
                    ),
                )),
                (None, _) if now >= r.deadline => {
                    out.push(Reply::fail(r.req, "no session came up in time"));
                }
                _ => keep.push(r),
            }
        }
        self.reach = keep;
    }

    fn next_deadline(&self) -> Option<u64> {
        let pubs = self
            .pubs
            .iter()
            .filter(|p| p.sent < p.count && !p.blocked)
            .map(|p| p.next);
        let waits = self.waits.iter().map(|w| w.deadline);
        // A join is also re-checked soon: hub liveness has no event of its own.
        let joins = self
            .waits
            .iter()
            .any(|w| matches!(w.kind, Kind::Join))
            .then(|| self.core.now() + 50_000_000);
        // A reach test looks at its session's path every 50 ms.
        let reach = (!self.reach.is_empty()).then(|| self.core.now() + 50_000_000);
        pubs.chain(waits).chain(joins).chain(reach).min()
    }
}

/// The lengths of the datagrams in a send of `len` bytes cut every `segment` bytes (the last may be shorter).
fn datagram_lens(len: usize, segment: usize) -> impl Iterator<Item = usize> {
    let seg = segment.max(1);
    (0..len).step_by(seg).map(move |o| seg.min(len - o))
}

// Milliseconds with microsecond resolution.
#[allow(clippy::cast_precision_loss)]
fn ms(ns: u64) -> f64 {
    ns as f64 / 1e6
}

/// Everything the loop sends and receives besides the node's own state.
struct Io {
    net: Net,
    streams: Streams,
    sbuf: Vec<u8>,
}

impl Io {
    async fn drain<const K: usize, const D: usize>(&mut self, agent: &mut Agent<K, D>) {
        let mut replies = Vec::new();
        for _ in 0..4096 {
            let now = agent.core.now();
            agent.core.pump(now);
            let mut moved = false;
            while let Some(Tx { remote, len, segment }) = agent.core.poll_transmit(now, &mut self.sbuf) {
                moved = true;
                if let Some(l) = agent.core.tlog.as_mut() {
                    for n in datagram_lens(len, segment) {
                        l.note("udp_tx", format!("{remote} {n}"));
                    }
                }
                if let Some(data) = self.sbuf.get(..len)
                    && let Err(e) = self.net.send(data, remote, segment).await
                {
                    tracing::warn!("a datagram could not be sent: {e}");
                }
            }
            while let Some(op) = agent.core.ops.pop_front() {
                moved = true;
                match op {
                    Op::Connect { stream, to } => self.streams.connect(stream, to),
                    Op::Write { stream, data } => {
                        if let Some(l) = agent.core.tlog.as_mut() {
                            l.note("carrier_tx", format!("{stream} {}", data.len()));
                        }
                        let _ = self.streams.write(stream, data);
                    }
                    Op::Close { stream } => self.streams.close(stream),
                }
            }
            if !agent.core.events.is_empty() {
                moved = true;
                agent.events(now, &mut replies);
            }
            for r in replies.drain(..) {
                emit(&r);
            }
            if !moved {
                return;
            }
        }
    }
}

/// Run the PINC node program until it is told to stop.
///
/// # Errors
/// The node or its socket could not start.
// One loop that owns the node, read top to bottom.
#[allow(clippy::too_many_lines, clippy::needless_continue)]
pub async fn serve<const K: usize, const D: usize>(
    init: Init,
    mut cmds: UnboundedReceiver<Request>,
) -> Result<(), String> {
    let me_spec = init
        .me()
        .ok_or_else(|| format!("{} is not a node of the scenario", init.name))?;
    let bind = SocketAddr::new(IpAddr::V4(me_spec.ip), me_spec.port(UDP_PORT));
    let net = Net::bind(bind).map_err(|e| format!("the UDP socket on {bind} could not be opened: {e}"))?;
    let batch = net.batch();
    let mtu = u16::try_from(init.mtu).unwrap_or(1500);
    let (mut agent, ready) = Agent::<K, D>::new(&init, mtu, batch)?;
    let (streams, mut wire) = Streams::new();
    if agent.core.is_hub() {
        let tcp = SocketAddr::new(bind.ip(), me_spec.port(TCP_PORT));
        let listener = nuclei::net::TcpListener::bind(tcp)
            .await
            .map_err(|e| format!("the TCP listener on {tcp} could not be opened: {e}"))?;
        streams.listen(listener, ACCEPT_BASE);
    }
    let mut io = Io {
        net,
        streams,
        sbuf: vec![0u8; 64 * 1024],
    };
    println!("READY {}", serde_json::to_string(&ready).map_err(|e| e.to_string())?);
    let mut rbuf = vec![0u8; 64 * 1024];
    let mut replies = Vec::new();
    // The node's next deadline, on one precise timer moved only when the deadline does: arming it costs the runtime a
    // system call. The millisecond wheel is not used: it fires up to a millisecond late, once per round trip of a
    // transfer still in slow start, which made a 1 MiB fetch over a WAN 10 ms slower.
    let mut timer = std::pin::pin!(nuclei::time::sleep_until_precise(std::time::Instant::now()));
    let mut armed: Option<std::time::Instant> = None;
    loop {
        io.drain(&mut agent).await;
        if agent.stopping {
            // Let the farewell leave, then end.
            Net::sleep_until(std::time::Instant::now() + std::time::Duration::from_millis(200)).await;
            io.drain(&mut agent).await;
            return Ok(());
        }
        let due = [agent.core.poll_timeout(), agent.next_deadline()]
            .into_iter()
            .flatten()
            .min();
        // A deadline already passed fires at once; with none, the armed one stands if it is still ahead.
        let now_i = std::time::Instant::now();
        let at = due.map_or_else(
            || {
                armed
                    .filter(|a| *a > now_i)
                    .unwrap_or(now_i + std::time::Duration::from_secs(1))
            },
            |t| agent.core.instant_of(t),
        );
        if armed != Some(at) {
            timer.as_mut().reset(at);
            armed = Some(at);
        }
        let wake = std::future::poll_fn(|cx| timer.as_mut().poll(cx));
        nuclei::select! {
            r = io.net.recv(&mut rbuf) => {
                let now = agent.core.now();
                match r {
                    Ok((len, from, stride)) => {
                        if let Some(all) = rbuf.get_mut(..len) {
                            for chunk in all.chunks_mut(stride) {
                                if let Some(l) = agent.core.tlog.as_mut() {
                                    l.note("udp_rx", format!("{from} {}", chunk.len()));
                                }
                                agent.core.handle_datagram(now, from, chunk);
                            }
                        }
                    }
                    Err(e) => return Err(format!("the UDP socket failed: {e}")),
                }
            }
            () = wake => {
                let now = agent.core.now();
                agent.core.handle_timeout(now);
                agent.tick(now, &mut replies);
            }
            r = cmds.recv() => match r {
                // The time is read now, not when the loop went to wait: a request that arrives late in a wait would
                // otherwise be stamped, and its duration counted, from before it existed.
                Some(req) => {
                    let now = agent.core.now();
                    agent.request(now, req, &mut replies);
                }
                // The orchestrator closed its end: nobody is left to ask for anything.
                None => return Ok(()),
            },
            Some(w) = wire.recv() => {
                let now = agent.core.now();
                match w {
                Wire::Ev(StreamEv::Closed(id)) => {
                    io.streams.ended(id);
                    agent.core.stream_event(now, StreamEv::Closed(id));
                }
                Wire::Ev(ev) => agent.core.stream_event(now, ev),
                Wire::Connected(id, Some(s)) => {
                    io.streams.adopt(id, s);
                    agent.core.stream_event(now, StreamEv::Opened(id));
                }
                Wire::Connected(id, None) => agent.core.stream_event(now, StreamEv::Failed(id)),
                Wire::Accepted(id, s) => {
                    io.streams.adopt(id, s);
                    agent.core.stream_event(now, StreamEv::Accepted(id));
                }
                }
            },
        }
        let now = agent.core.now();
        agent.tick(now, &mut replies);
        for r in replies.drain(..) {
            emit(&r);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::datagram_lens;

    #[test]
    fn a_batched_send_is_one_entry_per_datagram() {
        assert_eq!(datagram_lens(3000, 1200).collect::<Vec<_>>(), [1200, 1200, 600]);
        assert_eq!(datagram_lens(1200, 1200).collect::<Vec<_>>(), [1200]);
        assert_eq!(datagram_lens(0, 0).count(), 0);
        assert_eq!(datagram_lens(3, 0).collect::<Vec<_>>(), [1, 1, 1]);
    }
}
