//! The node adapter: a `pinc-node` node (the real endpoint with instrumented crypto, the connectivity client, membership
//! and broadcast) driven as a simulator [`Node`].
//!
//! [`SuiteNode`] wraps one node (rebuilt on every restart) and the protocol layers of the application ([`Layers`]). It
//! answers the key requests of the endpoint and of the carrier handshakes with a deterministic software identity,
//! answers access checks through the recorder's oracle after the world's latency, splits the endpoint's batched
//! transmits into single datagrams, reports every datagram and every state sample to the recorder, and implements
//! [`Host`](crate::suite::proto::host::Host) so the layers can dial, open streams, write, subscribe and publish. A
//! bootstrap node is a hub: it also runs the relay for its members. Every node opens carrier streams to its relays
//! over the simulator's TCP and WebSocket connections; a browser opens WebSocket carriers only and sends no datagram.
//! [`Shared`] holds what all nodes of a run share; [`SuiteCost`] is the simulator's cost model for the suite.
//!
//! # What the runner does
//!
//! - Builds one [`Shared`] per run and one [`SuiteNode`] per world node, adds them to the simulator in world order, and
//!   gives each simulator interface the address [`iface_ip`] of the matching world interface.
//! - Stops every node at time 0 (`Sim::crash`) and starts it at its start time (`Sim::restart`): a node begins stopped,
//!   and each restart builds a new incarnation. A restart that keeps no state must be scheduled at the time of its
//!   `restart` action with a false flag.
//! - Sends [`Cmd::Persist`] every 60 s, [`Cmd::Shutdown`] and then a crash at the same time for a leave or upgrade,
//!   [`Cmd::Revoke`] to every node when the oracle revokes a peer (it also calls `Rec::revoke`), [`Cmd::Intent`] for
//!   each application intent, and [`Cmd::Compromise`] at a key compromise (the node then calls
//!   `Registry::note_compromise` with its identity seed and its current exported state; for a node that is down, use
//!   [`SuiteNode::identity_seed`] and [`SuiteNode::exported`]).
//! - Records what only it knows: `Rec::suspended`, `Rec::address_change` and `Rec::nat_rebind` (the node records
//!   `node_started`, `node_stopped`, `resumed`, `link_returned` on an interface coming up, and `restarted_with_state`,
//!   which need the layers' open intents; the reference records it for every `restart` action of the world, state kept or
//!   not, so a restart at the time of such an action does, and an upgrade does not). A path-MTU violation is the simulator's `DropReason::Mtu` count. The runner
//!   tells a node about address changes and moves that the simulator does not deliver while the node is not running
//!   with [`SuiteNode::mark_moved`] and [`SuiteNode::set_iface_up`].
//! - Feeds the amplification ledger of `Registry::sec_verdict` from the simulator, which alone sees unvalidated sources.
//!
//! # Limits of the adapter
//!
//! The endpoint uses the UDP interfaces of the world; streams carry only the connectivity client's relay carriers. The
//! state size reported to the recorder is an
//! estimate built from counts the endpoint exposes (see [`SESSION_STATE_BYTES`]). The redundant-bytes count of a datagram
//! is zero here: only the node's value layer sees which bytes of a payload it already held. The endpoint's connection
//! memory (the slot table is resident, the buffer pools only as far as they are used) is
//! allocated once per table and handed from an ended endpoint to the next one on the same thread, so a restart or a
//! later run does not allocate again; an idle node holds about 17 MiB of it. The endpoint is half a megabyte, so build a node on a thread with a stack of a few megabytes.
//!
//! Invariants: the endpoint sees the node's local clock, the layers and the recorder see true time; a node's identity is created once
//! and kept across restarts; nothing here reads a clock, a socket or a random source of the machine.

mod apps;
mod carrier;
mod core;
mod cost;
mod events;
mod layer;
mod mem;
mod peers;
mod relay;
mod shared;
mod values;

static TRACE_FROM: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(u64::MAX);
static TRACE_TO: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Also record the endpoint, membership and broadcast records of watched nodes between the true times `from` and
/// `to` (nanoseconds), for diagnosis. The window is process-wide and off until set.
pub fn set_trace_window(from: u64, to: u64) {
    TRACE_FROM.store(from, std::sync::atomic::Ordering::Relaxed);
    TRACE_TO.store(to, std::sync::atomic::Ordering::Relaxed);
}

fn in_trace_window(now: u64) -> bool {
    use std::sync::atomic::Ordering::Relaxed;
    (TRACE_FROM.load(Relaxed)..TRACE_TO.load(Relaxed)).contains(&now)
}

static DECISIONS: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Record the decisions of every node (sessions opening, ending and failing, members joining and going down) as lines
/// `D <seconds> n<node> <what> n<peer>`, whatever nodes are watched. Process-wide and off until set; the reference
/// side prints the same form, so two runs of one world can be compared for their first difference.
pub fn set_decision_trace(on: bool) {
    DECISIONS.store(on, std::sync::atomic::Ordering::Relaxed);
}

fn decision_trace() -> bool {
    DECISIONS.load(std::sync::atomic::Ordering::Relaxed)
}

/// Whether the window is wide: datagrams are then summed per second and address, not listed.
fn wide_window() -> bool {
    use std::sync::atomic::Ordering::Relaxed;
    TRACE_TO.load(Relaxed).saturating_sub(TRACE_FROM.load(Relaxed)) > 4_000_000_000
}

/// How many turns of the host loop a call may take before the node is reported as not settling.
const SETTLE_ROUNDS: usize = 128;

use std::net::{IpAddr, SocketAddr};
use std::rc::Rc;

use self::core::{Core, Phase};
pub use self::core::{CpuParts, LEDGER_ENTRY_BYTES, LOCAL_BASE, MAX_GSO, PEER_ENTRY_BYTES, SESSION_STATE_BYTES};
pub use self::cost::{HANDLER_CALL_NS, SuiteCost};
pub use self::layer::{NodeLayer, NodeSets, NodeValues};
pub use self::mem::{CHUNKS_PER_CONN, Ep, SESSIONS};
pub use self::shared::{SetupError, Shared, identity_seed, iface_ip};
use crate::sim::stuck;
use crate::suite::proto::host::Layers;
use crate::suite::world::model::Intent;
use crate::{Clock, IfaceEvent, Node, StreamEvent, StreamId, StreamOp, Time, Transmit, Work};

/// A scenario command for a suite node.
#[derive(Debug)]
pub enum Cmd {
    /// Export the endpoint state into the persisted bytes (the runner sends it every 60 s).
    Persist,
    /// The node leaves on purpose (leave or upgrade): the endpoint closes its sessions and exports its state; the runner
    /// crashes the node at the same time.
    Shutdown,
    /// The oracle revoked this peer: end its sessions and refuse it from now on.
    Revoke(usize),
    /// An application intent for the layers.
    Intent(Box<Intent>),
    /// The adversary compromised this node: its identity seed and current state become known to it.
    Compromise,
}

/// What a suite node reports to the engine's event log (session level only, so a trace stays small).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NodeEvent {
    /// An incarnation started; `restored` says it loaded persisted state.
    Started {
        /// State was restored.
        restored: bool,
    },
    /// The node stopped for good: a graceful leave (a crash is the engine's own record).
    Stopped,
    /// A dial of this node is open.
    Connected {
        /// The peer's world index.
        peer: usize,
        /// The session resumed an earlier one.
        resumed: bool,
    },
    /// A peer's session is open.
    Incoming {
        /// The peer's world index.
        peer: usize,
    },
    /// A dial ended without a session.
    ConnectFailed {
        /// The peer's world index.
        peer: usize,
        /// Why the endpoint gave up; `None` when the node itself closed the session (a revoked peer).
        reason: Option<pinc_core::ConnectFailure>,
    },
    /// A session ended.
    Closed {
        /// The peer's world index.
        peer: usize,
    },
    /// The oracle revoked a peer.
    Revoked {
        /// The peer's world index.
        peer: usize,
    },
    /// The node was suspended.
    Suspended,
    /// The node resumed.
    Resumed,
}

/// One node of a suite run; see the module docs.
pub struct SuiteNode<L: Layers> {
    core: Core,
    layers: L,
    /// The time of the last link-returned record: the interfaces of one handover come up together and count once.
    link_returned_at: Option<Time>,
}

impl<L: Layers> SuiteNode<L> {
    /// Node `idx` of the shared world, running `layers`. The node starts stopped.
    ///
    /// # Errors
    /// [`SetupError::NoSuchNode`] if `idx` is not in the world, or an identity error.
    pub fn new(shared: Rc<Shared>, idx: usize, layers: L) -> Result<Self, SetupError> {
        Ok(Self {
            core: Core::new(shared, idx)?,
            layers,
            link_returned_at: None,
        })
    }

    /// The node's index in the world.
    pub fn idx(&self) -> usize {
        self.core.idx
    }

    /// The layers, for inspection.
    pub fn layers(&self) -> &L {
        &self.layers
    }

    /// The layers, mutably.
    pub fn layers_mut(&mut self) -> &mut L {
        &mut self.layers
    }

    /// Whether an incarnation is running.
    pub fn running(&self) -> bool {
        self.core.running()
    }

    /// How many incarnations have started.
    pub fn incarnation(&self) -> u64 {
        self.core.incarnation
    }

    /// The largest exported state so far in bytes (the recorder's `NodeFacts.export_max`).
    pub fn max_export(&self) -> usize {
        self.core.max_export
    }

    /// The bytes the node would return from a crash now: the last exported state.
    pub fn exported(&self) -> &[u8] {
        &self.core.persisted
    }

    /// The seed of the node's identity key.
    pub fn identity_seed(&self) -> [u8; 32] {
        self.core.seed
    }

    /// Timer calls that left the endpoint's deadline due twice in a row (each is a defect of the endpoint).
    pub fn timer_violations(&self) -> u64 {
        self.core.timer_violations
    }

    /// The nanoseconds of CPU the node has reported in all, for the recorder's total.
    pub fn cpu_ns(&self) -> u64 {
        self.core.cpu_ns
    }

    /// The CPU the node was charged, by part.
    pub fn cpu_parts(&self) -> CpuParts {
        self.core.cpu_parts
    }

    /// The estimate of the live state in bytes (see [`SESSION_STATE_BYTES`]); zero when stopped.
    pub fn state_bytes(&self) -> u64 {
        self.core.state_bytes()
    }

    /// The endpoint's numbers and its sessions, one line each, for diagnosis.
    pub fn describe(&self) -> Vec<String> {
        let Some(ep) = self.core.endpoint() else {
            let notices = self.core.notices.iter().map(|n| format!("notice {n}"));
            return std::iter::once("stopped".to_owned()).chain(notices).collect();
        };
        let mut out = vec![format!("{:?}", ep.node_stats())];
        out.extend(self.core.notices.iter().map(|n| format!("notice {n}")));
        out.push(self.core.wire_summary());
        if let Some(h) = self.core.hub.as_ref().filter(|h| h.datagrams_dropped > 0) {
            out.push(format!("hub datagrams_dropped {}", h.datagrams_dropped));
        }
        for n in 0..SESSIONS {
            if let pinc_core::Answer::Stats(st) = ep.query(pinc_core::Query::SessionAt(n)) {
                out.push(format!(
                    "session {:?} peer {:?} alpn {:?} dialer {} established {} allowed {} held {} route {:?} heard {} pto_count {}",
                    st.session,
                    st.node.map(|n| self.core.shared.index_of(&n)),
                    st.alpn.map(|a| String::from_utf8_lossy(a.as_bytes()).into_owned()),
                    st.dialer, st.established, st.allowed, st.held, st.route, st.heard, st.pto_count
                ));
            }
        }
        out
    }

    /// Sessions the endpoint holds now.
    pub fn sessions(&self) -> usize {
        self.core.endpoint().map_or(0, |e| e.node_stats().sessions)
    }

    /// The membership view as `(epoch, members)` with members as world indices; `None` when the node is stopped.
    pub fn view(&self) -> Option<(u64, Vec<usize>)> {
        self.core.view()
    }

    /// The node's address changed while it was suspended or stopped: the next resume says it moved.
    pub fn mark_moved(&mut self) {
        self.core.moved = true;
    }

    /// Record that the interface with this address is up or down without telling the endpoint, for a change the
    /// simulator did not deliver because the node was not running. The next incarnation starts from this state.
    pub fn set_iface_up(&mut self, ip: IpAddr, up: bool) {
        if up {
            self.core.iface_up(ip);
        } else {
            self.core.iface_down(ip);
        }
    }

    fn enter(&mut self, now: Time) {
        self.core.tick(now);
    }

    /// One turn of the host loop: the node's pending work, its events for the layers, the key answers, streams and
    /// datagrams it asked for. Returns whether anything moved.
    fn pump(&mut self) -> bool {
        let mut did = false;
        if let Some(node) = self.core.node.as_mut() {
            node.poll(self.core.local);
        }
        did |= self.core.service(&mut self.layers);
        did |= self.core.keys_step();
        did |= self.core.io_step();
        did |= self.core.udp_step();
        did |= self.core.streams_out_step();
        did
    }

    /// Handle the events of the last call until none is left, then sample the state size.
    fn settle(&mut self) {
        for _ in 0..SETTLE_ROUNDS {
            if !self.pump() {
                self.core.sample();
                return;
            }
        }
        self.core.violation("G-SPEC", "the host loop of a node does not settle");
        self.core.sample();
    }

    fn graceful_stop(&mut self, now: Time) {
        self.core.events.push_back(NodeEvent::Stopped);
        self.core.shared.rec.borrow_mut().node_stopped(self.core.idx, now, true);
        self.layers.stop();
        self.core.phase = Phase::Left;
    }
}

impl<L: Layers> Node for SuiteNode<L> {
    type Cmd = Cmd;
    type Event = NodeEvent;

    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        self.core.calls += 1;
        let hdr = if local.is_ipv4() { 28 } else { 48 };
        let size = data.len() as u64 + hdr;
        self.core
            .shared
            .rec
            .borrow_mut()
            .udp_received(self.core.idx, now, remote, size, 0);
        if self.core.shared.is_watched(self.core.idx) && in_trace_window(self.core.now) {
            if wide_window() {
                self.core
                    .shared
                    .note_net(self.core.idx, true, self.core.now, remote, data.len());
            } else {
                let first = data.first().copied().unwrap_or(0);
                self.core.shared.note_trace(format!(
                    "n{} true{} RX {remote} -> {local} len {} first {first:#x}",
                    self.core.idx,
                    self.core.now,
                    data.len()
                ));
            }
        }
        self.core.handle_datagram(local, remote, data);
        self.settle();
    }

    fn poll_transmit(&mut self, now: Time, buf: &mut [u8]) -> Option<Transmit> {
        if !self.core.running() {
            return None;
        }
        self.enter(now);
        loop {
            if let Some((local, remote, len)) = self.core.next_datagram(buf) {
                if self.core.shared.is_watched(self.core.idx) && in_trace_window(self.core.now) {
                    if wide_window() {
                        self.core
                            .shared
                            .note_net(self.core.idx, false, self.core.now, remote, len);
                    } else {
                        let first = buf.first().copied().unwrap_or(0);
                        self.core.shared.note_trace(format!(
                            "n{} true{} TX {local} -> {remote} len {len} first {first:#x}",
                            self.core.idx, self.core.now
                        ));
                    }
                }
                self.core.record_wire(remote, local, buf.get(..len)?);
                return Some(Transmit {
                    local,
                    remote,
                    len,
                    send_at: None,
                });
            }
            // The node may have events of its own (a closed session, a writable stream) that make the layers
            // write more; handle them before saying nothing is left.
            if !self.pump() {
                self.core.sample();
                return None;
            }
        }
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        if !self.core.running() {
            return None;
        }
        if std::mem::take(&mut self.core.timer_check) {
            // A deadline that is already due is normal while the host has not yet called back; one that two timer
            // calls in a row left due is a timer the endpoint cannot act on.
            let (local, d) = (self.core.local, self.core.endpoint().and_then(Ep::poll_timeout));
            if stuck(&mut self.core.timer_last, &mut self.core.timer_left, local, d) {
                self.core.timer_violations += 1;
            }
        }
        let layers = self.layers.poll_timeout().filter(|_| self.core.deliver());
        self.core.next_deadline().into_iter().chain(layers).min()
    }

    fn handle_timeout(&mut self, now: Time) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        self.core.calls += 1;
        self.core.run_timers();
        if self.core.deliver() && self.layers.poll_timeout().is_some_and(|d| d <= self.core.now) {
            let local = self.core.now;
            self.layers.timeout(local, &mut self.core);
        }
        self.settle();
    }

    fn command(&mut self, now: Time, cmd: Cmd) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        self.core.calls += 1;
        match cmd {
            Cmd::Persist => self.core.persisted = self.core.export(),
            Cmd::Shutdown => {
                let local = self.core.local;
                if let Some(node) = self.core.node.as_mut() {
                    node.leave(local);
                }
                self.core.persisted = self.core.export();
                self.graceful_stop(now);
            }
            Cmd::Revoke(peer) => self.core.revoke(peer),
            Cmd::Intent(intent) => {
                if self.core.deliver() {
                    let local = self.core.now;
                    self.layers.intent(local, &mut self.core, &intent);
                }
            }
            Cmd::Compromise => {
                let state = self.core.export();
                self.core
                    .shared
                    .registry
                    .note_compromise(self.core.idx, now, &self.core.seed, &state);
            }
        }
        self.settle();
    }

    fn poll_event(&mut self) -> Option<NodeEvent> {
        self.core.events.pop_front()
    }

    fn crash(&mut self, now: Time) -> Vec<u8> {
        if self.core.running() {
            self.enter(now);
            if self.core.phase != Phase::Left {
                self.core
                    .shared
                    .rec
                    .borrow_mut()
                    .node_stopped(self.core.idx, now, false);
                self.layers.stop();
            }
            self.core.end();
        }
        self.core.persisted.clone()
    }

    fn restart(&mut self, now: Time, persisted: &[u8]) {
        let alpns = self.layers.alpns();
        let Some(restored) = self.core.begin(now, persisted, &alpns) else {
            return;
        };
        self.core.events.push_back(NodeEvent::Started { restored });
        self.core.shared.rec.borrow_mut().node_started(self.core.idx, now);
        let local = self.core.now;
        self.layers.boot(local, &mut self.core);
        if self.core.shared.restart_action_at(self.core.idx, now) {
            let open = self.layers.has_open_intents(local);
            self.core
                .shared
                .rec
                .borrow_mut()
                .restarted_with_state(self.core.idx, now, open);
        }
        self.settle();
    }

    fn suspend(&mut self, now: Time) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        let (local, wall) = (self.core.local, self.core.wall_ms());
        if let Some(node) = self.core.node.as_mut() {
            node.suspend(local, wall);
        }
        self.core.events.push_back(NodeEvent::Suspended);
        self.settle();
    }

    fn resume(&mut self, now: Time) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        let moved = std::mem::take(&mut self.core.moved);
        let local = self.core.local;
        if let Some(node) = self.core.node.as_mut() {
            node.resume(local, moved);
        }
        self.core.events.push_back(NodeEvent::Resumed);
        let open = self.layers.has_open_intents(self.core.now);
        self.core.shared.rec.borrow_mut().resumed(self.core.idx, now, open);
        self.settle();
    }

    fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        self.enter(now);
        match event {
            IfaceEvent::Up(ip) => {
                self.core.iface_up(ip);
                if self.core.running() && self.link_returned_at.replace(now) != Some(now) {
                    let open = self.layers.has_open_intents(self.core.now);
                    self.core
                        .shared
                        .rec
                        .borrow_mut()
                        .link_returned(self.core.idx, now, open);
                }
            }
            IfaceEvent::Down(ip) => self.core.iface_down(ip),
            IfaceEvent::Changed { old, new } => self.core.iface_changed(old, new),
        }
        self.settle();
    }

    fn take_work(&mut self) -> Work {
        let w = self.core.shared.registry.peek_work(self.core.idx);
        let crypto = self.core.shared.registry.take_work(self.core.idx, &self.core.costs);
        let io = self.core.io_acc.floor();
        self.core.io_acc -= io;
        let calls = std::mem::take(&mut self.core.calls);
        let ns = crypto + calls * HANDLER_CALL_NS + io as u64;
        self.core.cpu_ns += ns;
        let p = &mut self.core.cpu_parts;
        p.crypto_ns += crypto;
        p.calls += calls;
        p.io_ns += io as u64;
        p.aead += w.aead;
        p.aead_bytes += w.aead_bytes;
        p.hash_bytes += w.hash_bytes;
        Work { ticks: 0, ns }
    }

    fn clock_changed(&mut self, _now: Time, clock: &Clock) {
        self.core.clock = clock.clone();
    }

    fn poll_stream(&mut self, _now: Time, buf: &mut [u8]) -> Option<StreamOp> {
        let (op, data) = self.core.wire.ops.pop_front()?;
        buf.get_mut(..data.len())?.copy_from_slice(&data);
        Some(op)
    }

    fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        self.core.calls += 1;
        self.core.stream_event(event);
        self.settle();
    }

    fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        if !self.core.running() {
            return;
        }
        self.enter(now);
        self.core.calls += 1;
        self.core.stream_record(stream, data);
        self.settle();
    }
}
