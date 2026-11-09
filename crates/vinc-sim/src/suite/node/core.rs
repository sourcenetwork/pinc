//! The part of a suite node that owns the endpoint: its keys, sessions, interfaces and the host duties.
//!
//! [`Core`] is everything except the protocol layers, so a layer can be handed `&mut Core` as its
//! [`Host`](crate::suite::proto::host::Host) while the layers themselves stay a separate field of the node. The
//! endpoint is SANS-IO: every command's reply events and every polled event end up in one queue that
//! [`Core::service`] drains, answering key requests and access checks itself and turning the rest into
//! [`LayerEvent`]s.
//!
//! Invariants: all endpoint time is the node's local time (the simulator's clock for this node plus a fixed base so it
//! is never negative, and never going backward); no borrow of the recorder is held across a call into a layer; a
//! session the node closed on its own (a revoked or unknown peer) is hidden from the layers for its whole life.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{IpAddr, SocketAddr};
use std::rc::Rc;

use vinc_core::{
    Answer, Command, CommandError, EndpointConfig, Event, IfaceEvent as EpIfaceEvent, IfaceId, Query, Reply, Role,
    SessionId, Value, state_len,
};
use vinc_crypto::identity::MAX_SIGNATURE_LEN;
use vinc_crypto::{Drbg, Keypair, Software};
use vinc_security::{Alpn, Env, KeyHandle, KeyRequest, LocalIdentity, PrekeyPolicy, SoftKeys, SoftPrekeys};
use vinc_transport::stream::{NoSource, RecvStatus};

use super::mem::{CLIENT_TICKETS, Ep, recycle, slots};
use super::shared::{Shared, derive, make_identity};
use super::{NodeEvent, SetupError};
use crate::Clock;
use crate::suite::crypto::{DeviceCosts, Tracked};
use crate::suite::proto::host::{Host, LayerEvent, Layers};

/// The local time of a node at true time zero with a perfect clock: one hour, so a negative clock offset never
/// makes the endpoint's time negative.
pub const LOCAL_BASE: u64 = 3_600_000_000_000;
/// The most same-size datagrams the endpoint batches into one transmit.
pub const MAX_GSO: usize = 8;
/// The close code of a session the node ends because the peer is revoked or unknown (the access-denied code).
const CLOSE_DENIED: u64 = 3;
const SECOND: u64 = 1_000_000_000;

/// The estimate of the memory one live session holds, in bytes: one pool chunk plus its tables. The endpoint keeps no
/// byte accounting of its own, so the state size the node reports is built from counts it does expose.
pub const SESSION_STATE_BYTES: u64 = 20_480;
/// The estimate of one amplification-ledger entry, in bytes.
pub const LEDGER_ENTRY_BYTES: u64 = 64;
/// The size of one remembered round trip in the exported state format, used as its memory estimate.
pub const PEER_ENTRY_BYTES: u64 = 41;

/// One interface of the node as the endpoint sees it.
pub(super) struct IfEntry {
    ip: IpAddr,
    port: u16,
    up: bool,
    id: Option<IfaceId>,
}

/// Where an incarnation is in its life.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Phase {
    /// No endpoint.
    Stopped,
    /// The endpoint runs and the layers get events.
    Running,
    /// The node left on purpose: the endpoint still sends its closes, the layers are stopped.
    Left,
}

struct Sess {
    peer: usize,
    hidden: bool,
}

/// How the node knows a session an event names.
enum Known {
    Visible(usize),
    Hidden,
    Unknown,
}

pub(super) struct Core {
    pub(super) shared: Rc<Shared>,
    pub(super) idx: usize,
    pub(super) costs: DeviceCosts,
    pub(super) kp: Keypair,
    pub(super) identity: LocalIdentity,
    pub(super) seed: [u8; 32],
    pub(super) incarnation: u64,
    pub(super) last_start: u64,
    pub(super) phase: Phase,
    ep: Option<Box<Ep>>,
    prekeys: Option<SoftPrekeys<Tracked>>,
    drbg: Drbg,
    sessions: BTreeMap<SessionId, Sess>,
    queue: VecDeque<Event>,
    acp: VecDeque<(u64, u64, bool)>,
    pub(super) clock: Clock,
    pub(super) now: u64,
    pub(super) local: u64,
    pub(super) revoked: BTreeSet<usize>,
    pub(super) ifaces: Vec<IfEntry>,
    pub(super) moved: bool,
    scratch: Vec<u8>,
    pub(super) events: VecDeque<NodeEvent>,
    stash: Vec<u8>,
    stash_at: usize,
    stash_route: Option<(SocketAddr, SocketAddr, usize)>,
    pub(super) io_acc: f64,
    pub(super) calls: u64,
    pub(super) cpu_ns: u64,
    pub(super) persisted: Vec<u8>,
    pub(super) max_export: usize,
    pub(super) next_sample: u64,
    pub(super) timer_violations: u64,
}

impl Core {
    pub(super) fn new(shared: Rc<Shared>, idx: usize) -> Result<Self, SetupError> {
        let spec = shared.world.nodes.get(idx).ok_or(SetupError::NoSuchNode(idx))?;
        let (kp, identity) = make_identity(shared.world.seed, idx)?;
        let ifaces = spec
            .ifaces
            .iter()
            .filter(|f| f.kind.starts_with("udp"))
            .filter_map(|f| {
                Some(IfEntry {
                    ip: super::shared::iface_ip(&f.addr)?,
                    port: f.addr.port,
                    up: true,
                    id: None,
                })
            })
            .collect();
        let costs = shared.costs(idx);
        let seed = super::shared::identity_seed(shared.world.seed, idx);
        Ok(Self {
            idx,
            costs,
            kp,
            identity,
            seed,
            incarnation: 0,
            last_start: 0,
            phase: Phase::Stopped,
            ep: None,
            prekeys: None,
            drbg: Drbg::new(&derive(b"suite-keys", shared.world.seed, idx as u64, 0)),
            sessions: BTreeMap::new(),
            queue: VecDeque::new(),
            acp: VecDeque::new(),
            clock: Clock::default(),
            now: 0,
            local: LOCAL_BASE,
            revoked: BTreeSet::new(),
            ifaces,
            moved: false,
            scratch: Vec::new(),
            events: VecDeque::new(),
            stash: Vec::new(),
            stash_at: 0,
            stash_route: None,
            io_acc: 0.0,
            calls: 0,
            cpu_ns: 0,
            persisted: Vec::new(),
            max_export: 0,
            next_sample: 0,
            timer_violations: 0,
            shared,
        })
    }

    /// Set the true time of the next calls and tell the ledger whose work and time they are.
    pub(super) fn tick(&mut self, now: u64) {
        self.now = now;
        self.shared.registry.now.set(now);
        self.shared.registry.enter(self.idx);
        let local = u64::try_from(i128::from(self.clock.local(now)) + i128::from(LOCAL_BASE)).unwrap_or(0);
        self.local = self.local.max(local);
    }

    /// The true time at which the local time `deadline` is reached.
    pub(super) fn to_true(&self, deadline: u64) -> u64 {
        let rel = i64::try_from(deadline).unwrap_or(i64::MAX) - LOCAL_BASE.cast_signed();
        self.clock.to_true(self.now, rel)
    }

    pub(super) fn running(&self) -> bool {
        self.phase != Phase::Stopped
    }

    /// Layers receive events only while the node has not left.
    pub(super) fn deliver(&self) -> bool {
        self.phase == Phase::Running
    }

    pub(super) fn endpoint(&self) -> Option<&Ep> {
        self.ep.as_deref()
    }

    pub(super) fn violation(&self, gate: &str, msg: &str) {
        self.shared.rec.borrow_mut().violation(self.now, gate, self.idx, msg);
    }

    fn provider(&self) -> Tracked {
        Tracked::new(self.shared.registry, self.idx, Software)
    }

    // ---- life ----

    /// Build a fresh endpoint, restore `persisted` unless this restart keeps no state, and register `alpns`.
    /// Returns whether state was restored; `None` if the endpoint could not be built.
    pub(super) fn begin(&mut self, now: u64, persisted: &[u8], alpns: &[&'static [u8]]) -> Option<bool> {
        self.tick(now);
        self.incarnation += 1;
        let stateless = self.shared.restarts_stateless(self.idx, self.last_start, now);
        self.last_start = now;
        self.clear_volatile();
        let Some(table) = slots() else {
            self.violation("G-SPEC", "the node could not allocate its connection memory");
            return None;
        };
        let prov = self.provider();
        let world_seed = self.shared.world.seed;
        let inc = self.incarnation;
        let mut cfg = EndpointConfig::new(u64::from_be_bytes(first8(&derive(
            b"suite-cfg",
            world_seed,
            self.idx as u64,
            inc,
        ))));
        cfg.conn.max_gso = MAX_GSO;
        let ep_drbg = Drbg::new(&derive(b"suite-endpoint", world_seed, self.idx as u64, inc));
        let mut ep = Box::new(Ep::new(self.local, prov, ep_drbg, self.identity, cfg, table));
        self.drbg = Drbg::new(&derive(b"suite-keys", world_seed, self.idx as u64, inc));
        let mut env = Env {
            provider: &prov,
            now: self.local,
            drbg: &mut self.drbg,
        };
        match SoftPrekeys::new(&mut env, PrekeyPolicy::default()) {
            Ok(mut keys) => {
                // vertexia: one prekey per incarnation, never rotated; ceiling is an incarnation longer than the
                // policy lifetime (10 minutes) still using it, upgrade path is a rotation timer calling `acquire`.
                match keys.acquire(&mut env) {
                    Ok(info) => ep.set_prekey(info),
                    Err(_) => self.violation("G-SPEC", "the node could not make a prekey"),
                }
                self.prekeys = Some(keys);
            }
            Err(_) => self.violation("G-SPEC", "the node could not make a prekey"),
        }
        for a in alpns {
            if !ep.register_alpn(a) {
                self.violation("G-SPEC", "the endpoint refused a protocol name");
            }
        }
        let mut restored = false;
        if !stateless && !persisted.is_empty() {
            match ep.restore_state(self.local, persisted) {
                Ok(_) => {
                    restored = true;
                    self.persisted = persisted.to_vec();
                }
                Err(_) => self.violation("G-SPEC", "the persisted node state could not be restored"),
            }
        }
        if !restored {
            self.persisted.clear();
        }
        for e in &mut self.ifaces {
            e.id = None;
            if e.up {
                e.id = ep.add_iface(SocketAddr::new(e.ip, e.port));
            }
        }
        self.ep = Some(ep);
        self.phase = Phase::Running;
        self.next_sample = 0;
        Some(restored)
    }

    fn clear_volatile(&mut self) {
        if let Some(ep) = self.ep.take() {
            recycle(*ep);
        }
        self.prekeys = None;
        self.sessions.clear();
        self.queue.clear();
        self.acp.clear();
        self.stash.clear();
        self.stash_at = 0;
        self.stash_route = None;
        self.phase = Phase::Stopped;
    }

    /// Drop everything volatile (the process died or the node left).
    pub(super) fn end(&mut self) {
        self.clear_volatile();
    }
}

impl Drop for Core {
    fn drop(&mut self) {
        self.clear_volatile();
    }
}

impl Core {
    // ---- commands to the endpoint ----

    pub(super) fn cmd(&mut self, c: Command<'_, NoSource>) -> Result<Reply, CommandError> {
        let ep = self.ep.as_mut().ok_or(CommandError::NoSession)?;
        let r = ep.command(self.local, c)?;
        self.queue.extend(r.events.iter().copied());
        Ok(r)
    }

    pub(super) fn handle_datagram(&mut self, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if let Some(ep) = self.ep.as_mut() {
            ep.handle_datagram(self.local, local, remote, data);
        }
    }

    /// Run the endpoint timers that are due and answer the access checks whose answer time has come. Returns
    /// whether the endpoint's own timer was due.
    pub(super) fn run_timers(&mut self) -> bool {
        while self.acp.front().is_some_and(|&(due, ..)| due <= self.now) {
            if let Some((_, check, allow)) = self.acp.pop_front() {
                // An answer for a check the endpoint dropped meanwhile is refused; there is nothing to repair.
                let _ = self.cmd(Command::AcpAnswer { check, allow });
            }
        }
        let local = self.local;
        let Some(ep) = self.ep.as_mut() else { return false };
        let due = ep.poll_timeout().is_some_and(|d| d <= local);
        if due {
            ep.handle_timeout(local);
            if ep.poll_timeout().is_some_and(|d| d <= local) {
                self.timer_violations += 1;
            }
        }
        due
    }

    /// The next true time the endpoint or an access answer wants a call.
    pub(super) fn next_deadline(&self) -> Option<u64> {
        let ep = self.ep.as_ref().and_then(|e| e.poll_timeout()).map(|d| self.to_true(d));
        let acp = self.acp.front().map(|&(due, ..)| due);
        ep.into_iter().chain(acp).min()
    }

    /// Next datagram: the rest of a batch, or a fresh batch from the endpoint (one transmit call recorded). The
    /// datagram is written to `buf`; returns `(local, remote, len)`.
    pub(super) fn next_datagram(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, SocketAddr, usize)> {
        if let Some((local, remote, seg)) = self.stash_route {
            let rest = self.stash.get(self.stash_at..)?;
            let n = rest.len().min(seg);
            buf.get_mut(..n)?.copy_from_slice(rest.get(..n)?);
            self.stash_at += n;
            if self.stash_at >= self.stash.len() {
                self.stash_route = None;
                self.stash.clear();
                self.stash_at = 0;
            }
            return Some((local, remote, n));
        }
        let ep = self.ep.as_mut()?;
        let tx = ep.poll_transmit(self.local, buf)?;
        let segs = tx.len.div_ceil(tx.segment_size.max(1));
        self.shared.rec.borrow_mut().transmit_call(self.idx, self.now);
        self.io_acc += self.costs.io_call + self.costs.io_seg * segs as f64;
        let first = tx.len.min(tx.segment_size.max(1));
        if tx.len > first {
            self.stash.clear();
            self.stash.extend_from_slice(buf.get(first..tx.len)?);
            self.stash_at = 0;
            self.stash_route = Some((tx.local, tx.remote, tx.segment_size));
        }
        Some((tx.local, tx.remote, first))
    }

    /// Record a datagram the node puts on the wire: wire bytes, plaintext payload and third-party bytes.
    pub(super) fn record_wire(&self, remote: SocketAddr, local: SocketAddr, bytes: &[u8]) {
        let scan = self.shared.registry.scan_wire(self.idx, bytes);
        let hdr = if local.is_ipv4() { 28 } else { 48 };
        self.shared.rec.borrow_mut().wire(
            self.idx,
            self.now,
            bytes.len() as u64 + hdr,
            scan.third_party,
            scan.plaintext_payload,
            false,
            0,
            Some(remote),
        );
    }

    // ---- state ----

    /// The endpoint's exported state, or nothing if it is down or the export failed.
    pub(super) fn export(&mut self) -> Vec<u8> {
        let Some(ep) = self.ep.as_ref() else { return Vec::new() };
        let mut out = vec![0u8; state_len(CLIENT_TICKETS)];
        if let Ok(n) = ep.export_state(self.local, &mut out) {
            out.truncate(n);
            self.max_export = self.max_export.max(n);
            out
        } else {
            self.violation("G-SPEC", "the node state could not be exported");
            Vec::new()
        }
    }

    /// The estimate of the node's live state in bytes: sessions, ledger entries and remembered round trips at the
    /// documented per-item sizes. The endpoint holds no byte accounting of its own.
    pub(super) fn state_bytes(&self) -> u64 {
        let Some(ep) = self.ep.as_ref() else { return 0 };
        let st = ep.node_stats();
        st.sessions as u64 * SESSION_STATE_BYTES
            + st.ledger as u64 * LEDGER_ENTRY_BYTES
            + ep.rtt().peers().count() as u64 * PEER_ENTRY_BYTES
    }

    /// Report the state size to the recorder at most once per virtual second.
    pub(super) fn sample(&mut self) {
        if !self.running() || self.now < self.next_sample {
            return;
        }
        self.next_sample = self.now + SECOND;
        let bytes = self.state_bytes();
        self.shared.rec.borrow_mut().state_sample(self.now, self.idx, bytes);
    }

    // ---- interfaces ----

    pub(super) fn iface_up(&mut self, ip: IpAddr) {
        let (local, ep) = (self.local, self.ep.as_mut());
        if let Some(e) = self.ifaces.iter_mut().find(|e| e.ip == ip) {
            e.up = true;
            if let Some(ep) = ep {
                if e.id.is_none() {
                    e.id = ep.add_iface(SocketAddr::new(e.ip, e.port));
                }
                if let Some(id) = e.id {
                    ep.iface_event(local, id, EpIfaceEvent::Up);
                }
            }
            return;
        }
        // An address the node does not have: a handover. The interface of the same family that is down takes the new
        // address, as the endpoint expects (a down, an address change, then an up).
        let v4 = ip.is_ipv4();
        let port = self
            .ifaces
            .iter()
            .find(|e| e.ip.is_ipv4() == v4)
            .map_or(4433, |e| e.port);
        let slot = self.ifaces.iter_mut().find(|e| e.ip.is_ipv4() == v4 && !e.up);
        match (slot, ep) {
            (Some(e), Some(ep)) => {
                e.ip = ip;
                e.up = true;
                match e.id {
                    Some(id) => {
                        ep.iface_event(local, id, EpIfaceEvent::AddrChange(SocketAddr::new(ip, e.port)));
                        ep.iface_event(local, id, EpIfaceEvent::Up);
                    }
                    None => e.id = ep.add_iface(SocketAddr::new(ip, e.port)),
                }
            }
            (Some(e), None) => {
                e.ip = ip;
                e.up = true;
            }
            (None, ep) => {
                let id = ep.and_then(|ep| ep.add_iface(SocketAddr::new(ip, port)));
                self.ifaces.push(IfEntry { ip, port, up: true, id });
            }
        }
    }

    pub(super) fn iface_down(&mut self, ip: IpAddr) {
        let (local, ep) = (self.local, self.ep.as_mut());
        if let Some(e) = self.ifaces.iter_mut().find(|e| e.ip == ip) {
            e.up = false;
            if let (Some(ep), Some(id)) = (ep, e.id) {
                ep.iface_event(local, id, EpIfaceEvent::Down);
            }
        }
    }

    pub(super) fn iface_changed(&mut self, old: IpAddr, new: IpAddr) {
        let (local, ep) = (self.local, self.ep.as_mut());
        if let Some(e) = self.ifaces.iter_mut().find(|e| e.ip == old) {
            e.ip = new;
            if let (Some(ep), Some(id)) = (ep, e.id) {
                ep.iface_event(local, id, EpIfaceEvent::AddrChange(SocketAddr::new(new, e.port)));
            }
        }
    }

    // ---- events ----

    /// Handle every event the endpoint and the last commands produced. Returns whether there was any.
    pub(super) fn service<L: Layers>(&mut self, layers: &mut L) -> bool {
        let mut any = false;
        loop {
            let ev = match self.ep.as_mut().and_then(|e| e.poll_event()) {
                Some(e) => e,
                None => match self.queue.pop_front() {
                    Some(e) => e,
                    None => return any,
                },
            };
            any = true;
            self.on_event(layers, ev);
        }
    }

    fn known(&self, session: SessionId) -> Known {
        match self.sessions.get(&session) {
            Some(s) if s.hidden => Known::Hidden,
            Some(s) => Known::Visible(s.peer),
            None => Known::Unknown,
        }
    }

    fn visible(&mut self, session: SessionId) -> Option<usize> {
        match self.known(session) {
            Known::Visible(p) => Some(p),
            Known::Hidden => None,
            Known::Unknown => {
                self.violation("G-SPEC", "the endpoint named a session the node never opened");
                None
            }
        }
    }

    fn on_event<L: Layers>(&mut self, layers: &mut L, ev: Event) {
        match ev {
            Event::KeyRequest { session } => self.answer_keys(session),
            Event::AcpCheck { check, node, .. } => {
                let principal = self.shared.index_of(&node);
                let (allow, _) = self.shared.rec.borrow_mut().acp_decide(self.now, self.idx, principal);
                self.acp
                    .push_back((self.now + self.shared.world.acp_latency_ns, check, allow));
            }
            Event::Connected {
                session,
                node,
                alpn,
                resumed,
            } => self.on_open(layers, session, node, alpn, true, resumed),
            Event::Incoming { session, node, alpn } => self.on_open(layers, session, node, alpn, false, false),
            Event::ConnectFailed { node, alpn, reason } => {
                if let Some(peer) = self.shared.index_of(&node) {
                    self.events.push_back(NodeEvent::ConnectFailed {
                        peer,
                        reason: Some(reason),
                    });
                    if self.deliver() {
                        let (local, bytes) = (self.now, alpn.as_bytes());
                        layers.event(local, self, LayerEvent::ConnectFailed { peer, alpn: bytes });
                    }
                }
            }
            Event::Closed { session, .. } => match self.sessions.remove(&session) {
                Some(s) if !s.hidden => {
                    self.events.push_back(NodeEvent::Closed { peer: s.peer });
                    if self.deliver() {
                        let local = self.now;
                        layers.event(local, self, LayerEvent::Closed { session });
                    }
                }
                Some(_) => {}
                None => self.violation("G-SPEC", "the endpoint named a session the node never opened"),
            },
            Event::StreamOpened { session, stream } => {
                if self.visible(session).is_some() && self.deliver() {
                    let local = self.now;
                    layers.event(local, self, LayerEvent::StreamOpened { session, stream });
                }
            }
            Event::StreamReadable { session, stream } => {
                if self.visible(session).is_some() {
                    self.read_stream(layers, session, stream);
                }
            }
            Event::StreamWritable { session, stream } => {
                if self.visible(session).is_some() && self.deliver() {
                    let local = self.now;
                    layers.event(local, self, LayerEvent::StreamWritable { session, stream });
                }
            }
            Event::StreamReset { session, stream, .. } => {
                if self.visible(session).is_some() && self.deliver() {
                    let local = self.now;
                    layers.event(local, self, LayerEvent::StreamReset { session, stream });
                }
            }
            Event::DatagramReceived { .. }
            | Event::PathChanged { .. }
            | Event::PeerAsleep { .. }
            | Event::PeerAwake { .. }
            | Event::ReachOut { .. }
            | Event::TicketsReceived { .. } => {}
        }
    }

    fn on_open<L: Layers>(
        &mut self,
        layers: &mut L,
        session: SessionId,
        node: vinc_crypto::NodeId,
        alpn: Alpn,
        dialed: bool,
        resumed: bool,
    ) {
        let peer = self.shared.index_of(&node);
        let hide = peer.is_none_or(|p| self.revoked.contains(&p));
        self.sessions.insert(
            session,
            Sess {
                peer: peer.unwrap_or(usize::MAX),
                hidden: hide,
            },
        );
        let Some(peer) = peer.filter(|_| !hide) else {
            let _ = self.cmd(Command::Close {
                session,
                error: CLOSE_DENIED,
            });
            if dialed && let Some(peer) = peer {
                self.events.push_back(NodeEvent::ConnectFailed { peer, reason: None });
                if self.deliver() {
                    let local = self.now;
                    layers.event(
                        local,
                        self,
                        LayerEvent::ConnectFailed {
                            peer,
                            alpn: alpn.as_bytes(),
                        },
                    );
                }
            }
            return;
        };
        let (local, bytes) = (self.now, alpn.as_bytes());
        if dialed {
            self.events.push_back(NodeEvent::Connected { peer, resumed });
            if self.deliver() {
                layers.event(
                    local,
                    self,
                    LayerEvent::Connected {
                        session,
                        peer,
                        alpn: bytes,
                    },
                );
            }
        } else {
            self.events.push_back(NodeEvent::Incoming { peer });
            if self.deliver() {
                layers.event(
                    local,
                    self,
                    LayerEvent::Incoming {
                        session,
                        peer,
                        alpn: bytes,
                    },
                );
            }
        }
    }

    /// Read everything readable on a stream, consume it, and hand it to the layers in one piece.
    fn read_stream<L: Layers>(&mut self, layers: &mut L, session: SessionId, stream: u64) {
        let mut buf = std::mem::take(&mut self.scratch);
        buf.clear();
        let mut fin = false;
        loop {
            let n = match self.ep.as_ref().map(|e| e.query(Query::Read { session, stream })) {
                Some(Answer::Chunk(c)) if !c.is_empty() => {
                    buf.extend_from_slice(c);
                    c.len()
                }
                _ => break,
            };
            match self.cmd(Command::Consume { session, stream, n }) {
                Ok(rep) => fin |= rep.value == Value::Recv(RecvStatus::Finished),
                Err(_) => break,
            }
        }
        if !fin && let Ok(rep) = self.cmd(Command::Consume { session, stream, n: 0 }) {
            fin = rep.value == Value::Recv(RecvStatus::Finished);
        }
        if self.deliver() && (!buf.is_empty() || fin) {
            let local = self.now;
            layers.event(
                local,
                self,
                LayerEvent::StreamData {
                    session,
                    stream,
                    data: &buf,
                    fin,
                },
            );
        }
        self.scratch = buf;
    }

    /// Answer the key request of `session` with the node's software keys.
    fn answer_keys(&mut self, session: SessionId) {
        let prov = self.provider();
        let reg = self.shared.registry;
        let (Some(ep), Some(prekeys)) = (self.ep.as_ref(), self.prekeys.as_ref()) else {
            return;
        };
        let Answer::KeyRequest(req) = ep.query(Query::KeyRequest(session)) else {
            return;
        };
        if let KeyRequest::Sign { message, .. } = req {
            // Both ends sign and verify in the handshake, so a signature made is charged with one verified.
            reg.note_sign(self.idx, message.len());
            reg.note_verify(self.idx, message.len());
        }
        let soft = SoftKeys {
            signer: Some((KeyHandle(1), &self.kp)),
            prekeys: Some(prekeys),
        };
        let mut env = Env {
            provider: &prov,
            now: self.local,
            drbg: &mut self.drbg,
        };
        let mut sig = [0u8; MAX_SIGNATURE_LEN];
        let response = soft.answer(&mut env, &req, &mut sig);
        let _ = self.cmd(Command::KeyResponse { session, response });
    }

    /// The oracle revoked `peer`: end its sessions now and refuse it from here on.
    pub(super) fn revoke(&mut self, peer: usize) {
        self.revoked.insert(peer);
        let open: Vec<SessionId> = self
            .sessions
            .iter()
            .filter(|(_, s)| s.peer == peer && !s.hidden)
            .map(|(id, _)| *id)
            .collect();
        for session in open {
            let _ = self.cmd(Command::Close {
                session,
                error: CLOSE_DENIED,
            });
        }
        self.events.push_back(NodeEvent::Revoked { peer });
    }
}

fn first8(b: &[u8; 32]) -> [u8; 8] {
    let mut out = [0u8; 8];
    out.copy_from_slice(&b[..8]);
    out
}

impl Host for Core {
    fn idx(&self) -> usize {
        self.idx
    }

    fn registry(&self) -> &'static crate::suite::crypto::Registry {
        self.shared.registry
    }

    fn connect(&mut self, peer: usize, alpn: &'static [u8]) -> bool {
        let shared = Rc::clone(&self.shared);
        let addrs = shared.public_addrs(peer);
        let Some(node) = shared.node_id(peer) else { return false };
        if peer == self.idx || addrs.is_empty() || self.revoked.contains(&peer) {
            return false;
        }
        self.cmd(Command::Connect {
            node,
            alpn,
            addrs,
            role: Role::Other,
        })
        .is_ok()
    }

    fn open_stream(&mut self, session: SessionId) -> Option<vinc_transport::stream::StreamId> {
        match self.cmd(Command::OpenStream { session, bidi: true }).ok()?.value {
            Value::Stream(id) => Some(id),
            _ => None,
        }
    }

    fn write(&mut self, session: SessionId, stream: vinc_transport::stream::StreamId, data: &[u8]) -> usize {
        match self.cmd(Command::Write { session, stream, data }) {
            Ok(Reply {
                value: Value::Written(n),
                ..
            }) => n,
            _ => 0,
        }
    }

    fn finish(&mut self, session: SessionId, stream: vinc_transport::stream::StreamId) {
        let _ = self.cmd(Command::Finish { session, stream });
    }

    fn reset(&mut self, session: SessionId, stream: vinc_transport::stream::StreamId, code: u64) {
        let _ = self.cmd(Command::Reset {
            session,
            stream,
            error: code,
        });
    }

    fn close(&mut self, session: SessionId, code: u64) {
        let _ = self.cmd(Command::Close { session, error: code });
    }

    fn peer_of(&self, session: SessionId) -> Option<usize> {
        self.sessions.get(&session).filter(|s| !s.hidden).map(|s| s.peer)
    }
}
