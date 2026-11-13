//! The part of a suite node that owns the VINC node: its keys, sessions, interfaces and the host duties.
//!
//! [`Core`] is everything except the protocol layers, so a layer can be handed `&mut Core` as its
//! [`Host`](crate::suite::proto::host::Host) while the layers themselves stay a separate field of the node. The node
//! (`vinc_node::Node`: the endpoint, the connectivity client, membership and broadcast) is SANS-IO: the events of
//! every command and every poll end up in one queue that [`Core::service`] drains, answering key requests and access
//! checks itself and turning the rest into layer events. A hub also runs the relay for its members (`relay.rs`), and
//! every node serves the carrier streams of its relays (`carrier.rs`).
//!
//! Invariants: all node time is the node's local time (the simulator's clock for this node plus a fixed base so it is
//! never negative, and never going backward); no borrow of the recorder is held across a call into a layer; a session
//! the node closed on its own (a revoked or unknown peer) is hidden from the layers for its whole life.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::net::{IpAddr, SocketAddr};
use std::rc::Rc;

use vinc_connect::client::{Config as ConnCfg, RelayCfg};
use vinc_core::{
    Command, CommandError, EndpointConfig, IfaceEvent as EpIfaceEvent, IfaceId, SessionId, Value, relay_parts,
    state_len,
};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use vinc_node::{Config as NodeConfig, HUB_ALPN, Node};
use vinc_security::{Env, LocalIdentity, PrekeyPolicy, SoftPrekeys};

use super::apps::SuiteApps;
use super::carrier::Wire;
use super::mem::{CLIENT_TICKETS, Ep, Src, recycle, slots};
use super::relay::{HubSide, LOCAL_RELAY};
use super::shared::{Shared, derive, make_identity};
use super::{NodeEvent, SetupError};
use crate::suite::crypto::{DeviceCosts, Tracked};
use crate::{Clock, WALL_EPOCH};

/// The local time of a node at true time zero with a perfect clock: one hour, so a negative clock offset never
/// makes the endpoint's time negative.
pub const LOCAL_BASE: u64 = 3_600_000_000_000;
/// The most same-size datagrams the endpoint batches into one transmit.
pub const MAX_GSO: usize = 8;
const SECOND: u64 = 1_000_000_000;

/// The relays a node can be configured with.
pub(super) const NRL: usize = 4;
/// The peers the connectivity layer remembers.
const NPEERS: usize = 64;

/// The estimate of the memory one live session holds, in bytes: one pool chunk plus its tables. The endpoint keeps no
/// byte accounting of its own, so the state size the node reports is built from counts it does expose.
pub const SESSION_STATE_BYTES: u64 = 20_480;
/// The estimate of one amplification-ledger entry, in bytes.
pub const LEDGER_ENTRY_BYTES: u64 = 64;
/// The size of one remembered round trip in the exported state format, used as its memory estimate.
pub const PEER_ENTRY_BYTES: u64 = 41;

type NodeT = Node<Ep, Tracked, (), NRL, NPEERS, SuiteApps>;

/// One interface of the node as the endpoint sees it.
pub(super) struct IfEntry {
    ip: IpAddr,
    port: u16,
    up: bool,
    id: Option<IfaceId>,
    /// A UDP interface of the world; false for the stand-in of a node that has none (a browser).
    udp: bool,
}

/// Where an incarnation is in its life.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Phase {
    /// No node.
    Stopped,
    /// The node runs and the layers get events.
    Running,
    /// The node left on purpose: it still sends its closes, the layers are stopped.
    Left,
}

pub(super) struct Sess {
    pub(super) peer: usize,
    pub(super) hidden: bool,
}

/// How the node knows a session an event names.
pub(super) enum Known {
    Visible(usize),
    Hidden,
    Unknown,
}

/// An access check waiting for its answer time.
#[derive(Clone, Copy)]
pub(super) enum Check {
    /// A session's check, by the endpoint's id.
    Endpoint(u64),
    /// A broadcast origin's check, by the node's id.
    Broadcast(u32),
}

/// The CPU a node was charged, by part, for the run's statistics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct CpuParts {
    /// Nanoseconds of the instrumented crypto.
    pub crypto_ns: u64,
    /// Handler calls (datagrams, timeouts, commands, carrier events).
    pub calls: u64,
    /// Nanoseconds of transmit I/O.
    pub io_ns: u64,
    /// AEAD calls.
    pub aead: u64,
    /// Bytes sealed or opened.
    pub aead_bytes: u64,
    /// Bytes hashed.
    pub hash_bytes: u64,
}

#[allow(
    clippy::struct_excessive_bools,
    reason = "independent facts about the node, not a state"
)]
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
    pub(super) node: Option<Box<NodeT>>,
    pub(super) prekeys: Option<SoftPrekeys<Tracked>>,
    pub(super) prekey_info: Option<vinc_security::PrekeyInfo>,
    pub(super) drbg: Drbg,
    pub(super) hub_drbg: Drbg,
    pub(super) hub: Option<Box<HubSide>>,
    pub(super) wire: Wire,
    pub(super) sessions: BTreeMap<SessionId, Sess>,
    pub(super) acp: VecDeque<(u64, Check, bool)>,
    pub(super) clock: Clock,
    pub(super) now: u64,
    pub(super) local: u64,
    pub(super) revoked: BTreeSet<usize>,
    pub(super) ifaces: Vec<IfEntry>,
    /// The node can send UDP: a browser cannot.
    pub(super) udp: bool,
    /// The node is a browser: WebSocket carriers only.
    pub(super) browser: bool,
    pub(super) moved: bool,
    pub(super) scratch: Vec<u8>,
    pub(super) events: VecDeque<NodeEvent>,
    stash: Vec<u8>,
    stash_at: usize,
    stash_route: Option<(SocketAddr, SocketAddr, usize)>,
    pub(super) io_acc: f64,
    pub(super) calls: u64,
    pub(super) cpu_ns: u64,
    /// The CPU charged so far by part: crypto, handler calls and transmit I/O, in nanoseconds, and the bytes sealed or
    /// opened and hashed.
    pub(super) cpu_parts: CpuParts,
    pub(super) persisted: Vec<u8>,
    pub(super) max_export: usize,
    pub(super) next_sample: u64,
    pub(super) timer_violations: u64,
    /// The last call ran the node's timers: the endpoint's deadline is checked once the host has drained its output.
    pub(super) timer_check: bool,
    /// The address the request being answered came to: replies leave from it.
    pub(super) reply_from: Option<SocketAddr>,
    /// The last connectivity notices, for diagnosis.
    pub(super) notices: VecDeque<String>,
    /// The ids of the relays the node was started with, by slot: what a carrier notice's number names.
    pub(super) relay_ids: Vec<vinc_crypto::NodeId>,
    /// The 5 s slot of true time the last path snapshot of the decision trace was taken in.
    pub(super) snap_slot: u64,
    /// The due deadline the endpoint showed after the previous timer call, to tell a stuck timer from a due one.
    pub(super) stale_deadline: Option<u64>,
}

impl Core {
    pub(super) fn new(shared: Rc<Shared>, idx: usize) -> Result<Self, SetupError> {
        let spec = shared.world.nodes.get(idx).ok_or(SetupError::NoSuchNode(idx))?;
        let (kp, identity) = make_identity(shared.world.seed, idx)?;
        let mut ifaces: Vec<IfEntry> = spec
            .ifaces
            .iter()
            .filter(|f| f.kind.starts_with("udp"))
            .filter_map(|f| {
                Some(IfEntry {
                    ip: super::shared::iface_ip(&f.addr)?,
                    port: f.addr.port,
                    up: true,
                    id: None,
                    udp: true,
                })
            })
            .collect();
        let udp = !ifaces.is_empty();
        if !udp {
            // A node with no UDP interface (a browser) is still somewhere on the network: its carriers leave from
            // the address of its stream interface, which the endpoint also needs as the address relay paths arrive at.
            ifaces.extend(spec.ifaces.iter().filter_map(|f| {
                Some(IfEntry {
                    ip: super::shared::iface_ip(&f.addr)?,
                    port: 4433,
                    up: true,
                    id: None,
                    udp: false,
                })
            }));
            ifaces.truncate(1);
        }
        let costs = shared.costs(idx);
        let seed = super::shared::identity_seed(shared.world.seed, idx);
        let world_seed = shared.world.seed;
        Ok(Self {
            idx,
            costs,
            kp,
            identity,
            seed,
            incarnation: 0,
            last_start: 0,
            phase: Phase::Stopped,
            node: None,
            prekeys: None,
            prekey_info: None,
            drbg: Drbg::new(&derive(b"suite-keys", world_seed, idx as u64, 0)),
            hub_drbg: Drbg::new(&derive(b"suite-hub", world_seed, idx as u64, 0)),
            hub: None,
            wire: Wire::default(),
            sessions: BTreeMap::new(),
            acp: VecDeque::new(),
            clock: Clock::default(),
            now: 0,
            local: LOCAL_BASE,
            revoked: BTreeSet::new(),
            ifaces,
            udp,
            browser: spec.device == "browser",
            moved: false,
            scratch: Vec::new(),
            events: VecDeque::new(),
            stash: Vec::new(),
            stash_at: 0,
            stash_route: None,
            io_acc: 0.0,
            calls: 0,
            cpu_ns: 0,
            cpu_parts: CpuParts::default(),
            persisted: Vec::new(),
            max_export: 0,
            next_sample: 0,
            timer_violations: 0,
            timer_check: false,
            reply_from: None,
            notices: VecDeque::new(),
            relay_ids: Vec::new(),
            snap_slot: 0,
            stale_deadline: None,
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
        let (local, wall) = (self.local, self.wall_ms());
        if let Some(node) = self.node.as_mut() {
            node.set_wall_ms(local, wall);
        }
    }

    /// The wall clock in milliseconds, as the node's own clock reads it.
    pub(super) fn wall_ms(&self) -> u64 {
        let ns = i128::from(WALL_EPOCH) + i128::from(self.clock.local(self.now));
        u64::try_from(ns.max(0) / 1_000_000).unwrap_or(0)
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
        self.node.as_deref().map(Node::endpoint)
    }

    pub(super) fn violation(&self, gate: &str, msg: &str) {
        self.shared.rec.borrow_mut().violation(self.now, gate, self.idx, msg);
    }

    pub(super) fn provider(&self) -> Tracked {
        Tracked::new(self.shared.registry, self.idx, Software)
    }

    /// The UDP address of the node: its first interface that is up.
    pub(super) fn udp_addr(&self) -> Option<SocketAddr> {
        self.ifaces
            .iter()
            .find(|e| e.up && e.udp)
            .map(|e| SocketAddr::new(e.ip, e.port))
    }

    /// The UDP address a datagram to `to` leaves from: the first interface that is up in the family of `to` (a datagram
    /// from the other family does not arrive), else the first interface that is up.
    pub(super) fn udp_addr_for(&self, to: &SocketAddr) -> Option<SocketAddr> {
        let up = || self.ifaces.iter().filter(|e| e.up && e.udp);
        up().find(|e| e.ip.is_ipv4() == to.is_ipv4())
            .or_else(|| up().next())
            .map(|e| SocketAddr::new(e.ip, e.port))
    }

    /// The address carrier streams leave from: the first IPv4 interface that is up, else any.
    pub(super) fn stream_local(&self) -> Option<SocketAddr> {
        let up = || self.ifaces.iter().filter(|e| e.up);
        up().find(|e| e.ip.is_ipv4())
            .or_else(|| up().next())
            .map(|e| SocketAddr::new(e.ip, e.port))
    }

    // ---- life ----

    /// Build a fresh node, restore `persisted` into its endpoint unless this restart keeps no state, and register
    /// `alpns`. Returns whether state was restored; `None` if the node could not be built.
    pub(super) fn begin(&mut self, now: u64, persisted: &[u8], alpns: &[&'static [u8]]) -> Option<bool> {
        self.tick(now);
        self.incarnation += 1;
        let stateless = self.shared.restarts_stateless(self.idx, self.last_start, now);
        self.last_start = now;
        if stateless && let Some(values) = self.shared.values_of(self.idx) {
            values.forget();
        }
        self.clear_volatile();
        let Some(table) = slots(self.idx) else {
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
        // The reset key comes from the node's identity, not its incarnation: it survives a restart, as a host's does.
        cfg.reset_key = Some(derive(b"suite-reset", world_seed, self.idx as u64, 0));
        // A hub runs the relay of its members, and a node that serves a relay sends no tail repair on its sessions.
        cfg.conn.tail_repair = !self.shared.is_hub(self.idx);
        let ep_drbg = Drbg::new(&derive(b"suite-endpoint", world_seed, self.idx as u64, inc));
        let mut ep = Box::new(Ep::new(self.local, prov, ep_drbg, self.identity, cfg, table));
        self.drbg = Drbg::new(&derive(b"suite-keys", world_seed, self.idx as u64, inc));
        self.hub_drbg = Drbg::new(&derive(b"suite-hub", world_seed, self.idx as u64, inc));
        let mut env = Env {
            provider: &prov,
            now: self.local,
            drbg: &mut self.drbg,
        };
        let mut prekey = None;
        match SoftPrekeys::new(&mut env, PrekeyPolicy::default()) {
            Ok(mut keys) => {
                // vertexia: one prekey per incarnation, never rotated; ceiling is an incarnation longer than the
                // policy lifetime (10 minutes) still using it, upgrade path is a rotation timer calling `acquire`.
                match keys.acquire(&mut env) {
                    Ok(info) => {
                        ep.set_prekey(info.clone());
                        self.prekey_info = Some(info.clone());
                        prekey = Some(info);
                    }
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
        let Some(prekey) = prekey else {
            recycle(self.idx, *ep);
            return None;
        };
        let node = match self.build_node(*ep, prekey, now) {
            Ok(n) => n,
            Err(msg) => {
                self.violation("G-SPEC", &msg);
                return None;
            }
        };
        self.node = Some(node);
        if self.shared.is_hub(self.idx) {
            let me = self.identity.node_id();
            self.hub = Some(Box::new(HubSide::new(me, derive_seed(world_seed, self.idx, inc))));
            self.hub_peers_init();
            self.hub_dial_peers();
        }
        self.refresh_local(false);
        self.phase = Phase::Running;
        self.next_sample = 0;
        Some(restored)
    }

    #[allow(clippy::default_trait_access, reason = "the default limits of the node's broadcast")]
    fn build_node(&mut self, ep: Ep, prekey: vinc_security::PrekeyInfo, now: u64) -> Result<Box<NodeT>, String> {
        let mut relays: [Option<RelayCfg>; NRL] = [None; NRL];
        // A node is never its own relay: a hub lists the other hubs only.
        let me = self.identity.node_id();
        for (d, r) in relays
            .iter_mut()
            .zip(self.shared.relays().iter().filter(|r| r.id != me))
        {
            *d = Some(RelayCfg {
                udp: r.udp.filter(|_| self.udp),
                tcp: r.tcp.filter(|_| !self.browser),
                ..*r
            });
        }
        self.relay_ids = relays.iter().flatten().map(|r| r.id).collect();
        let spec = self
            .shared
            .world
            .nodes
            .get(self.idx)
            .ok_or("the node is not in the world".to_owned())?;
        let local = self
            .udp_addr()
            .or_else(|| self.stream_local())
            .ok_or("the node has no interface".to_owned())?;
        let cfg = NodeConfig {
            connect: ConnCfg {
                me: self.identity.node_id(),
                identity: self.identity,
                relays,
                phone: spec.device == "phone",
                restarted: self.incarnation > 1,
                start: self.local,
                v6: false,
                keep_learn: false,
            },
            is_hub: self.shared.is_hub(self.idx),
            version: self.shared.version_at(self.idx, now),
            alpn: HUB_ALPN,
            limits: Default::default(),
            wall_ms: self.wall_ms(),
            local,
            trace: self.shared.is_watched(self.idx),
        };
        let key = Keypair::from_seed(IdentityAlg::Ed25519, &self.seed)
            .map(Box::new)
            .map_err(|_| "the node key could not be made".to_owned())?;
        let drbg = Drbg::new(&derive(
            b"suite-node",
            self.shared.world.seed,
            self.idx as u64,
            self.incarnation,
        ));
        let seed = u64::from_be_bytes(first8(&derive(
            b"suite-conn",
            self.shared.world.seed,
            self.idx as u64,
            self.incarnation,
        )));
        let prov = self.provider();
        let (Some(values), Some(sets)) = (self.shared.values_of(self.idx), self.shared.sets_of(self.idx)) else {
            return Err("the node has no stores".to_owned());
        };
        let apps = SuiteApps::new(values.clone(), sets.clone());
        let mut node = Node::with_apps(&cfg, ep, prekey, prov, drbg, key, (), seed, apps)
            .map_err(|e| format!("the node could not start: {e}"))?;
        // The node answers a value only if the host registered its root.
        for root in values.served_roots() {
            node.values_provide(&root);
        }
        Ok(Box::new(node))
    }

    fn clear_volatile(&mut self) {
        if let Some(node) = self.node.take() {
            recycle(self.idx, node.into_endpoint());
        }
        self.prekeys = None;
        self.hub = None;
        self.wire = Wire::default();
        self.sessions.clear();
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
    // ---- commands to the node ----

    pub(super) fn cmd(&mut self, c: Command<'_, Src>) -> Result<Value, CommandError> {
        let local = self.local;
        self.node.as_mut().ok_or(CommandError::NoSession)?.command(local, c)
    }

    pub(super) fn handle_datagram(&mut self, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        if self.hub.is_some() {
            self.hub_datagram(local, remote, data);
        } else if let Some(node) = self.node.as_mut() {
            node.handle_datagram(self.local, local, remote, data);
        }
    }

    /// Run the timers that are due and answer the access checks whose answer time has come. Returns whether the
    /// node's own timer was due.
    pub(super) fn run_timers(&mut self) -> bool {
        while self.acp.front().is_some_and(|&(due, ..)| due <= self.now) {
            let Some((_, check, allow)) = self.acp.pop_front() else {
                break;
            };
            let local = self.local;
            match check {
                // An answer for a check the endpoint dropped meanwhile is refused; there is nothing to repair.
                Check::Endpoint(check) => {
                    let _ = self.cmd(Command::AcpAnswer { check, allow });
                }
                Check::Broadcast(id) => {
                    if let Some(node) = self.node.as_mut() {
                        node.broadcast_acp_answer(local, id, allow);
                    }
                }
            }
        }
        self.hub_timeout();
        let local = self.local;
        let Some(node) = self.node.as_mut() else { return false };
        let due = node.poll_timeout().is_some_and(|d| d <= local);
        if due {
            node.handle_timeout(local);
        }
        self.timer_check = due;
        due
    }

    /// The next true time the node, the relay or an access answer wants a call.
    pub(super) fn next_deadline(&self) -> Option<u64> {
        let node = self.node.as_ref().and_then(|n| n.poll_timeout());
        let relay = self.hub.as_ref().and_then(|h| h.next_deadline());
        let acp = self.acp.front().map(|&(due, ..)| due);
        node.into_iter().chain(relay).map(|d| self.to_true(d)).chain(acp).min()
    }

    /// Next datagram: a queued one of the relay or the connectivity layer, the rest of a batch, or a fresh batch from
    /// the endpoint (one transmit call recorded). The datagram is written to `buf`; returns `(local, remote, len)`.
    pub(super) fn next_datagram(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, SocketAddr, usize)> {
        if let Some((local, remote, data)) = self.wire.datagrams.pop_front() {
            buf.get_mut(..data.len())?.copy_from_slice(&data);
            return Some((local, remote, data.len()));
        }
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
        loop {
            let local = self.local;
            let tx = self.node.as_mut()?.poll_transmit(local, buf)?;
            let seg = tx.segment_size.max(1);
            if let Some((relay, slot)) = relay_parts(&tx.remote)
                && relay == LOCAL_RELAY
            {
                let data = buf.get(..tx.len).unwrap_or_default().to_vec();
                for chunk in data.chunks(seg) {
                    self.hub_send_local(slot, chunk);
                }
                continue;
            }
            if !self.udp {
                // A browser has no datagram socket: whatever the endpoint tried to send directly is lost.
                continue;
            }
            let segs = tx.len.div_ceil(seg);
            self.shared.rec.borrow_mut().transmit_call(self.idx, self.now);
            self.io_acc += self.costs.io_call + self.costs.io_seg * segs as f64;
            let first = tx.len.min(seg);
            if tx.len > first {
                self.stash.clear();
                self.stash.extend_from_slice(buf.get(first..tx.len)?);
                self.stash_at = 0;
                self.stash_route = Some((tx.local, tx.remote, seg));
            }
            return Some((tx.local, tx.remote, first));
        }
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
        let Some(ep) = self.endpoint() else { return Vec::new() };
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
        let Some(ep) = self.endpoint() else { return 0 };
        let st = ep.node_stats();
        st.sessions as u64 * SESSION_STATE_BYTES
            + st.ledger as u64 * LEDGER_ENTRY_BYTES
            + ep.rtt().peers().count() as u64 * PEER_ENTRY_BYTES
    }

    /// The membership view as `(epoch, members)` with members resolved to world indices.
    pub(super) fn view(&self) -> Option<(u64, Vec<usize>)> {
        let m = self.node.as_ref()?.membership();
        let members = m
            .members()
            .filter_map(|(id, _)| self.shared.index_of_bytes(id))
            .collect();
        Some((m.view_epoch(), members))
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

    /// Tell the node the addresses it has now, and that they changed when `changed` says so.
    fn refresh_local(&mut self, changed: bool) {
        let addrs: Vec<SocketAddr> = self
            .ifaces
            .iter()
            .filter(|e| e.up && e.udp)
            .map(|e| SocketAddr::new(e.ip, e.port))
            .collect();
        let local = self.local;
        if let Some(node) = self.node.as_mut() {
            node.set_local(&addrs);
            if changed {
                node.address_changed(local);
            }
        }
    }

    fn iface_event_to_node(&mut self, id: IfaceId, ev: EpIfaceEvent) {
        let local = self.local;
        if let Some(node) = self.node.as_mut() {
            node.iface_event(local, id, ev);
        }
    }

    fn add_iface_to_node(&mut self, addr: SocketAddr) -> Option<IfaceId> {
        self.node.as_mut().and_then(|n| n.add_iface(addr))
    }

    pub(super) fn iface_up(&mut self, ip: IpAddr) {
        if let Some(i) = self.ifaces.iter().position(|e| e.ip == ip) {
            self.ifaces[i].up = true;
            let (port, id) = (self.ifaces[i].port, self.ifaces[i].id);
            let id = id.or_else(|| self.add_iface_to_node(SocketAddr::new(ip, port)));
            self.ifaces[i].id = id;
            if let Some(id) = id {
                self.iface_event_to_node(id, EpIfaceEvent::Up);
            }
            self.refresh_local(true);
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
        if let Some(i) = self.ifaces.iter().position(|e| e.ip.is_ipv4() == v4 && !e.up) {
            self.ifaces[i].ip = ip;
            self.ifaces[i].up = true;
            let (port, id) = (self.ifaces[i].port, self.ifaces[i].id);
            match id {
                Some(id) => {
                    self.iface_event_to_node(id, EpIfaceEvent::AddrChange(SocketAddr::new(ip, port)));
                    self.iface_event_to_node(id, EpIfaceEvent::Up);
                }
                None => self.ifaces[i].id = self.add_iface_to_node(SocketAddr::new(ip, port)),
            }
        } else {
            let id = self.add_iface_to_node(SocketAddr::new(ip, port));
            self.ifaces.push(IfEntry {
                ip,
                port,
                up: true,
                id,
                udp: self.udp,
            });
        }
        self.refresh_local(true);
    }

    pub(super) fn iface_down(&mut self, ip: IpAddr) {
        if let Some(i) = self.ifaces.iter().position(|e| e.ip == ip) {
            self.ifaces[i].up = false;
            if let Some(id) = self.ifaces[i].id {
                self.iface_event_to_node(id, EpIfaceEvent::Down);
            }
            self.refresh_local(false);
        }
    }

    pub(super) fn iface_changed(&mut self, old: IpAddr, new: IpAddr) {
        if let Some(i) = self.ifaces.iter().position(|e| e.ip == old) {
            self.ifaces[i].ip = new;
            if let Some(id) = self.ifaces[i].id {
                let port = self.ifaces[i].port;
                self.iface_event_to_node(id, EpIfaceEvent::AddrChange(SocketAddr::new(new, port)));
            }
            self.refresh_local(true);
        }
    }
}

fn first8(b: &[u8; 32]) -> [u8; 8] {
    let mut out = [0u8; 8];
    out.copy_from_slice(&b[..8]);
    out
}

/// The seed of a hub's relay tables: one per node and incarnation.
fn derive_seed(world_seed: u64, idx: usize, inc: u64) -> u64 {
    u64::from_be_bytes(first8(&derive(b"suite-relay", world_seed, idx as u64, inc)))
}
