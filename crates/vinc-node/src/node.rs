//! The node: the endpoint, the connectivity client, membership and broadcast as one SANS-IO state machine.
//!
//! The surface mirrors the endpoint's: datagrams, time and commands go in; datagrams, the next deadline and
//! [`NodeEvent`]s come out. Streams and datagrams of the application pass through to the endpoint untouched; the
//! hub stream, the membership frames and the broadcast frames never reach the application as bytes.
//!
//! The host drives it as it drives the endpoint:
//!
//! ```text
//! handle_datagram(now, local, remote, buf)      command(now, cmd) -> Value      dial(now, node, alpn, role, hints)
//! poll_transmit(now, out) -> Option<Transmit>   poll_event() -> Option<NodeEvent>
//! poll_timeout() -> Option<u64>                 handle_timeout(now)
//! ```
//!
//! plus the connectivity client's own streams and key answers (`poll_io`, `stream_data`, `poll_stream`, `poll_udp`,
//! `key_request`, `sign_request` and their responses), which a host serves exactly as for the client alone.
//! After any input call `poll_transmit` until it returns `None`; there are no hidden wakeups.
//!
//! Invariants: every table is bounded; the same inputs in the same order give the same outputs; no input panics.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::vec::Vec;
use core::cell::Cell;
use core::net::{IpAddr, Ipv4Addr, SocketAddr};

use vinc_broadcast::{Config as BcConfig, ReachStats, Refused, StartError as BcStartError, Topics};
use vinc_connect::client::Connectivity;
use vinc_connect::record::MAX_ADDRS;
use vinc_connect::ticket::Ticket;
use vinc_core::{Command, CommandError, Role, SessionId, Transmit, Value, is_relay_addr};
use vinc_crypto::{Drbg, IdentityAlg, Keypair, Provider};
use vinc_membership::session::Carrier;
use vinc_membership::{Config as MemConfig, Membership, NodeId, StartError as MemStartError, TableFull};
use vinc_security::{Env, PrekeyInfo};

use crate::apps::{Apps, DtnApp, NoApps, ServeSource};
use crate::config::{Config, Nanos, Store};
use crate::dtn::Dtn;
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::hosts::{Bc, MemHost};
use crate::io::Io;
use crate::layer::Layer;
use crate::reconcile::Reconciler;
use crate::trace::{Body, NodeTrace, TraceItem, tag};
use crate::values::Values;

/// Why a node could not start.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StartError {
    /// The endpoint's protocol registry is full, or the protocol id is empty or too long.
    Alpn,
    /// The protocol id of the hub stream is the protocol id of a layer: the node could not tell their sessions apart.
    AlpnOfLayer(Layer),
    /// Membership could not start: too many hubs, or the incarnation could not be issued.
    Membership(MemStartError),
    /// Broadcast could not start: the limits are unusable, or the key is not the node's.
    Broadcast(BcStartError),
}

impl core::fmt::Display for StartError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Alpn => f.write_str("the hub protocol id could not be registered with the endpoint"),
            Self::AlpnOfLayer(l) => write!(
                f,
                "the hub protocol id {} is also the protocol id of a layer, so each needs an id of its own",
                core::str::from_utf8(l.alpn()).unwrap_or_default()
            ),
            Self::Membership(e) => e.fmt(f),
            Self::Broadcast(e) => e.fmt(f),
        }
    }
}

impl core::error::Error for StartError {}

/// What [`Node::poll_timeout`] last answered, while no call could have moved it, and what the layers above the
/// endpoint contributed to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Due {
    /// A call since the last answer could have moved any deadline.
    Stale,
    /// A call since the last answer could have moved the endpoint's deadline and no layer's: the layers' stands.
    Endpoint(Layers),
    /// The deadline, or none, and the layers' part of it.
    Known(Option<Nanos>, Layers),
}

/// The earliest deadline of the layers above the endpoint, and the node's clock when it was worked out. A layer's
/// deadline is good from one of its inputs to the next, as the node's is for its host; a call that only moves the
/// endpoint is no input of theirs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Layers {
    at: Nanos,
    due: Option<Nanos>,
}

/// The node. See the module docs for the driving contract.
pub struct Node<E: Ep, P: Provider + Clone, St: Store, const R: usize, const PEERS: usize, A: Apps<P> = NoApps> {
    pub(crate) io: Io<E, St>,
    pub(crate) apps: A,
    pub(crate) vals: Option<Box<Values<A::Values>>>,
    pub(crate) recs: Option<Box<Reconciler>>,
    pub(crate) dtn: Option<Box<Dtn>>,
    pub(crate) conn: Box<Connectivity<P, R, PEERS>>,
    pub(crate) mem: Membership,
    pub(crate) topics: Topics,
    pub(crate) prov: P,
    pub(crate) drbg: Drbg,
    pub(crate) ident: vinc_crypto::NodeId,
    pub(crate) local: SocketAddr,
    pub(crate) local_addrs: [Option<SocketAddr>; MAX_ADDRS],
    pub(crate) next_duty: Nanos,
    /// What [`Node::poll_timeout`] answers, until a call that could move it: every such call clears this.
    pub(crate) deadline: Cell<Due>,
    pub(crate) leaving: bool,
    /// The port-mapping client, once the host turned it on.
    pub(crate) pm: Option<Box<crate::portmap::Pm>>,
}

impl<E: Ep, P: Provider + Clone, St: Store, const R: usize, const PEERS: usize, A: Apps<P>> core::fmt::Debug
    for Node<E, P, St, R, PEERS, A>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Node")
            .field("hub", &self.io.is_hub)
            .field("members", &self.mem.member_count())
            .finish_non_exhaustive()
    }
}

/// The settle loop runs at most this many rounds per call.
const SETTLE_ROUNDS: usize = 64;

impl<E: Ep, P: Provider + Clone, St: Store, const R: usize, const PEERS: usize> Node<E, P, St, R, PEERS, NoApps>
where
    E::Src: ServeSource<crate::apps::NoValues>,
{
    /// Start a node that runs membership and broadcast only.
    ///
    /// # Errors
    /// [`StartError`] if the protocol id cannot be registered, or a layer refuses to start.
    #[allow(
        clippy::too_many_arguments,
        reason = "a node is built once from the pieces the host owns"
    )]
    pub fn new(
        cfg: &Config<R>,
        ep: E,
        prekey: PrekeyInfo,
        prov: P,
        drbg: Drbg,
        key: Box<Keypair>,
        store: St,
        seed: u64,
    ) -> Result<Self, StartError> {
        Self::with_apps(cfg, ep, prekey, prov, drbg, key, store, seed, NoApps::default())
    }
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// Start a node. `ep` is an endpoint with its interfaces and prekey set; `key` signs broadcast messages and must `ep` is an endpoint with its interfaces and prekey set; `key` signs broadcast messages and must
    /// be the key of the configured identity; `seed` keys the connectivity layer's tables. `apps` says which layers
    /// above broadcast run and gives them their stores.
    ///
    /// # Errors
    /// [`StartError`] if a protocol id cannot be registered or is claimed by two owners (the hub stream and a layer),
    /// or a layer refuses to start.
    #[allow(
        clippy::too_many_arguments,
        reason = "a node is built once from the pieces the host owns"
    )]
    pub fn with_apps(
        cfg: &Config<R>,
        mut ep: E,
        prekey: PrekeyInfo,
        prov: P,
        drbg: Drbg,
        key: Box<Keypair>,
        store: St,
        seed: u64,
        mut apps: A,
    ) -> Result<Self, StartError> {
        let now = cfg.connect.start;
        if let Some(layer) = Layer::of_alpn(cfg.alpn) {
            return Err(StartError::AlpnOfLayer(layer));
        }
        if !ep.register_alpn(cfg.alpn) {
            return Err(StartError::Alpn);
        }
        let on = apps.enabled();
        for (enabled, layer) in [(on.values, Layer::Values), (on.sets, Layer::Sets), (on.dtn, Layer::Dtn)] {
            if enabled && !ep.register_alpn(layer.alpn()) {
                return Err(StartError::Alpn);
            }
        }
        let ident = cfg.connect.identity.node_id();
        let me = ident.bytes;
        let mut hubs: Vec<NodeId> = Vec::with_capacity(R);
        let mut algs = BTreeMap::new();
        for r in cfg.connect.relays.iter().flatten() {
            if r.id.bytes != me && !hubs.contains(&r.id.bytes) {
                hubs.push(r.id.bytes);
                if r.id.alg != ident.alg {
                    algs.insert(r.id.bytes, r.id.alg);
                }
            }
        }
        let max_frame = 2 + vinc_broadcast::consts::MAX_TOPIC + vinc_broadcast::wire::MAX_HEAD + cfg.limits.max_body;
        let mut conn = Box::new(Connectivity::new(cfg.connect, prekey, prov.clone(), seed));
        conn.set_gossip_alpn(cfg.alpn);
        let mut io = Io::new(
            ep,
            store,
            me,
            ident.alg,
            cfg.is_hub,
            cfg.alpn,
            cfg.version,
            now,
            cfg.wall_ms,
            hubs.clone(),
            algs,
            max_frame,
            cfg.trace,
        );
        let mut node_hubs = hubs;
        if cfg.is_hub {
            node_hubs.retain(|h| *h != me);
        }
        let mut local_addrs = [None; MAX_ADDRS];
        if let Some(s) = local_addrs.first_mut() {
            *s = Some(cfg.local);
        }
        let mut conn = conn;
        conn.set_local(&[cfg.local]);
        refresh_ticket(&mut io, &conn, &ident, &local_addrs);
        let mem_cfg = MemConfig {
            me,
            is_hub: cfg.is_hub,
            hubs: &node_hubs,
            trace: cfg.trace,
        };
        let mut mem = {
            let mut host = MemHost {
                io: &mut io,
                topics: None,
            };
            Membership::start(&mem_cfg, &mut host, now, cfg.wall_ms, 0).map_err(StartError::Membership)?
        };
        mem.set_max_frame(max_frame);
        let bc_cfg = BcConfig {
            me,
            is_hub: cfg.is_hub,
            hubs: &node_hubs,
            incarnation: mem.incarnation(),
            trace: cfg.trace,
            limits: cfg.limits,
        };
        let topics = Topics::start(&bc_cfg, key, now, cfg.wall_ms).map_err(StartError::Broadcast)?;
        io.trace(NodeTrace::Started {
            hub: u64::from(cfg.is_hub),
        });
        let vals = on
            .values
            .then(|| Box::new(Values::new(apps.values().clone(), cfg.trace)));
        let recs = on.sets.then(|| Box::new(Reconciler::new()));
        let dtn = on.dtn.then(|| {
            let policy = apps.dtn().policy();
            let budget = apps.dtn().budget();
            Box::new(Dtn::new(policy, budget, cfg.wall_ms))
        });
        let mut node = Self {
            io,
            apps,
            vals,
            recs,
            dtn,
            conn,
            mem,
            topics,
            prov,
            drbg,
            ident,
            local: cfg.local,
            local_addrs,
            next_duty: now,
            deadline: Cell::new(Due::Stale),
            leaving: false,
            pm: None,
        };
        node.refresh_alive(now);
        Ok(node)
    }

    // ---------------------------------------------------------------- the loop

    /// Whether the node is in a group: it is a hub, or it names a hub to attach to. A member with no hub is alone, and
    /// membership has nothing to do for it.
    pub(crate) fn in_group(&self) -> bool {
        self.io.is_hub || !self.io.hubs.is_empty()
    }

    /// Whether membership keeps a timer: the node is in a group and has not left it. Once it leaves,
    /// [`Membership::on_timeout`] does nothing, so a deadline asked of it would stay due and the host would call again
    /// at once, forever (vinc#551).
    fn mem_timed(&self) -> bool {
        self.in_group() && !self.leaving
    }

    /// Whether the periodic duties have anything to keep: a group to attach to, a layer above broadcast, or tables
    /// of sessions and backoffs. An idle node arms no timer of its own.
    pub(crate) fn duty_needed(&self) -> bool {
        self.in_group()
            || self.vals.is_some()
            || self.recs.is_some()
            || self.dtn.is_some()
            || !self.io.sess.is_empty()
            || !self.io.failed.is_empty()
            || !self.io.carriers.is_empty()
    }

    /// Take the time of a call.
    pub(crate) fn begin(&mut self, now: Nanos) {
        self.io.now = self.io.now.max(now);
        self.deadline.set(Due::Stale);
    }

    /// Take the time of a call that can move the endpoint's deadline and no layer's (it moves the application's data
    /// or asks for a datagram): the layers' deadline stands until one of them runs, which [`Self::settle_with`] and
    /// every other call say. The DTN layer's deadline follows the wall clock, so with it every call counts for the
    /// layers too.
    fn begin_endpoint(&mut self, now: Nanos) {
        self.io.now = self.io.now.max(now);
        let kept = match self.deadline.get() {
            Due::Known(_, l) | Due::Endpoint(l) if self.dtn.is_none() => Due::Endpoint(l),
            _ => Due::Stale,
        };
        self.deadline.set(kept);
    }

    /// Refresh what the layers read of the node: which hubs are alive, the ticket the address hash covers.
    pub(crate) fn refresh_alive(&mut self, now: Nanos) {
        self.io.hub_alive.clear();
        for h in &self.io.hubs {
            if self.mem.hub_is_up(now, h) {
                self.io.hub_alive.push(*h);
            }
        }
    }

    pub(crate) fn mem_host(&mut self) -> (&mut Membership, MemHost<'_, E, St>) {
        (
            &mut self.mem,
            MemHost {
                io: &mut self.io,
                topics: Some(&mut self.topics),
            },
        )
    }

    pub(crate) fn bc_host(&mut self) -> (&mut Topics, Bc<'_, E, St>) {
        (
            &mut self.topics,
            Bc {
                io: &mut self.io,
                mem: Some(&self.mem),
            },
        )
    }

    /// Run whatever is pending: endpoint events, the connectivity layer's timers, packets the relays carried, the
    /// dials the layers asked for. Every input call ends with it; a host calls it after serving key answers and
    /// stream operations, which it does outside the node.
    pub fn poll(&mut self, now: Nanos) {
        self.begin(now);
        self.settle(now);
    }

    pub(crate) fn settle(&mut self, now: Nanos) {
        self.settle_with(now, true);
    }

    /// Settle, with or without the connectivity layer's own step (`connect`).
    fn settle_with(&mut self, now: Nanos, connect: bool) {
        // The layers run: their deadlines may move.
        self.deadline.set(Due::Stale);
        for _ in 0..SETTLE_ROUNDS {
            self.refresh_alive(now);
            let mut busy = self.service(now);
            busy |= self.events_step(now);
            busy |= self.values_step(now);
            if connect {
                self.drive(now);
            }
            busy |= self.inbound_step(now);
            busy |= self.notices_step();
            busy |= self.dtn_step(now);
            if !busy {
                break;
            }
        }
    }

    fn drive(&mut self, now: Nanos) {
        let wall = self.io.wall_ms();
        let mut env = Env {
            provider: &self.prov,
            now,
            drbg: &mut self.drbg,
        };
        self.conn.drive(now, &mut self.io.ep, &mut env, Some(wall));
    }

    fn inbound_step(&mut self, now: Nanos) -> bool {
        let (addrs, fallback) = (&self.local_addrs, self.local);
        let ep = &mut self.io.ep;
        let mut did = false;
        self.conn.deliver_inbound(|from, data| {
            did = true;
            ep.handle_datagram(now, inbound_local(addrs, &from, fallback), from, data);
        });
        did
    }

    fn notices_step(&mut self) -> bool {
        let mut did = false;
        while let Some(n) = self.conn.poll_notice() {
            did = true;
            self.io.emit(NodeEvent::Connect(n));
        }
        did
    }

    /// The work the layers queued: dials and path probes the layers asked for, their events and their traces.
    fn service(&mut self, now: Nanos) -> bool {
        let mut did = false;
        while let Some(peer) = self.io.dials.pop() {
            did = true;
            self.dial_peer(now, &peer);
        }
        while let Some((hub, member)) = self.io.probes.pop() {
            did = true;
            self.probe_via(&hub, &member);
        }
        while let Some((layer, peer)) = self.io.ldials.pop() {
            did = true;
            self.dial_layer(now, layer, &peer);
        }
        while let Some(e) = self.mem.poll_event() {
            did = true;
            self.dtn_contacts_changed();
            self.io.emit(NodeEvent::Member(e));
        }
        if self.io.tq.on() {
            while let Some(t) = self.mem.poll_trace() {
                self.io.tq.push(now, Body::Membership(t));
            }
            while let Some(t) = self.topics.poll_trace() {
                self.io.tq.push(now, Body::Broadcast(t));
            }
            while let Some(t) = self.io.ep.poll_trace() {
                self.io.tq.push(t.t, Body::Core(t));
            }
        }
        did
    }

    /// Refresh the ticket the address hash covers, and whether the reflexive address is known.
    pub(crate) fn refresh_ticket(&mut self) {
        refresh_ticket(&mut self.io, &self.conn, &self.ident, &self.local_addrs);
    }

    // ---------------------------------------------------------------- inputs

    /// A datagram arrived at `local` from `remote`. The node may use `buf` as scratch.
    pub fn handle_datagram(&mut self, now: Nanos, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        self.handle_batch(now, local, remote, buf, usize::MAX);
    }

    /// Datagrams the host received from `remote` in one read, each `segment` bytes long but the last (which may be
    /// shorter): as [`handle_datagram`](Self::handle_datagram) for each in turn, except that the connectivity layer's
    /// own step runs once, after the last. Every event of every datagram is handled as it comes; what that step
    /// decides depends on the time, which is the same for all of them, and on the state they leave.
    pub fn handle_batch(&mut self, now: Nanos, local: SocketAddr, remote: SocketAddr, buf: &mut [u8], segment: usize) {
        self.begin(now);
        let mut rest = buf;
        loop {
            // An empty buffer is one empty datagram, as the host read it.
            let n = segment.max(1).min(rest.len());
            let (d, tail) = core::mem::take(&mut rest).split_at_mut(n);
            if !self.pm_datagram(now, remote, d) && !self.conn.handle_udp(now, remote, d) {
                self.io.ep.handle_datagram(now, local, remote, d);
            }
            self.settle_with(now, tail.is_empty());
            if tail.is_empty() {
                return;
            }
            rest = tail;
        }
    }

    /// Time passed. Safe to call at any time.
    pub fn handle_timeout(&mut self, now: Nanos) {
        self.begin(now);
        self.io.ep.handle_timeout(now);
        self.refresh_alive(now);
        if self.mem_timed() && now >= self.mem.poll_timeout() {
            self.refresh_ticket();
            let (m, mut h) = self.mem_host();
            m.on_timeout(&mut h, now);
        }
        if self.topics.poll_timeout().is_some_and(|t| now >= t) {
            let (t, mut h) = self.bc_host();
            t.on_timer(&mut h, now);
        }
        self.values_timeout(now);
        self.sets_timeout(now);
        self.dtn_timeout(now);
        if self.duty_needed() && now >= self.next_duty {
            self.duties(now);
        }
        self.pm_timeout(now);
        self.settle(now);
    }

    /// When the host should next call [`Node::handle_timeout`].
    pub fn poll_timeout(&self) -> Option<Nanos> {
        // A host asks many times between two calls that could move the answer: it is worked out once for them all,
        // and the layers' part once for all the calls that move only the endpoint.
        let layers = match self.deadline.get() {
            Due::Known(d, l) => {
                debug_assert_eq!(
                    d,
                    self.with_endpoint(self.layers_deadline(l.at)),
                    "a call moved the node's deadline and did not say so"
                );
                return d;
            }
            Due::Endpoint(l) => {
                debug_assert_eq!(
                    l.due,
                    self.layers_deadline(l.at),
                    "a call moved a layer's deadline and did not say so"
                );
                l
            }
            Due::Stale => Layers {
                at: self.io.now,
                due: self.layers_deadline(self.io.now),
            },
        };
        let d = self.with_endpoint(layers.due);
        self.deadline.set(Due::Known(d, layers));
        d
    }

    /// The node's deadline: the endpoint's or the layers', whichever is earlier.
    fn with_endpoint(&self, layers: Option<Nanos>) -> Option<Nanos> {
        [self.io.ep.poll_timeout(), layers].into_iter().flatten().min()
    }

    /// The earliest deadline of every layer above the endpoint, worked out for the clock `now`.
    fn layers_deadline(&self, now: Nanos) -> Option<Nanos> {
        [
            self.conn.next_deadline(now),
            self.mem_timed().then(|| self.mem.poll_timeout()),
            self.topics.poll_timeout(),
            self.values_deadline(),
            self.sets_deadline(),
            self.dtn_deadline(),
            self.duty_needed().then_some(self.next_duty),
            self.pm_deadline(),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    /// The next datagram to send. Packets that ride a relay carrier are handed to the connectivity layer and not
    /// returned. A hub returns the packets for the members of its own relay, whose synthetic addresses its client does
    /// not know, for the host that runs the relay.
    pub fn poll_transmit(&mut self, now: Nanos, out: &mut [u8]) -> Option<Transmit> {
        // Nothing waits to leave: the call would change nothing, so it is not an input, and the deadline worked out
        // for the last one stands. A host asks after every operation; most of the time there is nothing.
        if !self.io.ep.transmit_waiting() {
            return None;
        }
        self.begin_endpoint(now);
        loop {
            let t = self.io.ep.poll_transmit(now, out)?;
            // A hub hands the host the packets for its own relay's members; the paths of its client are routed here.
            if is_relay_addr(&t.remote) && (self.conn.path_parts(&t.remote).is_some() || !self.io.is_hub) {
                // The connectivity layer takes the packet: its deadlines may move.
                self.deadline.set(Due::Stale);
                let seg = t.segment_size.max(1);
                if let Some(data) = out.get(..t.len) {
                    for s in data.chunks(seg) {
                        self.conn.route(now, &self.io.ep, t.remote, s);
                    }
                }
                continue;
            }
            return Some(t);
        }
    }

    /// Apply a command of the application; the events it caused come out of [`Node::poll_event`].
    ///
    /// # Errors
    /// The endpoint's refusal.
    pub fn command(&mut self, now: Nanos, cmd: Command<'_, E::Src>) -> Result<Value, CommandError> {
        self.begin(now);
        let r = self.io.cmd(cmd);
        self.settle(now);
        r
    }

    /// Apply a command that only moves the application's own data (it writes, reads, opens or ends one of its
    /// streams): as [`command`](Self::command), except that the node's layers run only if the command raised an event
    /// or one waits in the endpoint. Such a command gives them nothing else to act on, and what is due by the clock
    /// comes at its deadline ([`poll_timeout`](Self::poll_timeout)). A host that moves data in many small commands
    /// spares the layers a full round for each.
    ///
    /// # Errors
    /// The endpoint's refusal.
    pub fn data_command(&mut self, now: Nanos, cmd: Command<'_, E::Src>) -> Result<Value, CommandError> {
        self.begin_endpoint(now);
        let r = self.io.cmd(cmd);
        if !self.io.evq.is_empty() || self.io.ep.events_waiting() {
            self.settle(now);
        }
        r
    }

    /// Dial `node` for `alpn`; the connectivity layer finds the way (known addresses, a lookup, the home relay).
    ///
    /// # Errors
    /// The endpoint's refusal.
    pub fn dial(
        &mut self,
        now: Nanos,
        node: vinc_crypto::NodeId,
        alpn: &[u8],
        role: Role,
        hints: &[SocketAddr],
    ) -> Result<SessionId, CommandError> {
        self.begin(now);
        self.io.learn_alg(&node);
        let r = self.conn.dial(now, &mut self.io.ep, node, alpn, role, hints);
        self.settle(now);
        r
    }

    /// The next event for the application.
    pub fn poll_event(&mut self) -> Option<NodeEvent> {
        let e = self.io.out.pop();
        // The node held events back in the endpoint while the queue was full: it takes them as the host makes room.
        if self.io.out.resumable() {
            let now = self.io.now;
            self.settle(now);
        }
        e
    }

    /// The next trace record. Empty unless tracing was configured.
    pub fn poll_trace(&mut self) -> Option<TraceItem> {
        let now = self.io.now;
        self.io.tq.pop(now)
    }

    /// The wall clock in milliseconds, as the host reads it now. The node advances it by its own clock between calls.
    pub fn set_wall_ms(&mut self, now: Nanos, wall_ms: u64) {
        self.begin(now);
        self.io.set_wall(wall_ms);
    }

    // ---------------------------------------------------------------- membership and broadcast

    /// The membership machine, for reading the view.
    pub const fn membership(&self) -> &Membership {
        &self.mem
    }

    /// The broadcast machine, for reading its tables.
    pub const fn broadcast(&self) -> &Topics {
        &self.topics
    }

    /// The host's stores of the layers above broadcast.
    pub const fn apps(&self) -> &A {
        &self.apps
    }

    /// The host's stores, for the host to fill: add a value to serve, a set item, a bundle's key.
    pub fn apps_mut(&mut self) -> &mut A {
        self.deadline.set(Due::Stale);
        &mut self.apps
    }

    /// The endpoint, for queries (statistics, reading a stream).
    pub const fn endpoint(&self) -> &E {
        &self.io.ep
    }

    /// End the node and give the endpoint back, so a host that recycles its connection memory can reuse it.
    pub fn into_endpoint(self) -> E {
        self.io.ep
    }

    /// The endpoint, for the calls the node does not wrap (reading a datagram, an interface event, a new prekey).
    /// Commands go through [`Node::command`], so the node sees their effects.
    pub fn endpoint_mut(&mut self) -> &mut E {
        self.deadline.set(Due::Stale);
        &mut self.io.ep
    }

    /// The connectivity client, for queries.
    pub fn connectivity(&self) -> &Connectivity<P, R, PEERS> {
        &self.conn
    }

    /// Publish `body` to `topic`; returns the message id.
    ///
    /// # Errors
    /// [`Refused`] for a long topic, a body over the configured limit, a full topic table or a signing failure.
    pub fn publish(&mut self, now: Nanos, topic: &[u8], body: &[u8]) -> Result<[u8; 8], Refused> {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        let r = t.publish(&mut h, now, topic, body);
        self.settle(now);
        r
    }

    /// Subscribe to `topic`.
    ///
    /// # Errors
    /// [`Refused`] for a long topic or a full topic table.
    pub fn subscribe(&mut self, now: Nanos, topic: &[u8]) -> Result<(), Refused> {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        let r = t.subscribe(&mut h, now, topic);
        self.settle(now);
        r
    }

    /// Unsubscribe from `topic`.
    pub fn unsubscribe(&mut self, now: Nanos, topic: &[u8]) {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        t.unsubscribe(&mut h, topic);
        self.settle(now);
    }

    /// Take `member` as a subscriber of `topic` to send to straight when no hub is reachable.
    pub fn hint_subscriber(&mut self, topic: &[u8], member: &NodeId) -> bool {
        self.deadline.set(Due::Stale);
        self.topics.hint(topic, member)
    }

    /// Name the peers this node holds sessions with: from then on the hubs hand it topic messages only from its
    /// connected component (see [`Topics::set_adjacent`](vinc_broadcast::Topics::set_adjacent)). Returns how many
    /// peers the record names.
    ///
    /// # Errors
    /// [`Refused::Sign`] if the record cannot be signed.
    pub fn set_adjacent(&mut self, now: Nanos, peers: &[NodeId]) -> Result<usize, Refused> {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        let r = t.set_adjacent(&mut h, now, peers);
        self.settle(now);
        r
    }

    /// On a hub: what its adjacency table holds, what it refused and whether it is closed
    /// ([`NodeEvent::ReachClosed`]); on a member: how many adjacency records it signed. See
    /// [`Topics::reach_stats`](vinc_broadcast::Topics::reach_stats).
    pub fn reach_stats(&self) -> ReachStats {
        self.topics.reach_stats()
    }

    /// The access-control layer answered a broadcast check ([`NodeEvent::BroadcastAcpCheck`]).
    pub fn broadcast_acp_answer(&mut self, now: Nanos, id: u32, allow: bool) {
        self.begin(now);
        self.refresh_alive(now);
        let (t, mut h) = self.bc_host();
        t.acp_answer(&mut h, now, id, allow);
        self.settle(now);
    }

    /// Leave the group: close every hub session with the leave code and every other session after it. A hub reports
    /// the member as left.
    pub fn leave(&mut self, now: Nanos) {
        self.begin(now);
        self.leaving = true;
        let (m, mut h) = self.mem_host();
        m.leave(&mut h);
        self.io.trace(NodeTrace::Left);
        // A refused shutdown leaves the sessions to the transport's own timeout.
        let _ = self.io.cmd(Command::Shutdown);
        self.settle(now);
    }

    /// The access-control layer lifted the revocation of `peer`; whether it was revoked. Its place in every
    /// revocation table is free again.
    pub fn unrevoke(&mut self, peer: &NodeId) -> bool {
        self.deadline.set(Due::Stale);
        let a = self.mem.unrevoke(peer);
        let b = self.topics.unrevoke(peer);
        let c = self.io.revoked.remove(peer);
        // The deny given while it was revoked must not outlive the revocation.
        let _ = self.io.cmd(Command::AcpForget {
            peer: self.io.full_id(peer),
        });
        a | b | c
    }

    /// The access-control layer's answer for `peer` changed: forget the endpoint's cached answer, so the peer's next
    /// session is checked afresh and a session already up is checked again at its next event.
    pub fn forget_access(&mut self, peer: &NodeId) {
        self.deadline.set(Due::Stale);
        let _ = self.io.cmd(Command::AcpForget {
            peer: self.io.full_id(peer),
        });
    }

    /// The access-control layer revoked `peer`: forget it in the view, the roster and the subscriptions, and close
    /// every session with it. Effective within this call.
    ///
    /// # Errors
    /// [`TableFull`] if the revocation table is full; nothing was recorded.
    pub fn revoke(&mut self, now: Nanos, peer: &NodeId) -> Result<(), TableFull> {
        self.begin(now);
        let (m, mut h) = self.mem_host();
        m.revoke(&mut h, now, peer)?;
        self.topics.revoke(peer);
        // A cached allow would admit the peer's next session before the check could refuse it.
        let _ = self.io.cmd(Command::AcpForget {
            peer: self.io.full_id(peer),
        });
        if self.io.revoked.len() < crate::config::TABLE_MAX {
            self.io.revoked.insert(*peer);
        }
        let mut sessions: Vec<SessionId> = Vec::new();
        let mut n = 0;
        while let Some(st) = self.io.ep.session_at(n) {
            n += 1;
            if st.node.is_some_and(|x| x.bytes == *peer) {
                sessions.push(st.session);
            }
        }
        for session in &sessions {
            // A session that cannot be closed now ends at the transport's own timeout; the peer is refused meanwhile.
            let _ = self.io.cmd(Command::Close {
                session: *session,
                error: crate::config::DENIED,
            });
        }
        self.io.trace(NodeTrace::Revoked {
            peer: tag(peer),
            sessions: sessions.len() as u64,
        });
        self.settle(now);
        Ok(())
    }

    /// The address of this node changed (a handover): the address tag moves on, and the connectivity layer restarts
    /// its discovery.
    pub fn address_changed(&mut self, now: Nanos) {
        self.begin(now);
        self.mem.address_changed(now);
        self.conn.link_changed(now);
        self.pm_restart(now);
        self.settle(now);
    }

    /// A hub is told that `member`'s relay carrier opened. The hub restores a member it confirmed down within the lease.
    pub fn member_carrier_opened(&mut self, now: Nanos, member: &NodeId) {
        self.begin(now);
        if self.io.carriers.len() < crate::config::TABLE_MAX || self.io.carriers.contains_key(member) {
            self.io.carriers.insert(*member, Carrier::Open);
        }
        self.io.trace(NodeTrace::Carrier {
            member: tag(member),
            open: 1,
        });
        let (m, mut h) = self.mem_host();
        m.carrier_return(&mut h, now, member);
        self.settle(now);
    }

    /// A hub is told that `member`'s relay carrier closed. `sleep` is the time of the sleep notice that preceded the
    /// close, if the relay saw one. The hub starts confirming the drop.
    pub fn member_carrier_closed(&mut self, now: Nanos, member: &NodeId, sleep: Option<Nanos>) {
        self.begin(now);
        if self.io.carriers.len() < crate::config::TABLE_MAX || self.io.carriers.contains_key(member) {
            self.io.carriers.insert(*member, Carrier::Gone { since: now, sleep });
        }
        self.io.trace(NodeTrace::Carrier {
            member: tag(member),
            open: 0,
        });
        let (m, mut h) = self.mem_host();
        m.carrier_gone(&mut h, now, member);
        self.settle(now);
    }
}

/// The local address a datagram carried by a relay arrives at: the node's current address of the sender's family, so it
/// names the path the sessions use after the node moved; the address the node started with only while none is set.
fn inbound_local(addrs: &[Option<SocketAddr>; MAX_ADDRS], from: &SocketAddr, fallback: SocketAddr) -> SocketAddr {
    addrs
        .iter()
        .flatten()
        .find(|a| a.is_ipv4() == from.is_ipv4())
        .copied()
        .unwrap_or(fallback)
}

/// Rebuild the ticket the address hash covers from the connectivity layer's candidates and home relay.
fn refresh_ticket<P: Provider, const R: usize, const PEERS: usize, E: Ep, St: Store>(
    io: &mut Io<E, St>,
    conn: &Connectivity<P, R, PEERS>,
    ident: &vinc_crypto::NodeId,
    local: &[Option<SocketAddr>; MAX_ADDRS],
) {
    let unspec = SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0);
    let mut c = [unspec; MAX_ADDRS];
    let n = conn.candidates(&mut c);
    let mut t = Ticket::new(*ident);
    if let Some(home) = conn.home().and_then(|h| conn.relay_cfg(h)) {
        t = t.with_home(home.id);
    }
    let found = c.get(..n).unwrap_or_default();
    io.reflexive = found.iter().any(|a| !local.contains(&Some(*a)));
    for a in found.iter().take(vinc_connect::ticket::MAX_ADDRS) {
        if let Ok(next) = t.with_addr(*a) {
            t = next;
        }
    }
    io.ticket_len = t.encode(&mut io.ticket).unwrap_or(0);
}

/// The identity algorithm of this node, for hosts that build peer ids from bare bytes.
impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// The full id of the peer whose short id is `id`: the algorithm learned from a session or a configured relay.
    pub fn full_id(&self, id: &NodeId) -> vinc_crypto::NodeId {
        self.io.full_id(id)
    }

    /// This node's full id.
    pub const fn id(&self) -> &vinc_crypto::NodeId {
        &self.ident
    }

    /// The identity algorithm of this node.
    pub const fn alg(&self) -> IdentityAlg {
        self.ident.alg
    }

    /// Whether this node is a hub.
    pub const fn is_hub(&self) -> bool {
        self.io.is_hub
    }
}

#[cfg(test)]
mod inbound_tests {
    use super::*;

    fn addr(s: &str) -> SocketAddr {
        s.parse()
            .unwrap_or_else(|_| SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0))
    }

    #[test]
    fn a_relayed_datagram_arrives_at_the_current_address_of_its_family() {
        let (old, new, v6) = (addr("10.0.0.1:4433"), addr("10.0.1.1:4433"), addr("[fd00::1]:4433"));
        let mut addrs = [None; MAX_ADDRS];
        for (d, a) in addrs.iter_mut().zip([v6, new]) {
            *d = Some(a);
        }
        assert_eq!(inbound_local(&addrs, &addr("240.0.0.3:0"), old), new);
        assert_eq!(inbound_local(&addrs, &addr("[fd00::9]:0"), old), v6);
        assert_eq!(inbound_local(&[None; MAX_ADDRS], &addr("240.0.0.3:0"), old), old);
    }
}
