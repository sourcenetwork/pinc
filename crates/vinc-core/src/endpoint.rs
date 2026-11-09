//! The endpoint: a bounded table of connections and every rule that spans more than one of them.
//!
//! The endpoint is SANS-IO. The host feeds it datagrams ([`Endpoint::handle_datagram`]), commands
//! ([`Endpoint::command`]) and the clock ([`Endpoint::handle_timeout`]); it hands back datagrams
//! ([`Endpoint::poll_transmit`]), events ([`Endpoint::poll_event`]) and the next deadline
//! ([`Endpoint::poll_timeout`]). It reads no clock, opens no socket and allocates nothing per packet.
//!
//! # Memory
//!
//! The caller owns the connection table: a `[Slot; K]` where every slot carries the memory (a buffer pool and a stream
//! table) its connections run in, so the endpoint never allocates and the caller chooses where the memory lives. An
//! endpoint is large (it holds the ticket stores, the ledger and every lookup table inline): place it in a `Box` or a
//! static. A slot whose memory a failed construction consumed is retired for good and counted in [`NodeStats`].
//!
//! # The rules
//!
//! - **Demultiplexing.** A fixed hash table maps each 4-byte connection id (the first one, the derived window and the
//!   id the dialer invented) to its sessions. Ids are derived from session secrets, so two sessions may hold the same
//!   four bytes; a datagram with an id several sessions hold is tried against each in turn on a copy, and the session
//!   whose keys open it owns it.
//! - **Amplification ledger.** Every outgoing datagram passes the [`Ledger`].
//! - **Half-open cap.** A first Initial creates state only in a datagram of at least 1200 bytes (464 for a short
//!   one), and only while fewer than 256 sessions are unauthenticated; a resumption Hello is exempt from the count.
//!   An unauthenticated session lives 30 s.
//! - **Round trips.** See [`NodeRtt`](crate::rtt::NodeRtt); the endpoint feeds them to every connection.
//! - **Access check.** An established session raises [`Event::AcpCheck`] unless a cached answer (30 s) exists; its
//!   application events are held until the answer allows it.
//! - **Sub-sessions.** A second protocol to a connected peer costs no round trip.
//!
//! Invariants: no table grows; no input panics; a datagram is counted once in [`NodeStats`]; a session is freed
//! exactly once and its memory returns to its slot.

use core::net::SocketAddr;

use vinc_crypto::{Drbg, NodeId, Provider};
use vinc_security::{Alpn, AlpnList, ClientTickets, ConnId, LocalIdentity, PrekeyInfo, ResponderStores};
use vinc_transport::conn::{Config, PathId, Resources};
use vinc_transport::stream::{self, StreamSource};

use crate::api::{Event, Events, NodeStats, SessionId};
use crate::heap::DeadlineHeap;
use crate::ledger::Ledger;
use crate::queue::{EVENT_HEADROOM, EventRing};
use crate::rtt::NodeRtt;
use crate::slot::{MAX_CIDS, NIL, Slot, State};
use crate::table::Table;
use crate::trace::{TraceLog, TraceRecord};

/// The length of every connection id the endpoint issues.
pub const CID_LEN: usize = 4;
/// The largest datagram the endpoint takes in; a longer one is dropped.
pub const MAX_DATAGRAM: usize = 9216;
/// The most interfaces.
pub const MAX_IFACES: usize = 8;
/// The most (local, remote) address pairs named by a path id at once.
pub const PATH_ENTRIES: usize = 1024;
/// The most peers whose access answer is cached, and the most checks waiting.
pub const ACP_ENTRIES: usize = 256;
/// Sub-session ids remembered so a repeated open is not accepted twice.
pub const SUBS_SEEN: usize = 1024;
/// The events the host may leave unread.
pub const EVENT_QUEUE: usize = 2048;
/// The most protocols the registry holds.
pub const MAX_ALPNS: usize = vinc_security::ids::MAX_ALPNS;
/// The peers whose prekey cache knowledge is remembered.
pub const PREKEY_PEERS: usize = 256;
/// How long a closing session may wait for its CLOSE to leave before it is dropped.
pub(crate) const CLOSE_GRACE: u64 = 1_000_000_000;

/// How the endpoint behaves; [`EndpointConfig::new`] holds the defaults.
#[derive(Debug, Clone, Copy)]
pub struct EndpointConfig {
    /// The base configuration of every connection. The connection id length is forced to [`CID_LEN`].
    pub conn: Config,
    /// Keys the hash of every lookup table; take it from the host's random generator.
    pub seed: u64,
    /// Tickets issued per full handshake (at most 4; 0 turns resumption off).
    pub tickets_per_session: u8,
    /// How long an issued ticket lives, in seconds.
    pub ticket_lifetime_s: u32,
}

impl EndpointConfig {
    /// The defaults, hashing with `seed`.
    pub const fn new(seed: u64) -> Self {
        Self {
            conn: Config::new(),
            seed,
            tickets_per_session: 1,
            ticket_lifetime_s: vinc_security::tickets::DEFAULT_TICKET_LIFETIME_S,
        }
    }
}

/// The access answer of one peer: whether it may connect, and the local time the answer stops counting.
#[derive(Debug, Clone, Copy)]
pub(crate) struct AcpAnswer {
    pub(crate) allow: bool,
    pub(crate) until: u64,
}

/// The counters the endpoint keeps for [`NodeStats`].
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct Counters {
    pub(crate) datagrams_in: u64,
    pub(crate) datagrams_out: u64,
    pub(crate) dropped_in: u64,
    pub(crate) held_by_ledger: u64,
    pub(crate) stalled_in: u64,
    pub(crate) retired: u64,
}

/// The endpoint; see the module docs.
///
/// Type parameters: the crypto provider `P`, the source type `S` of source-backed streams, `N` stream slots, `C` chunk
/// ring entries per stream half, `F` packets tracked in flight and `NP` paths per connection (as for the
/// transport's `Connection`), `K` sessions in the table, `D` entries of the connection id table (at least ten per
/// session), `PK` prekeys and `TK` tickets in the responder's stores and `CT` tickets this node holds as a client.
#[allow(clippy::type_complexity, reason = "the table sizes are the type's parameters")]
pub struct Endpoint<
    's,
    'a,
    P: Provider,
    S: StreamSource,
    const N: usize,
    const C: usize,
    const F: usize,
    const NP: usize,
    const K: usize,
    const D: usize,
    const PK: usize,
    const TK: usize,
    const CT: usize,
> {
    pub(crate) provider: P,
    pub(crate) drbg: Drbg,
    pub(crate) identity: LocalIdentity,
    pub(crate) prekey: Option<PrekeyInfo>,
    pub(crate) cfg: EndpointConfig,
    pub(crate) alpns: [Option<Alpn>; MAX_ALPNS],
    pub(crate) slots: &'s mut [Slot<'a, P, S, N, C, F, NP>; K],
    pub(crate) free: u32,
    pub(crate) live: usize,
    pub(crate) half_open: usize,
    pub(crate) demux: Table<ConnId, u32, D>,
    pub(crate) by_peer: Table<NodeId, u32, K>,
    pub(crate) heap: DeadlineHeap<K>,
    pub(crate) dirty_head: [u32; 2],
    pub(crate) dirty_tail: [u32; 2],
    pub(crate) ledger: Ledger,
    pub(crate) rtt: NodeRtt,
    pub(crate) node_ver: u64,
    pub(crate) ekk: Table<NodeId, [u8; 32], PREKEY_PEERS>,
    pub(crate) acp: Table<NodeId, AcpAnswer, ACP_ENTRIES>,
    pub(crate) checks: Table<u64, NodeId, ACP_ENTRIES>,
    pub(crate) check_of: Table<NodeId, u64, ACP_ENTRIES>,
    pub(crate) next_check: u64,
    pub(crate) stores: ResponderStores<PK, TK>,
    pub(crate) tickets: ClientTickets<CT>,
    pub(crate) paths: Table<(SocketAddr, SocketAddr), u32, PATH_ENTRIES>,
    pub(crate) next_path_gen: u32,
    pub(crate) ifaces: [Option<SocketAddr>; MAX_IFACES],
    pub(crate) subs_seen: Table<ConnId, (), SUBS_SEEN>,
    pub(crate) events: EventRing<EVENT_QUEUE>,
    /// Some session has `parked` work.
    pub(crate) backlog: bool,
    /// The latest time an entry point was called with.
    pub(crate) last_now: u64,
    pub(crate) capture: Option<Events>,
    pub(crate) scratch: [u8; MAX_DATAGRAM],
    pub(crate) stash: [u8; MAX_DATAGRAM],
    pub(crate) stash_meta: Option<StashMeta>,
    pub(crate) udp_heard: Option<u64>,
    pub(crate) started: u64,
    pub(crate) t_first: Option<u64>,
    pub(crate) quiet_until: u64,
    pub(crate) suspended: bool,
    pub(crate) moved: bool,
    pub(crate) counters: Counters,
    pub(crate) trace: TraceLog,
}

/// A datagram built for a destination other than the one being batched, kept for the next call.
#[derive(Debug, Clone, Copy)]
pub(crate) struct StashMeta {
    pub(crate) path: PathId,
    pub(crate) len: usize,
    pub(crate) segment: usize,
}

macro_rules! ep_impl {
    ($($body:tt)*) => {
        impl<'s, 'a, P, S, const N: usize, const C: usize, const F: usize, const NP: usize, const K: usize,
            const D: usize, const PK: usize, const TK: usize, const CT: usize>
            $crate::Endpoint<'s, 'a, P, S, N, C, F, NP, K, D, PK, TK, CT>
        where
            P: ::vinc_crypto::Provider,
            S: ::vinc_transport::stream::StreamSource,
        {
            $($body)*
        }
    };
}
pub(crate) use ep_impl;

/// The environment a connection call needs, borrowing only the provider and the generator.
macro_rules! env {
    ($s:ident, $now:expr) => {
        ::vinc_security::Env {
            provider: &$s.provider,
            now: $now,
            drbg: &mut $s.drbg,
        }
    };
}
pub(crate) use env;

ep_impl! {
    /// A new endpoint at time `now`, with `slots` as its connection table. Every slot must be free (built with
    /// [`Slot::new`]). `D` must be at least ten times `K`.
    ///
    pub fn new(
        now: u64,
        provider: P,
        drbg: Drbg,
        identity: LocalIdentity,
        mut cfg: EndpointConfig,
        slots: &'s mut [Slot<'a, P, S, N, C, F, NP>; K],
    ) -> Self {
        const { assert!(2 * K + 64 <= EVENT_HEADROOM, "the event queue headroom is too small for the session table") };
        cfg.conn.cid_len = CID_LEN;
        let seed = cfg.seed;
        let last = K.saturating_sub(1);
        for (i, s) in slots.iter_mut().enumerate() {
            s.m.next_free = if i < last { u32::try_from(i + 1).unwrap_or(NIL) } else { NIL };
        }
        Self {
            provider,
            drbg,
            identity,
            prekey: None,
            cfg,
            alpns: [None; MAX_ALPNS],
            slots,
            free: if K == 0 { NIL } else { 0 },
            live: 0,
            half_open: 0,
            demux: Table::new(seed ^ 0x01),
            by_peer: Table::new(seed ^ 0x02),
            heap: DeadlineHeap::new(),
            dirty_head: [NIL; 2],
            dirty_tail: [NIL; 2],
            ledger: Ledger::new(seed ^ 0x03),
            rtt: NodeRtt::new(seed ^ 0x04),
            node_ver: 1,
            ekk: Table::new(seed ^ 0x05),
            acp: Table::new(seed ^ 0x06),
            checks: Table::new(seed ^ 0x07),
            check_of: Table::new(seed ^ 0x08),
            next_check: 1,
            stores: ResponderStores::default(),
            tickets: ClientTickets::new(),
            paths: Table::new(seed ^ 0x09),
            next_path_gen: 1,
            ifaces: [None; MAX_IFACES],
            subs_seen: Table::new(seed ^ 0x0A),
            events: EventRing::new(),
            backlog: false,
            last_now: now,
            capture: None,
            scratch: [0; MAX_DATAGRAM],
            stash: [0; MAX_DATAGRAM],
            stash_meta: None,
            udp_heard: None,
            started: now,
            t_first: None,
            quiet_until: 0,
            suspended: false,
            moved: false,
            counters: Counters::default(),
            trace: TraceLog::new(),
        }
    }

    /// Set the prekey new dials carry; the host rotates it.
    pub fn set_prekey(&mut self, prekey: PrekeyInfo) {
        self.prekey = Some(prekey);
    }

    /// Accept sessions for `alpn`. Returns false when the registry is full or the name is empty or too long.
    pub fn register_alpn(&mut self, alpn: &[u8]) -> bool {
        let Some(a) = Alpn::new(alpn) else { return false };
        if alpn.is_empty() {
            return false;
        }
        if self.alpns.iter().flatten().any(|x| *x == a) {
            return true;
        }
        match self.alpns.iter_mut().find(|s| s.is_none()) {
            Some(s) => {
                *s = Some(a);
                true
            }
            None => false,
        }
    }

    /// Stop accepting sessions for `alpn`.
    pub fn unregister_alpn(&mut self, alpn: &[u8]) {
        for s in &mut self.alpns {
            if s.is_some_and(|a| a.as_bytes() == alpn) {
                *s = None;
            }
        }
    }

    /// The registry as the handshake takes it.
    pub(crate) fn alpn_list(&self) -> Option<AlpnList> {
        let mut buf: [&[u8]; MAX_ALPNS] = [&[]; MAX_ALPNS];
        let mut n = 0;
        for (d, a) in buf.iter_mut().zip(self.alpns.iter().flatten()) {
            *d = a.as_bytes();
            n += 1;
        }
        AlpnList::new(buf.get(..n)?)
    }

    /// Whether `alpn` is in the registry.
    pub(crate) fn accepts(&self, alpn: &[u8]) -> bool {
        self.alpns.iter().flatten().any(|a| a.as_bytes() == alpn)
    }

    /// This node's identity.
    pub const fn identity(&self) -> &LocalIdentity {
        &self.identity
    }

    /// The responder's shared stores (prekey cache and issued tickets).
    pub const fn stores(&mut self) -> &mut ResponderStores<PK, TK> {
        &mut self.stores
    }

    /// The tickets this node holds as a client.
    pub const fn tickets(&mut self) -> &mut ClientTickets<CT> {
        &mut self.tickets
    }

    /// The node round trips.
    pub const fn rtt(&self) -> &NodeRtt {
        &self.rtt
    }

    /// The amplification ledger.
    pub const fn ledger(&self) -> &Ledger {
        &self.ledger
    }

    /// The node-wide numbers.
    pub fn node_stats(&self) -> NodeStats {
        NodeStats {
            sessions: self.live,
            half_open: self.half_open,
            lrtt: self.rtt.lrtt(),
            tgr: self.rtt.tgr(),
            hs_floor: self.rtt.hs_floor(),
            thin: self.rtt.thin_node(),
            ledger: self.ledger.len(),
            datagrams_in: self.counters.datagrams_in,
            datagrams_out: self.counters.datagrams_out,
            dropped_in: self.counters.dropped_in,
            held_by_ledger: self.counters.held_by_ledger,
            stalled_in: self.counters.stalled_in,
            events_dropped: self.events.dropped,
            events_lost: self.events.lost,
        }
    }

    /// Slots a failed construction retired for good.
    pub const fn retired_slots(&self) -> u64 {
        self.counters.retired
    }

    /// Trace records dropped because the ring was full.
    pub const fn trace_dropped(&self) -> u64 {
        self.trace.dropped()
    }

    /// The next trace record, oldest first. Always `None` without the `trace` feature.
    pub fn poll_trace(&mut self) -> Option<TraceRecord> {
        self.trace.pop()
    }

    /// The next event, oldest first.
    pub fn poll_event(&mut self) -> Option<Event> {
        let ev = self.events.pop();
        if self.backlog && !self.events.stalled() {
            self.resume_parked(self.last_now);
        }
        ev
    }

    /// Queue an event for the host, or put it in the reply of the command being applied.
    pub(crate) fn emit(&mut self, ev: Event) {
        if let Some(cap) = self.capture.as_mut()
            && cap.push(ev)
        {
            return;
        }
        self.events.push(ev);
    }

    pub(crate) fn session_id(&self, i: usize) -> SessionId {
        SessionId::new(i, self.slots.get(i).map_or(0, |s| s.m.generation))
    }

    /// The slot of `id` if the session is live.
    pub(crate) fn slot_of(&self, id: SessionId) -> Option<usize> {
        let s = self.slots.get(id.slot())?;
        (s.m.in_use && s.m.generation == id.generation() && s.conn.is_some()).then_some(id.slot())
    }

    /// The session ids of the live sessions, in table order.
    pub fn sessions(&self) -> impl Iterator<Item = SessionId> + '_ {
        self.slots
            .iter()
            .enumerate()
            .filter(|(_, s)| s.m.in_use && s.conn.is_some())
            .map(|(i, s)| SessionId::new(i, s.m.generation))
    }

    // ---- paths ----

    /// The path id of a pair of addresses, creating it if needed.
    pub(crate) fn path_id(&mut self, local: SocketAddr, remote: SocketAddr) -> PathId {
        let key = (local, remote);
        if let Some(i) = self.paths.index_of(&key) {
            self.paths.touch(&key);
            let generation = self.paths.at_index(i).map_or(0, |(_, g)| *g);
            return PathId(u64::from(generation) << 32 | i as u64);
        }
        let generation = self.next_path_gen;
        self.next_path_gen = self.next_path_gen.wrapping_add(1).max(1);
        self.paths.insert(key, generation);
        let i = self.paths.index_of(&key).unwrap_or(0);
        PathId(u64::from(generation) << 32 | i as u64)
    }

    /// The addresses a path id names.
    pub(crate) fn path_addrs(&self, id: PathId) -> Option<(SocketAddr, SocketAddr)> {
        let i = usize::try_from(id.0 & 0xFFFF_FFFF).ok()?;
        let (key, generation) = self.paths.at_index(i)?;
        (u64::from(*generation) == id.0 >> 32).then_some(*key)
    }

    // ---- the slot table ----

    /// Take a free slot for a new session and prepare its memory for `client`'s role.
    pub(crate) fn alloc_slot(&mut self, client: bool, now: u64) -> Option<(usize, Resources<'a, S, N, C>)> {
        let i = self.free as usize;
        let slot = self.slots.get_mut(i)?;
        let mut mem = slot.mem.take()?;
        self.free = slot.m.next_free;
        mem.pool.reset();
        mem.streams.reinit(&stream::Config::new(client), &mem.pool);
        slot.m.begin(client, now);
        self.live += 1;
        Some((i, mem))
    }

    /// Give a slot back without a connection (its construction failed). The memory went with the failed call.
    pub(crate) fn retire_slot(&mut self, i: usize) {
        if let Some(s) = self.slots.get_mut(i) {
            s.m.in_use = false;
            s.m.generation = s.m.generation.wrapping_add(1);
        }
        self.live = self.live.saturating_sub(1);
        self.counters.retired += 1;
    }

    /// Register a datagram destination id for session `i`.
    pub(crate) fn register_cid(&mut self, i: usize, cid: ConnId) -> bool {
        u32::try_from(i).is_ok_and(|i| self.demux.insert_dup(cid, i))
    }

    /// Bring the demultiplexing table in line with the connection ids session `i` accepts now.
    pub(crate) fn sync_cids(&mut self, i: usize, force: bool) {
        let Some(slot) = self.slots.get_mut(i) else { return };
        let Some(conn) = slot.conn.as_ref() else { return };
        let epoch = conn.cid_epoch();
        if !force && slot.m.cid_epoch == epoch {
            return;
        }
        let Ok(idx) = u32::try_from(i) else { return };
        let mut new: [Option<ConnId>; MAX_CIDS] = [None; MAX_CIDS];
        for (d, c) in new.iter_mut().zip(conn.local_cids()) {
            *d = Some(c);
        }
        for old in slot.m.cids.iter().flatten() {
            if !new.contains(&Some(*old)) {
                self.demux.remove_pair(old, &idx);
            }
        }
        for n in new.iter().flatten() {
            if !slot.m.cids.contains(&Some(*n)) {
                self.demux.insert_dup(*n, idx);
            }
        }
        slot.m.cids = new;
        slot.m.cid_epoch = epoch;
    }

    /// End session `i`: unregister it, return its memory to the slot and put the slot on the free list.
    pub(crate) fn free_slot(&mut self, i: usize, now: u64) {
        let Ok(idx) = u32::try_from(i) else { return };
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        for c in slot.m.cids.iter().flatten() {
            self.demux.remove_pair(c, &idx);
        }
        if let Some(o) = slot.m.odcid.take() {
            self.demux.remove_pair(&o, &idx);
        }
        slot.m.cids = [None; MAX_CIDS];
        if slot.m.half_open {
            self.half_open = self.half_open.saturating_sub(1);
            slot.m.half_open = false;
        }
        let peer = slot.m.peer;
        let linked = slot.m.linked;
        let step_dialer = u64::from(slot.m.client);
        slot.m.held.clear();
        slot.m.in_use = false;
        slot.m.state = State::Closing;
        slot.m.generation = slot.m.generation.wrapping_add(1);
        slot.m.next_free = self.free;
        if let Some(c) = slot.conn.take() {
            slot.mem = Some(c.into_resources());
        }
        self.free = idx;
        self.live = self.live.saturating_sub(1);
        self.heap.set(i, None);
        if let Some(p) = peer.filter(|_| linked) {
            self.unlink_peer(&p, idx);
        }
        crate::trace::trace!(self, now, Session { slot: i as u64, step: 2, dialer: step_dialer });
        let _ = (now, step_dialer);
    }

    /// Append session `idx` to the end of its peer's list, so sessions are visited in the order they were made.
    pub(crate) fn link_peer(&mut self, peer: NodeId, idx: u32) {
        if self.slots.get(idx as usize).is_none_or(|s| s.m.linked) {
            return;
        }
        if let Some(s) = self.slots.get_mut(idx as usize) {
            s.m.peer_next = NIL;
            s.m.linked = true;
        }
        let Some(mut cur) = self.by_peer.get(&peer).copied() else {
            self.by_peer.insert(peer, idx);
            return;
        };
        while let Some(next) = self.slots.get(cur as usize).map(|s| s.m.peer_next).filter(|n| *n != NIL) {
            cur = next;
        }
        if let Some(s) = self.slots.get_mut(cur as usize) {
            s.m.peer_next = idx;
        }
    }

    fn unlink_peer(&mut self, peer: &NodeId, idx: u32) {
        let Some(head) = self.by_peer.get(peer).copied() else { return };
        let after = self.slots.get(idx as usize).map_or(NIL, |s| s.m.peer_next);
        if head == idx {
            if after == NIL {
                self.by_peer.remove(peer);
            } else {
                self.by_peer.insert(*peer, after);
            }
            return;
        }
        let mut cur = head;
        while let Some(s) = self.slots.get_mut(cur as usize) {
            if s.m.peer_next == idx {
                s.m.peer_next = after;
                return;
            }
            cur = s.m.peer_next;
        }
    }

    /// Make session `session` also answer to `cid`, so two sessions hold the same four bytes and a datagram for them is
    /// tried against each. For tests of the collision path; returns false if the session or the table cannot take it.
    #[cfg(feature = "inject")]
    pub fn alias_cid(&mut self, session: SessionId, cid: [u8; CID_LEN]) -> bool {
        let (Some(i), Some(c)) = (self.slot_of(session), ConnId::new(&cid)) else { return false };
        self.register_cid(i, c)
    }

    /// The first session of `peer`, oldest first, for which `f` holds.
    pub(crate) fn peer_find(&self, peer: &NodeId, f: impl Fn(&Self, usize) -> bool) -> Option<usize> {
        self.peer_sessions(peer).find(|i| f(self, *i))
    }

    /// The sessions of `peer`, oldest first.
    pub(crate) fn peer_sessions(&self, peer: &NodeId) -> impl Iterator<Item = usize> + '_ {
        let mut cur = self.by_peer.get(peer).copied().unwrap_or(NIL);
        core::iter::from_fn(move || {
            let s = self.slots.get(cur as usize)?;
            let i = cur as usize;
            cur = s.m.peer_next;
            Some(i)
        })
    }

    // ---- sending queues ----

    /// Queue session `i` for a send attempt. A broadcast session without a sub-session open to send waits behind the
    /// others.
    pub(crate) fn mark_dirty(&mut self, i: usize) {
        let Ok(idx) = u32::try_from(i) else { return };
        let Some(s) = self.slots.get_mut(i) else { return };
        if s.m.dirty != 0 || !s.m.in_use {
            return;
        }
        let q = usize::from(s.m.gossip && !s.m.ctrl_pending);
        s.m.dirty = u8::try_from(q + 1).unwrap_or(1);
        s.m.dirty_next = NIL;
        let tail = self.dirty_tail.get(q).copied().unwrap_or(NIL);
        match self.slots.get_mut(tail as usize) {
            Some(t) => t.m.dirty_next = idx,
            None => {
                if let Some(h) = self.dirty_head.get_mut(q) {
                    *h = idx;
                }
            }
        }
        if let Some(t) = self.dirty_tail.get_mut(q) {
            *t = idx;
        }
    }

    /// The first session waiting to send: ordinary sessions before broadcast ones.
    pub(crate) fn dirty_front(&self) -> Option<(usize, usize)> {
        (0..2).find_map(|q| {
            let h = self.dirty_head.get(q).copied()?;
            (h != NIL).then_some((q, h as usize))
        })
    }

    /// Take the first session of queue `q` off it.
    pub(crate) fn dirty_pop(&mut self, q: usize) {
        let Some(h) = self.dirty_head.get(q).copied().filter(|h| *h != NIL) else { return };
        let Some(s) = self.slots.get_mut(h as usize) else { return };
        let next = s.m.dirty_next;
        s.m.dirty = 0;
        s.m.dirty_next = NIL;
        if let Some(x) = self.dirty_head.get_mut(q) {
            *x = next;
        }
        if next == NIL
            && let Some(t) = self.dirty_tail.get_mut(q)
        {
            *t = NIL;
        }
    }

    /// Move the first session of queue `q` to its end, so the others get a turn.
    pub(crate) fn dirty_rotate(&mut self, q: usize) {
        let Some(h) = self.dirty_head.get(q).copied().filter(|h| *h != NIL) else { return };
        if self.dirty_head.get(q) == self.dirty_tail.get(q) {
            return;
        }
        self.dirty_pop(q);
        self.mark_dirty(h as usize);
    }
}
