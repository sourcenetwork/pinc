//! The endpoint: a bounded table of connections and every rule that spans more than one of them.
//!
//! The endpoint is SANS-IO. The host feeds it datagrams ([`Endpoint::handle_datagram`]), commands
//! ([`Endpoint::command`]) and the clock ([`Endpoint::handle_timeout`]); it hands back datagrams
//! ([`Endpoint::poll_transmit`]), events ([`Endpoint::poll_event`]) and the next deadline
//! ([`Endpoint::poll_timeout`]). It reads no clock, opens no socket and allocates nothing per packet.
//!
//! # Memory
//!
//! The connection table is a `[Slot; K]` where every slot carries the memory (a buffer pool and a stream table) its
//! connections run in. With [`Endpoint::new`] the caller owns it and chooses where the memory lives, and the endpoint
//! itself never allocates without the `alloc` feature; such an endpoint is large (it holds the ticket stores, the ledger
//! and every lookup table inline): place it in a `Box` or a static. With `alloc` the lookup tables are on the heap and
//! [`Endpoint::new_owned`] builds an endpoint that owns its table, built on the heap piece by piece, and makes the
//! memory of a slot when the slot is first taken: it holds the memory of the most sessions it has had at once
//! ([`Endpoint::backed_slots`]), kept for the sessions that follow. A slot whose memory a failed construction
//! consumed is retired for good and counted in [`NodeStats`].
//!
//! # The rules
//!
//! - **Demultiplexing.** A fixed hash table maps each 4-byte connection id (the first one, the derived window and the
//!   id the dialer invented) to its sessions. Ids are derived from session secrets, so two sessions may hold the same
//!   four bytes; a datagram with an id several sessions hold is tried against each in turn on a copy. A short datagram
//!   goes to the first holder that does not answer undecryptable or unroutable, a long packet to the first holder (see
//!   `rx`), and the candidate list can name a slot twice. A connection never lists an id twice (the transport draws
//!   the next index for a derived id equal to one it holds), and the table holds one entry per copy a connection
//!   lists. The table needs at least ten entries per session; the table sizes are type parameters the embedding
//!   crate picks, and nothing checks the ratio at run time.
//! - **Sessions by address.** A second table of `K` entries maps the remote address of each session whose active path
//!   is validated and direct to its slot, so [`Endpoint::session_from`] finds who sent a datagram without a walk of
//!   the sessions. Every input that touches a session settles it, and settling brings the session's entry in line with
//!   its path (validation, migration, a rebind); freeing a slot removes it. A slot holds at most one entry, so the
//!   table never fills; a lookup checks each entry against the session's path, so an entry whose path the table of
//!   address pairs evicted since is not an answer.
//! - **Amplification ledger.** Every outgoing datagram passes the [`Ledger`].
//! - **Half-open cap.** A first Initial creates state only in a datagram of at least 1200 bytes (464 for a short
//!   one), and only while fewer than 256 sessions are unauthenticated; a resumption Hello is exempt from the count.
//!   An unauthenticated session lives as long as an unestablished handshake: 30 s, 60 s on a thin node.
//! - **Reordered first flights.** A later part of a first message that arrives before its start is held: at most 4
//!   datagrams of at most 1500 bytes for the whole endpoint, for at most 1 s, the oldest given up first, and handed
//!   only to the session the start of the same message from the same address creates.
//! - **Round trips.** See [`NodeRtt`](crate::rtt::NodeRtt); the endpoint feeds them to every connection.
//! - **Access check.** An established session raises [`Event::AcpCheck`] unless a cached answer (30 s) exists; its
//!   application events are held until the answer allows it.
//! - **Sub-sessions.** A second protocol to a connected peer costs no round trip.
//!
//! Invariants: no table grows; no input panics; a datagram is counted once in [`NodeStats`]; a session is freed
//! exactly once and its memory returns to its slot.

use core::net::SocketAddr;

use pinc_crypto::{Drbg, NodeId, Provider};
use pinc_security::{Alpn, AlpnList, ClientTickets, ConnId, LocalIdentity, PrekeyInfo, ResponderStores};
use pinc_transport::conn::{Config, PathId, Resources};
use pinc_transport::stream::{self, StreamSource};

use crate::api::{Event, Events, NodeStats, SessionId};
use crate::heap::DeadlineHeap;
use crate::ledger::Ledger;
use crate::queue::EventRing;
use crate::rtt::NodeRtt;
use crate::slot::{MAX_CIDS, NIL, Slot, State, cid_delta};
use crate::store::{Store, filled};
use crate::table::Table;
use crate::trace::{TraceLog, TraceRecord};

/// The length of every connection id the endpoint issues.
pub const CID_LEN: usize = 4;
// The Initial padding covers a Reply cut into minimum-size datagrams only with ids this short.
const _: () = assert!(CID_LEN <= pinc_security::message::SPLIT_CID_MAX);
/// The largest datagram the endpoint takes in; a longer one is dropped.
pub const MAX_DATAGRAM: usize = 9216;
/// The most interfaces.
pub const MAX_IFACES: usize = 8;
/// Sub-session ids remembered so a repeated open is not accepted twice.
pub const SUBS_SEEN: usize = 1024;
/// The most protocols the registry holds.
pub const MAX_ALPNS: usize = pinc_security::ids::MAX_ALPNS;
/// The peers whose prekey cache knowledge is remembered.
pub const PREKEY_PEERS: usize = 256;
/// The addresses whose last re-join challenge is remembered.
pub(crate) const REJOIN_ADDRS: usize = 200;
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

/// The path id of entry `index` of the path table, whose entry holds `generation`.
pub(crate) const fn path_id_at(generation: u32, index: usize) -> PathId {
    PathId((generation as u64) << 32 | index as u64)
}

impl EndpointConfig {
    /// The defaults, hashing with `seed`. A first handshake flight that fits one datagram leaves whole; only its
    /// retransmissions are cut to the minimum datagram size, so a path that drops the larger datagram still connects.
    pub const fn new(seed: u64) -> Self {
        Self {
            conn: Config {
                flight_split: true,
                ..Config::new()
            },
            seed,
            tickets_per_session: 1,
            ticket_lifetime_s: pinc_security::tickets::DEFAULT_TICKET_LIFETIME_S,
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
    pub(crate) dropped_out: u64,
    pub(crate) reach_dropped: u64,
    pub(crate) ext_dropped: u64,
    pub(crate) held_by_ledger: u64,
    pub(crate) stalled_in: u64,
    pub(crate) backlog_refused: u64,
    pub(crate) holders_refused: u64,
    pub(crate) first_too_short: u64,
    pub(crate) stateless_rejects: u64,
    pub(crate) stateless_refused: u64,
    pub(crate) retired: u64,
}

/// The endpoint; see the module docs.
///
/// Type parameters: the crypto provider `P`, the source type `S` of source-backed streams, `N` stream slots, `C` chunk
/// ring entries per stream half, `F` packets tracked in flight and `NP` paths per connection (as for the
/// transport's `Connection`), `K` sessions in the table, `D` entries of the connection id table and of the table of address pairs (at least ten per
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
    pub(crate) slots: Slots<'s, Slot<'a, P, S, N, C, F, NP>, K>,
    /// What an endpoint that owns its table makes a slot's memory from; `None` when the host gave every slot its own.
    #[cfg(feature = "alloc")]
    pub(crate) fresh: Option<Fresh>,
    pub(crate) free: u32,
    pub(crate) live: usize,
    pub(crate) half_open: usize,
    pub(crate) demux: Table<ConnId, u32, D>,
    pub(crate) by_peer: Table<NodeId, u32, K>,
    /// The remote address of each session whose active path is validated and direct, to its slot (`Meta::route`).
    pub(crate) by_route: Table<SocketAddr, u32, K>,
    pub(crate) heap: DeadlineHeap<K>,
    /// The sessions that may have something to send, in two queues. An entry can name a slot that was freed or reused
    /// since it was queued; it is skipped when served.
    pub(crate) dirty_head: [u32; 2],
    pub(crate) dirty_tail: [u32; 2],
    pub(crate) ledger: Ledger,
    pub(crate) rtt: NodeRtt,
    pub(crate) node_ver: u64,
    pub(crate) ekk: Table<NodeId, [u8; 32], PREKEY_PEERS>,
    /// The cached access answers, the pending checks and the check of each peer: `D` entries each, ten per session
    /// of the endpoint's capacity (10 240 at the default capacity of 1024 sessions).
    pub(crate) acp: Table<NodeId, AcpAnswer, D>,
    pub(crate) checks: Table<u64, NodeId, D>,
    pub(crate) check_of: Table<NodeId, u64, D>,
    pub(crate) next_check: u64,
    pub(crate) stores: ResponderStores<PK, TK>,
    pub(crate) tickets: ClientTickets<CT>,
    pub(crate) paths: Table<(SocketAddr, SocketAddr), u32, D>,
    pub(crate) next_path_gen: u32,
    pub(crate) ifaces: [Option<SocketAddr>; MAX_IFACES],
    pub(crate) subs_seen: Table<ConnId, (), SUBS_SEEN>,
    pub(crate) events: EventRing<K>,
    /// The sessions with `parked` work, each at most once.
    pub(crate) parked: Store<u32, K>,
    /// Whether session slot `i` is in `parked`; kept beside the list, not in the slot, so a slot reused while listed
    /// is not listed twice and the list never outgrows `K`.
    pub(crate) is_parked: Store<bool, K>,
    pub(crate) parked_len: usize,
    /// The latest time an entry point was called with.
    pub(crate) last_now: u64,
    pub(crate) reach_in: crate::reach::ReachRing,
    pub(crate) ext_in: crate::ext_in::ExtRing,
    pub(crate) capture: Option<Events>,
    pub(crate) scratch: [u8; MAX_DATAGRAM],
    pub(crate) orphans: crate::orphan::Orphans,
    pub(crate) stash: [u8; MAX_DATAGRAM],
    pub(crate) stash_meta: Option<StashMeta>,
    pub(crate) udp_heard: Option<u64>,
    /// How many more sessions the host can take waiting to be accepted (`set_backlog_room`).
    pub(crate) backlog_room: usize,
    /// Server sessions this node made that the host has not taken yet: their handshakes are under way, or their
    /// `Incoming` waits to be read.
    pub(crate) owed: usize,
    /// Whether the ledger holds the source of the datagram being handled (set by `handle_datagram`).
    pub(crate) rx_held: bool,
    pub(crate) started: u64,
    pub(crate) t_first: Option<u64>,
    pub(crate) quiet_until: u64,
    pub(crate) suspended: bool,
    pub(crate) moved: bool,
    /// The node lost its link and has not seen it return, its address change or a resume since.
    pub(crate) dark: bool,
    /// The remote address of a re-join challenge of a thin session, and when it was last sent: the node's thin
    /// sessions space their re-join challenges to one address.
    pub(crate) rejoin_sent: Table<SocketAddr, u64, REJOIN_ADDRS>,
    pub(crate) counters: Counters,
    pub(crate) trace: TraceLog,
    /// The rejects the endpoint answers first messages with, without a session, that wait to be sent. Declared last:
    /// it is touched only when a first message is rejected, and placed here it moves no field a packet touches.
    pub(crate) rejects: crate::stateless::Rejects,
}

/// The connection table: lent by the caller, or (with `alloc`) owned by the endpoint. An owned table has room for
/// `K` slots and holds those taken so far: a slot is written when it is first taken, so an endpoint for thousands of
/// sessions that has had ten touches the memory of ten.
pub(crate) enum Slots<'s, T, const K: usize> {
    Borrowed(&'s mut [T; K]),
    #[cfg(feature = "alloc")]
    Owned(alloc::vec::Vec<T>),
}

impl<T, const K: usize> core::ops::Deref for Slots<'_, T, K> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        match self {
            Self::Borrowed(r) => r.as_slice(),
            #[cfg(feature = "alloc")]
            Self::Owned(v) => v,
        }
    }
}

impl<T, const K: usize> core::ops::DerefMut for Slots<'_, T, K> {
    fn deref_mut(&mut self) -> &mut [T] {
        match self {
            Self::Borrowed(r) => r.as_mut_slice(),
            #[cfg(feature = "alloc")]
            Self::Owned(v) => v,
        }
    }
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
            P: ::pinc_crypto::Provider,
            S: ::pinc_transport::stream::StreamSource,
        {
            $($body)*
        }
    };
}
pub(crate) use ep_impl;

#[cfg(feature = "alloc")]
impl<
    P,
    S,
    const N: usize,
    const C: usize,
    const F: usize,
    const NP: usize,
    const K: usize,
    const D: usize,
    const PK: usize,
    const TK: usize,
    const CT: usize,
> Endpoint<'static, 'static, P, S, N, C, F, NP, K, D, PK, TK, CT>
where
    P: Provider,
    S: StreamSource,
{
    /// A new endpoint that owns its connection table and the memory of every slot: up to `pool_chunks` buffer chunks
    /// and a stream table each, and one loss estimate they share. A slot and its memory are made when the slot is
    /// first taken and kept for the sessions that follow in it, and its buffer chunks are made a segment at a time as
    /// a session needs them. So the endpoint holds the memory of as many sessions as it has had at once, as large as
    /// they grew, not of the `K` it may have. Nothing outlives the endpoint and nothing is borrowed, so dropping it
    /// frees everything. The endpoint is built on the heap, piece by piece: no table of megabytes is ever formed on
    /// the stack. `D` must be at least ten times `K`.
    pub fn new_owned(
        now: u64,
        provider: P,
        drbg: Drbg,
        identity: LocalIdentity,
        cfg: EndpointConfig,
        pool_chunks: usize,
    ) -> alloc::boxed::Box<Self> {
        use alloc::{boxed::Box, vec::Vec};

        // Room for every slot at once, so the table never moves; the system commits it as slots are written.
        let mut ep = Box::new(Self::with_slots(
            now,
            provider,
            drbg,
            identity,
            cfg,
            Slots::Owned(Vec::with_capacity(K)),
        ));
        ep.fresh = Some(Fresh::new(pool_chunks));
        ep
    }

    /// Take the boxes of handshake machines from `machines`, a pool other endpoints may share, instead of a pool of
    /// this endpoint's own. A machine is held only while its handshake runs, so endpoints that share a pool hold as many
    /// as run at once, not one each. Affects only the slots made after the call.
    pub fn share_machines(&mut self, machines: &pinc_transport::conn::Machines) {
        if let Some(f) = self.fresh.as_mut() {
            f.machines = machines.clone();
        }
    }
}

/// What an endpoint that owns its table makes a slot's memory from, the first time the slot is taken.
#[cfg(feature = "alloc")]
pub(crate) struct Fresh {
    pool_chunks: usize,
    loss: alloc::rc::Rc<pinc_transport::recovery::LossEstimate>,
    machines: pinc_transport::conn::Machines,
    /// The pool a new stream table is made against; [`Endpoint::alloc_slot`] ties the table to the slot's own.
    probe: pinc_transport::stream::pool::BufferPool<'static>,
}

#[cfg(feature = "alloc")]
impl Fresh {
    fn new(pool_chunks: usize) -> Self {
        Self {
            pool_chunks,
            loss: alloc::rc::Rc::new(pinc_transport::recovery::LossEstimate::new()),
            machines: pinc_transport::conn::Machines::new(),
            probe: pinc_transport::stream::pool::BufferPool::new_boxed(1),
        }
    }

    /// The memory of one slot: its buffer pool, its stream table and its tables, none of which holds more than the
    /// slot's sessions come to use.
    fn memory<'m, S: StreamSource, const N: usize, const C: usize, const F: usize>(&self) -> Resources<'m, S, N, C, F> {
        use pinc_transport::conn::{Held, Shared, Tables};
        use pinc_transport::stream::Streams;
        use pinc_transport::stream::pool::BufferPool;

        Resources {
            pool: BufferPool::new_grown(self.pool_chunks),
            streams: Held::Owned(alloc::boxed::Box::new(Streams::new(
                &stream::Config::new(false),
                &self.probe,
            ))),
            loss: Shared::Counted(alloc::rc::Rc::clone(&self.loss)),
            tables: Tables::sharing(&self.machines),
        }
    }
}

/// The environment a connection call needs, borrowing only the provider and the generator.
macro_rules! env {
    ($s:ident, $now:expr) => {
        ::pinc_security::Env {
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
        cfg: EndpointConfig,
        slots: &'s mut [Slot<'a, P, S, N, C, F, NP>; K],
    ) -> Self {
        Self::with_slots(now, provider, drbg, identity, cfg, Slots::Borrowed(slots))
    }

    #[allow(clippy::large_types_passed_by_value, reason = "moved once into the endpoint, as `new` takes it")]
    fn with_slots(
        now: u64,
        provider: P,
        drbg: Drbg,
        identity: LocalIdentity,
        mut cfg: EndpointConfig,
        mut slots: Slots<'s, Slot<'a, P, S, N, C, F, NP>, K>,
    ) -> Self {
        cfg.conn.cid_len = CID_LEN;
        let seed = cfg.seed;
        let last = slots.len().saturating_sub(1);
        for (i, s) in slots.iter_mut().enumerate() {
            s.m.next_free = if i < last { u32::try_from(i + 1).unwrap_or(NIL) } else { NIL };
        }
        let free = if slots.is_empty() { NIL } else { 0 };
        Self {
            provider,
            drbg,
            identity,
            prekey: None,
            cfg,
            alpns: [None; MAX_ALPNS],
            slots,
            #[cfg(feature = "alloc")]
            fresh: None,
            free,
            live: 0,
            half_open: 0,
            demux: Table::new(seed ^ 0x01),
            by_peer: Table::new(seed ^ 0x02),
            by_route: Table::new(seed ^ 0x0C),
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
            parked: filled(0),
            is_parked: filled(false),
            parked_len: 0,
            last_now: now,
            reach_in: crate::reach::ReachRing::new(),
            ext_in: crate::ext_in::ExtRing::new(),
            capture: None,
            scratch: [0; MAX_DATAGRAM],
            orphans: crate::orphan::Orphans::new(),
            stash: [0; MAX_DATAGRAM],
            stash_meta: None,
            udp_heard: None,
            backlog_room: usize::MAX,
            owed: 0,
            rx_held: false,
            started: now,
            t_first: None,
            quiet_until: 0,
            suspended: false,
            moved: false,
            dark: false,
            rejoin_sent: Table::new(seed ^ 0x0B),
            counters: Counters::default(),
            trace: TraceLog::new(),
            rejects: crate::stateless::Rejects::new(),
        }
    }

    /// End the endpoint and give its connection table back with every session closed and every slot's memory
    /// returned, so another endpoint can run in the same memory. `None` when a failed construction took a slot's
    /// memory for good (see [`Endpoint::retired_slots`]): the table is then not whole and must not be reused. `None`
    /// also for an endpoint that owns its table ([`Endpoint::new_owned`]): there is nothing to give back, and dropping
    /// the endpoint frees it.
    pub fn into_slots(mut self) -> Option<&'s mut [Slot<'a, P, S, N, C, F, NP>; K]> {
        let now = self.last_now;
        for i in 0..K {
            self.free_slot(i, now);
        }
        if !self.slots.iter().all(|s| s.mem.is_some()) {
            return None;
        }
        match self.slots {
            Slots::Borrowed(table) => Some(table),
            #[cfg(feature = "alloc")]
            Slots::Owned(_) => None,
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
            dropped_out: self.counters.dropped_out,
            reach_dropped: self.counters.reach_dropped,
            ext_dropped: self.counters.ext_dropped,
            held_by_ledger: self.counters.held_by_ledger,
            stalled_in: self.counters.stalled_in,
            backlog_refused: self.counters.backlog_refused,
            holders_refused: self.counters.holders_refused,
            first_too_short: self.counters.first_too_short,
            stateless_rejects: self.counters.stateless_rejects,
            stateless_refused: self.counters.stateless_refused,
            events_queued: self.events.len(),
            events_dropped: self.events.dropped,
            events_lost: self.events.lost,
            fragments_held: self.orphans.counts.held,
            fragments_replayed: self.orphans.counts.replayed,
            fragments_expired: self.orphans.counts.expired,
            fragments_evicted: self.orphans.counts.evicted,
            fragments_waiting: self.orphans.waiting(),
            owed: self.owed,
        }
    }

    /// Slots a failed construction retired for good.
    pub const fn retired_slots(&self) -> u64 {
        self.counters.retired
    }

    /// Slots that hold memory, in use or free. For an endpoint that owns its table ([`Endpoint::new_owned`]) this is
    /// the most sessions it has had at once; for one given its table it is every slot not retired.
    pub fn backed_slots(&self) -> usize {
        self.slots.iter().filter(|s| s.mem.is_some() || s.conn.is_some()).count()
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
        if self.parked_len > 0 && !self.events.stalled() {
            self.resume_parked(self.last_now);
        }
        ev
    }

    /// Whether [`poll_event`](Self::poll_event) has an event to give, or work it holds back until events are read.
    pub const fn events_waiting(&self) -> bool {
        !self.events.is_empty() || self.parked_len > 0
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
            return path_id_at(generation, i);
        }
        let generation = self.next_path_gen;
        self.next_path_gen = self.next_path_gen.wrapping_add(1).max(1);
        self.paths.insert(key, generation);
        let i = self.paths.index_of(&key).unwrap_or(0);
        path_id_at(generation, i)
    }

    /// The addresses a path id names.
    pub(crate) fn path_addrs(&self, id: PathId) -> Option<(SocketAddr, SocketAddr)> {
        let i = usize::try_from(id.0 & 0xFFFF_FFFF).ok()?;
        let (key, generation) = self.paths.at_index(i)?;
        (u64::from(*generation) == id.0 >> 32).then_some(*key)
    }

    // ---- the slot table ----

    /// Take a free slot for a new session and prepare its memory for `client`'s role.
    pub(crate) fn alloc_slot(&mut self, client: bool, now: u64) -> Option<(usize, Resources<'a, S, N, C, F>)> {
        // An endpoint that owns its table adds a slot when every one it has is taken.
        #[cfg(feature = "alloc")]
        if self.free == NIL
            && self.fresh.is_some()
            && let Slots::Owned(v) = &mut self.slots
            && v.len() < K
            && let Ok(i) = u32::try_from(v.len())
        {
            v.push(Slot::unbacked());
            self.free = i;
        }
        let i = self.free as usize;
        let slot = self.slots.get_mut(i)?;
        let mut mem = match slot.mem.take() {
            Some(m) => m,
            #[cfg(feature = "alloc")]
            None => self.fresh.as_ref()?.memory(),
            #[cfg(not(feature = "alloc"))]
            None => return None,
        };
        self.free = slot.m.next_free;
        mem.pool.reset();
        mem.streams.reinit(&stream::Config::new(client), &mem.pool);
        mem.tables.clear();
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
        // A connection may hold an id twice: the table gets one entry per copy, so a copy that leaves takes its own.
        let (gone, added) = cid_delta(&slot.m.cids, &new);
        for old in gone.iter().flatten() {
            self.demux.remove_pair(old, &idx);
        }
        for n in added.iter().flatten() {
            self.demux.insert_dup(*n, idx);
        }
        slot.m.cids = new;
        slot.m.cid_epoch = epoch;
    }

    /// The remote address of session `i`'s active path, when the session is live and that path is validated and
    /// direct: the address a datagram of the session proves the peer is at.
    pub(crate) fn direct_remote(&self, i: usize) -> Option<SocketAddr> {
        let slot = self.slots.get(i).filter(|s| s.m.in_use)?;
        let conn = slot.conn.as_ref()?;
        let path = conn.active_path()?;
        let (_, remote) = self.path_addrs(path)?;
        (conn.path_validated(path) && !crate::relay_net::is_relay_addr(&remote)).then_some(remote)
    }

    /// Bring the table of sessions by address in line with session `i`'s path. A refused entry (the table holds one
    /// per slot, so only a table smaller than the slots refuses) leaves the session out, and the next settle tries
    /// again.
    pub(crate) fn sync_route(&mut self, i: usize) {
        let want = self.direct_remote(i);
        let Ok(idx) = u32::try_from(i) else { return };
        let Some(slot) = self.slots.get_mut(i) else { return };
        if slot.m.route == want {
            return;
        }
        if let Some(old) = slot.m.route.take() {
            self.by_route.remove_pair(&old, &idx);
        }
        slot.m.route = want.filter(|a| self.by_route.insert_dup(*a, idx));
    }

    /// The live session with a validated direct path from `remote` that `keep` accepts, the lowest session id of
    /// those: who a datagram from `remote` came from. It costs the entries of one chain of the table, not a walk of
    /// the sessions.
    pub fn session_from(&self, remote: &SocketAddr, keep: impl Fn(SessionId) -> bool) -> Option<SessionId> {
        self.by_route
            .holders(remote)
            .filter(|i| self.direct_remote(*i as usize).as_ref() == Some(remote))
            .map(|i| self.session_id(i as usize))
            .filter(|s| keep(*s))
            .min()
    }

    /// End session `i`: unregister it, return its memory to the slot and put the slot on the free list.
    // Out of line: it moves a whole connection (a value of over a hundred kilobytes); a caller that inlined it would
    // reserve and probe that much stack on every call, on its hot path too. The same holds where a connection is built.
    #[inline(never)]
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
        if let Some(a) = slot.m.route.take() {
            self.by_route.remove_pair(&a, &idx);
        }
        if slot.m.half_open {
            self.half_open = self.half_open.saturating_sub(1);
            slot.m.half_open = false;
        }
        if slot.m.owed {
            self.owed = self.owed.saturating_sub(1);
            slot.m.owed = false;
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
    /// others. `now` stamps the trace record.
    pub(crate) fn mark_dirty(&mut self, i: usize, now: u64) {
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
        crate::trace::trace!(self, now, TxMark { slot: i as u64, queue: q as u64 });
    }
}
