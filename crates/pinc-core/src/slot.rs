//! One entry of the connection table: the connection (or the memory waiting for the next one) and what the endpoint
//! knows about the session around it.
//!
//! Invariants: exactly one of `conn` and `mem` holds a value at any time, so a slot's memory is never lost and never
//! used by two connections; `gen` grows each time the slot starts a new session, so a [`SessionId`] names one
//! session only; the held events of a session are released in the order they arrived; the held ring never drops an
//! event the application cannot recover by reading state (a stream opened, a stream reset, a datagram): when the ring
//! holds nothing but those, the session is stalled and the endpoint reads no more from it until the ring drains.

use pinc_crypto::{NodeId, Provider};
use pinc_security::{Alpn, ConnId};
#[cfg(feature = "trace")]
use pinc_transport::conn::handshake_limit;
use pinc_transport::conn::{Connection, PathId, Resources, handshake_end};
use pinc_transport::stream::StreamSource;

use crate::api::{Event, SessionId};
use crate::keepalive::{Plan, Role};

/// Most connection ids one session registers: the first, the derived window and the id the dialer invented.
pub(crate) const MAX_CIDS: usize = 10;
/// The connection ids a session gave up and the ones it gained when its list goes from `old` to `new`, as a multiset
/// difference: an id held twice is listed twice, so the table gets one entry per copy.
pub(crate) fn cid_delta(
    old: &[Option<ConnId>; MAX_CIDS],
    new: &[Option<ConnId>; MAX_CIDS],
) -> ([Option<ConnId>; MAX_CIDS], [Option<ConnId>; MAX_CIDS]) {
    let mut gone = *old;
    let mut added = [None; MAX_CIDS];
    for (a, n) in added.iter_mut().zip(new.iter().flatten()) {
        match gone.iter_mut().find(|o| **o == Some(*n)) {
            Some(o) => *o = None,
            None => *a = Some(*n),
        }
    }
    (gone, added)
}

/// The most application events held back for the access check.
pub const HELD_EVENTS: usize = 64;
pub(crate) const NIL: u32 = u32::MAX;

/// Where the session is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum State {
    /// The handshake runs.
    Handshaking,
    /// The peer is authenticated.
    Established,
    /// The connection ended and the slot waits to be freed.
    Closing,
}

/// A held application event in compact form.
#[derive(Debug, Clone, Copy)]
pub(crate) struct HeldEvent {
    pub(crate) kind: u8,
    pub(crate) stream: u64,
    pub(crate) error: u64,
}

impl HeldEvent {
    pub(crate) const OPENED: u8 = 0;
    pub(crate) const READABLE: u8 = 1;
    pub(crate) const WRITABLE: u8 = 2;
    pub(crate) const RESET: u8 = 3;
    pub(crate) const DATAGRAM: u8 = 4;
    pub(crate) const STOPPED: u8 = 5;
    pub(crate) const OPEN_READY: u8 = 6;

    pub(crate) const fn of(ev: &Event) -> Option<Self> {
        let (kind, stream, error) = match *ev {
            Event::StreamOpened { stream, .. } => (Self::OPENED, stream, 0),
            Event::StreamReadable { stream, .. } => (Self::READABLE, stream, 0),
            Event::StreamWritable { stream, .. } => (Self::WRITABLE, stream, 0),
            Event::StreamReset { stream, error, .. } => (Self::RESET, stream, error),
            Event::StreamStopped { stream, error, .. } => (Self::STOPPED, stream, error),
            Event::OpenReady { .. } => (Self::OPEN_READY, 0, 0),
            Event::DatagramReceived { .. } => (Self::DATAGRAM, 0, 0),
            _ => return None,
        };
        Some(Self { kind, stream, error })
    }

    pub(crate) const fn event(&self, session: SessionId) -> Event {
        let stream = self.stream;
        match self.kind {
            Self::OPENED => Event::StreamOpened { session, stream },
            Self::READABLE => Event::StreamReadable { session, stream },
            Self::WRITABLE => Event::StreamWritable { session, stream },
            Self::OPEN_READY => Event::OpenReady { session },
            Self::RESET => Event::StreamReset {
                session,
                stream,
                error: self.error,
            },
            Self::STOPPED => Event::StreamStopped {
                session,
                stream,
                error: self.error,
            },
            _ => Event::DatagramReceived { session },
        }
    }

    /// Whether reading state tells the application what the event did, so a full ring may drop it.
    pub(crate) const fn lossy(&self) -> bool {
        matches!(self.kind, Self::READABLE | Self::WRITABLE | Self::OPEN_READY)
    }
}

/// The application events of a session waiting for its access check.
#[derive(Debug)]
pub(crate) struct Held {
    items: [Option<HeldEvent>; HELD_EVENTS],
    head: usize,
    len: usize,
    pub(crate) dropped: u64,
}

impl Held {
    pub(crate) const EMPTY: Self = Self {
        items: [None; HELD_EVENTS],
        head: 0,
        len: 0,
        dropped: 0,
    };

    pub(crate) const fn len(&self) -> usize {
        self.len
    }

    fn at(&self, i: usize) -> usize {
        (self.head + i) % HELD_EVENTS
    }

    /// Whether the ring holds nothing it may drop: it is full of events the application cannot recover. The endpoint
    /// reads no more events from the session while this is true, so [`push`](Self::push) always finds room.
    pub(crate) fn stalled(&self) -> bool {
        self.len == HELD_EVENTS && self.first_lossy().is_none()
    }

    /// The place, counting from the oldest, of the oldest event the application can recover.
    fn first_lossy(&self) -> Option<usize> {
        (0..self.len).find(|i| {
            self.items
                .get(self.at(*i))
                .copied()
                .flatten()
                .is_some_and(|h| h.lossy())
        })
    }

    /// Hold an event. A repeated read or write notification for the same stream merges; when full, the oldest such
    /// notification goes first. An event that cannot be recovered is never evicted: with none to evict the new event
    /// is refused and counted (the endpoint prevents this by checking [`stalled`](Self::stalled) first).
    pub(crate) fn push(&mut self, ev: HeldEvent) {
        if ev.lossy()
            && (0..self.len).any(|i| {
                self.items
                    .get(self.at(i))
                    .copied()
                    .flatten()
                    .is_some_and(|h| h.kind == ev.kind && h.stream == ev.stream)
            })
        {
            return;
        }
        if self.len == HELD_EVENTS {
            let Some(victim) = self.first_lossy() else {
                self.dropped += 1;
                return;
            };
            // Close the gap at `victim` by moving the older entries up one place.
            for i in (0..victim).rev() {
                let (from, to) = (self.at(i), self.at(i + 1));
                let moved = self.items.get(from).copied().flatten();
                if let Some(s) = self.items.get_mut(to) {
                    *s = moved;
                }
            }
            self.head = (self.head + 1) % HELD_EVENTS;
            self.len -= 1;
            self.dropped += 1;
        }
        let at = self.at(self.len);
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(ev);
            self.len += 1;
        }
    }

    pub(crate) fn pop(&mut self) -> Option<HeldEvent> {
        if self.len == 0 {
            return None;
        }
        let e = self.items.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % HELD_EVENTS;
        self.len -= 1;
        e
    }

    pub(crate) fn clear(&mut self) {
        while self.pop().is_some() {}
    }
}

/// When the endpoint last sent and heard on one path of a session.
#[derive(Debug, Clone, Copy)]
pub(crate) struct PathStamp {
    pub(crate) id: PathId,
    pub(crate) tx: u64,
    pub(crate) rx: u64,
}

/// What the endpoint knows about a session.
#[derive(Debug)]
pub(crate) struct Meta<const NP: usize> {
    pub(crate) generation: u32,
    pub(crate) in_use: bool,
    pub(crate) next_free: u32,
    /// 0 not queued for sending, else the queue (1 normal, 2 broadcast).
    pub(crate) dirty: u8,
    pub(crate) dirty_next: u32,
    pub(crate) peer: Option<NodeId>,
    pub(crate) alpn: Option<Alpn>,
    /// The next session of the same peer.
    pub(crate) peer_next: u32,
    pub(crate) client: bool,
    pub(crate) state: State,
    pub(crate) role: Role,
    /// The connectivity layer sends this session's keepalive (`CARRIER_PULSE`), and one is due now.
    pub(crate) pulse: bool,
    pub(crate) pulse_due: bool,
    pub(crate) gossip: bool,
    /// A sub-session open is queued in this session and has not left yet.
    pub(crate) ctrl_pending: bool,
    pub(crate) created: u64,
    /// Counted against the half-open cap.
    pub(crate) half_open: bool,
    /// A server session whose peer is not authenticated yet.
    pub(crate) unauth: bool,
    /// A server session the host has not taken yet (`Endpoint::session_taken`), counted in `Endpoint::owed`.
    pub(crate) owed: bool,
    pub(crate) allowed: bool,
    pub(crate) optimistic: bool,
    /// 0 none, 1 waiting for the access check and READY, 2 allowed and waiting for READY, 3 READY seen and waiting
    /// for the access check.
    pub(crate) hold: u8,
    /// Whether the application was told this session exists.
    pub(crate) announced: bool,
    /// The peer was heard since the application was told of the session, or before.
    pub(crate) answered: bool,
    /// The application is still to be told so: `drain` raises the event once the event queue has room.
    pub(crate) answer_due: bool,
    pub(crate) resumed: bool,
    pub(crate) parent: Option<SessionId>,
    pub(crate) has_sub: bool,
    pub(crate) last_tx: u64,
    pub(crate) last_rx: u64,
    pub(crate) last_app: u64,
    pub(crate) paths: [Option<PathStamp>; NP],
    pub(crate) cids: [Option<ConnId>; MAX_CIDS],
    pub(crate) cid_epoch: u64,
    pub(crate) odcid: Option<ConnId>,
    pub(crate) held: Held,
    pub(crate) seen_peak: u64,
    pub(crate) plan: Plan,
    /// Whether the session was woken by suspension while timing out.
    pub(crate) sleep_doubt: bool,
    pub(crate) acp_recheck: Option<u64>,
    /// The node round trip version last handed to the connection.
    pub(crate) node_ver: u64,
    /// The access check denied the session.
    pub(crate) denied: bool,
    /// The session was closed because its parent closed before the peer was heard.
    pub(crate) orphaned: bool,
    /// The session was closed so the application dials again.
    pub(crate) redial: bool,
    /// This is a sub-session.
    pub(crate) sub: bool,
    /// This sub-session waits for its parent's handshake to finish before it has keys.
    pub(crate) waiting: bool,
    /// The two connection ids of a waiting sub-session (the dialer's, then the accepting side's).
    pub(crate) sub_ids: Option<(ConnId, ConnId)>,
    /// The session is in its peer's list.
    pub(crate) linked: bool,
    /// The address this session holds in the endpoint's table of sessions by address, if any.
    pub(crate) route: Option<core::net::SocketAddr>,
    /// Close with this code once everything queued has left (a dialer's Finish goes out before its deny).
    pub(crate) deferred_close: Option<u64>,
}

impl<const NP: usize> Meta<NP> {
    /// The send queue this session belongs in: 1 for a broadcast session without a sub-session open still to leave,
    /// 0 for the others.
    pub(crate) const fn send_queue(&self) -> usize {
        if self.gossip && !self.ctrl_pending { 1 } else { 0 }
    }

    pub(crate) const EMPTY: Self = Self {
        generation: 0,
        in_use: false,
        next_free: NIL,
        dirty: 0,
        dirty_next: NIL,
        peer: None,
        alpn: None,
        peer_next: NIL,
        client: false,
        state: State::Handshaking,
        role: Role::Other,
        pulse: false,
        pulse_due: false,
        gossip: false,
        ctrl_pending: false,
        created: 0,
        half_open: false,
        unauth: false,
        owed: false,
        allowed: false,
        optimistic: false,
        hold: 0,
        announced: false,
        answered: false,
        answer_due: false,
        resumed: false,
        parent: None,
        has_sub: false,
        last_tx: 0,
        last_rx: 0,
        last_app: 0,
        paths: [None; NP],
        cids: [None; MAX_CIDS],
        cid_epoch: u64::MAX,
        odcid: None,
        held: Held::EMPTY,
        seen_peak: 0,
        plan: Plan {
            ping_at: None,
            review_at: None,
        },
        sleep_doubt: false,
        acp_recheck: None,
        node_ver: 0,
        denied: false,
        orphaned: false,
        redial: false,
        sub: false,
        waiting: false,
        sub_ids: None,
        linked: false,
        route: None,
        deferred_close: None,
    };

    /// Reset for a new session, keeping the table bookkeeping (generation, list links).
    pub(crate) fn begin(&mut self, client: bool, now: u64) {
        let keep = (
            self.generation.wrapping_add(1),
            self.next_free,
            self.dirty,
            self.dirty_next,
        );
        *self = Self::EMPTY;
        (self.generation, self.next_free, self.dirty, self.dirty_next) = keep;
        self.in_use = true;
        self.client = client;
        self.created = now;
        self.last_tx = now;
        self.last_rx = now;
        self.last_app = now;
    }

    /// When the endpoint last sent on path `id`, 0 for never: a path added to the session has no stamp until something
    /// leaves on it.
    pub(crate) fn path_tx(&self, id: PathId) -> u64 {
        self.paths.iter().flatten().find(|p| p.id == id).map_or(0, |p| p.tx)
    }

    pub(crate) fn stamp(&mut self, id: PathId) -> Option<&mut PathStamp> {
        let i = self
            .paths
            .iter()
            .position(|p| p.is_some_and(|p| p.id == id))
            .or_else(|| {
                let free = self.paths.iter().position(Option::is_none);
                free.or_else(|| {
                    self.paths
                        .iter()
                        .enumerate()
                        .filter_map(|(i, p)| p.map(|p| (p.tx.max(p.rx), i)))
                        .min()
                        .map(|(_, i)| i)
                })
                .inspect(|i| {
                    if let Some(s) = self.paths.get_mut(*i) {
                        *s = Some(PathStamp { id, tx: 0, rx: 0 });
                    }
                })
            })?;
        self.paths.get_mut(i)?.as_mut()
    }
}

/// One entry of the connection table. Build one per connection the endpoint may hold, each with its own memory.
pub struct Slot<'a, P: Provider, S: StreamSource, const N: usize, const C: usize, const F: usize, const NP: usize> {
    pub(crate) conn: Option<Connection<'a, P, S, N, C, F, NP>>,
    pub(crate) mem: Option<Resources<'a, S, N, C, F>>,
    pub(crate) m: Meta<NP>,
}

impl<'a, P: Provider, S: StreamSource, const N: usize, const C: usize, const F: usize, const NP: usize>
    Slot<'a, P, S, N, C, F, NP>
{
    /// A free slot that will run its connections in `memory`.
    pub fn new(memory: Resources<'a, S, N, C, F>) -> Self {
        Self {
            conn: None,
            mem: Some(memory),
            m: Meta::EMPTY,
        }
    }

    /// A free slot, the last of its free list, whose memory the endpoint makes when the slot is first taken.
    #[cfg(feature = "alloc")]
    pub(crate) const fn unbacked() -> Self {
        Self {
            conn: None,
            mem: None,
            m: Meta::EMPTY,
        }
    }

    /// How long the session lives while its peer is not authenticated: the node's connect limit (30 s, 60 s on a thin
    /// node), and at least [`HALF_OPEN_HOLD`](crate::HALF_OPEN_HOLD) once it answered as a responder (its flight went
    /// out, a reject is not one).
    #[cfg(feature = "trace")]
    pub(crate) fn half_open_life(&self, thin: bool) -> u64 {
        handshake_limit(thin, self.conn.as_ref().is_some_and(Connection::answered))
    }

    /// The first instant at which the session, still unauthenticated, has outlived its life: it is there at
    /// `created + life` and gone one tick past it, the transport's own rule (`handshake_end`), which the connection's
    /// deadline asks too.
    pub(crate) fn half_open_end(&self, thin: bool) -> u64 {
        handshake_end(
            self.m.created,
            thin,
            self.conn.as_ref().is_some_and(Connection::answered),
        )
    }
}

impl<P: Provider, S: StreamSource, const N: usize, const C: usize, const F: usize, const NP: usize> core::fmt::Debug
    for Slot<'_, P, S, N, C, F, NP>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Slot")
            .field("in_use", &self.m.in_use)
            .field("generation", &self.m.generation)
            .finish_non_exhaustive()
    }
}

/// Test-only driver of the held ring, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
pub(crate) mod trace {
    use super::{HELD_EVENTS, Held, HeldEvent};

    /// A held event as the probe shows it: its kind, stream and error.
    type HeldView = (u8, u64, u64);

    /// A ring of held events of its own, with its state readable after every call.
    pub struct HeldProbe {
        h: Held,
    }

    impl Default for HeldProbe {
        fn default() -> Self {
            Self::new()
        }
    }

    impl HeldProbe {
        /// The places of the ring.
        pub const SLOTS: usize = HELD_EVENTS;
        /// The kinds of event, as the code numbers them: opened, readable, writable, reset, datagram, stopped,
        /// open ready.
        pub const KINDS: [u8; 7] = [
            HeldEvent::OPENED,
            HeldEvent::READABLE,
            HeldEvent::WRITABLE,
            HeldEvent::RESET,
            HeldEvent::DATAGRAM,
            HeldEvent::STOPPED,
            HeldEvent::OPEN_READY,
        ];

        /// An empty ring.
        #[must_use]
        pub const fn new() -> Self {
            Self { h: Held::EMPTY }
        }

        /// Hold an event.
        pub fn push(&mut self, kind: u8, stream: u64, error: u64) {
            self.h.push(HeldEvent { kind, stream, error });
        }

        /// The oldest held event.
        pub fn pop(&mut self) -> Option<HeldView> {
            self.h.pop().map(|e| (e.kind, e.stream, e.error))
        }

        /// Release every held event.
        pub fn clear(&mut self) {
            self.h.clear();
        }

        /// Whether the ring is full of events the application cannot recover.
        #[must_use]
        pub fn stalled(&self) -> bool {
            self.h.stalled()
        }

        /// Whether the application can recover an event of this kind by reading state.
        #[must_use]
        pub const fn lossy(kind: u8) -> bool {
            HeldEvent {
                kind,
                stream: 0,
                error: 0,
            }
            .lossy()
        }

        /// How many events are held.
        #[must_use]
        pub const fn len(&self) -> usize {
            self.h.len
        }

        /// Whether no event is held.
        #[must_use]
        pub const fn is_empty(&self) -> bool {
            self.h.len == 0
        }

        /// The place of the oldest held event.
        #[must_use]
        pub const fn head(&self) -> usize {
            self.h.head
        }

        /// How many events the ring dropped.
        #[must_use]
        pub const fn dropped(&self) -> u64 {
            self.h.dropped
        }

        /// The `i`th held event, counting from the oldest.
        #[must_use]
        pub fn slot(&self, i: usize) -> Option<HeldView> {
            if i >= self.h.len {
                return None;
            }
            self.h
                .items
                .get(self.h.at(i))
                .copied()
                .flatten()
                .map(|e| (e.kind, e.stream, e.error))
        }

        /// The cell at place `p`, whatever the window: for the shift an eviction makes.
        #[must_use]
        pub fn cell(&self, p: usize) -> Option<HeldView> {
            self.h
                .items
                .get(p)
                .copied()
                .flatten()
                .map(|e| (e.kind, e.stream, e.error))
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::VecDeque;
    use std::vec::Vec;

    use proptest::prelude::*;

    use super::*;

    type Key = (u8, u64, u64);

    fn key(e: &HeldEvent) -> Key {
        (e.kind, e.stream, e.error)
    }

    /// What the endpoint does around the ring: it feeds a held event only while the ring is not stalled, and leaves
    /// the rest in the connection, in order, until the host drains.
    struct Sim {
        held: Held,
        waiting: VecDeque<HeldEvent>,
        offered: Vec<Key>,
        delivered: Vec<Key>,
        lossy_offered: usize,
    }

    impl Sim {
        fn feed(&mut self) {
            while !self.held.stalled() {
                let Some(ev) = self.waiting.pop_front() else { break };
                self.held.push(ev);
                assert!(self.held.len() <= HELD_EVENTS);
            }
        }

        fn offer(&mut self, ev: HeldEvent) {
            if ev.lossy() {
                self.lossy_offered += 1;
            } else {
                self.offered.push(key(&ev));
            }
            self.waiting.push_back(ev);
            self.feed();
        }

        fn take(&mut self) -> bool {
            let Some(e) = self.held.pop() else { return false };
            if !e.lossy() {
                self.delivered.push(key(&e));
            }
            self.feed();
            true
        }
    }

    #[derive(Debug, Clone)]
    enum Op {
        Offer(u8, u64, u64),
        Take,
    }

    fn ops() -> impl Strategy<Value = Vec<Op>> {
        prop::collection::vec(
            prop_oneof![
                6 => (0..5u8, 0..6u64, 0..4u64).prop_map(|(k, s, e)| Op::Offer(k, s, e)),
                1 => Just(Op::Take),
            ],
            0..600,
        )
    }

    proptest! {
        #[test]
        fn nothing_that_cannot_be_recovered_is_dropped(ops in ops()) {
            let mut sim = Sim {
                held: Held::EMPTY,
                waiting: VecDeque::new(),
                offered: Vec::new(),
                delivered: Vec::new(),
                lossy_offered: 0,
            };
            for op in ops {
                match op {
                    Op::Offer(kind, stream, error) => {
                        let (stream, error) = if kind == HeldEvent::DATAGRAM { (0, 0) } else { (stream, error) };
                        let error = if kind == HeldEvent::RESET { error } else { 0 };
                        sim.offer(HeldEvent { kind, stream, error });
                    }
                    Op::Take => {
                        sim.take();
                    }
                }
            }
            while sim.take() || !sim.waiting.is_empty() {}
            prop_assert_eq!(&sim.delivered, &sim.offered, "an event that cannot be recovered was lost or reordered");
            prop_assert!(sim.held.dropped as usize <= sim.lossy_offered, "a drop was counted for more than the lossy events");
        }
    }

    #[test]
    fn a_ring_full_of_unrecoverable_events_stalls_instead_of_dropping() {
        let mut h = Held::EMPTY;
        for i in 0..HELD_EVENTS as u64 {
            assert!(!h.stalled());
            h.push(HeldEvent {
                kind: HeldEvent::OPENED,
                stream: i,
                error: 0,
            });
        }
        assert!(h.stalled());
        // A recoverable notification is the only thing a full ring gives up.
        let mut h = Held::EMPTY;
        h.push(HeldEvent {
            kind: HeldEvent::READABLE,
            stream: 1,
            error: 0,
        });
        for _ in 1..HELD_EVENTS {
            h.push(HeldEvent {
                kind: HeldEvent::DATAGRAM,
                stream: 0,
                error: 0,
            });
        }
        assert!(!h.stalled());
        h.push(HeldEvent {
            kind: HeldEvent::RESET,
            stream: 2,
            error: 9,
        });
        assert_eq!((h.len(), h.dropped), (HELD_EVENTS, 1));
        assert!(h.stalled());
        let kinds: Vec<u8> = std::iter::from_fn(|| h.pop()).map(|e| e.kind).collect();
        assert!(!kinds.contains(&HeldEvent::READABLE));
        assert_eq!(
            kinds
                .iter()
                .map(|k| usize::from(*k == HeldEvent::DATAGRAM))
                .sum::<usize>(),
            HELD_EVENTS - 1
        );
        assert_eq!(kinds.last(), Some(&HeldEvent::RESET));
    }

    #[test]
    fn a_connection_id_held_twice_has_two_entries_and_leaves_one_at_a_time() {
        let id = |b: u8| ConnId::new(&[b; 4]);
        let list = |v: &[u8]| {
            let mut l = [None; MAX_CIDS];
            for (d, b) in l.iter_mut().zip(v) {
                *d = id(*b);
            }
            l
        };
        let count = |l: &[Option<ConnId>; MAX_CIDS], b: u8| l.iter().filter(|x| **x == id(b)).count();
        let (gone, added) = cid_delta(&list(&[1]), &list(&[1, 2, 2]));
        assert_eq!((count(&gone, 1), count(&added, 2), count(&added, 1)), (0, 2, 0));
        let (gone, added) = cid_delta(&list(&[1, 2, 2]), &list(&[1, 2]));
        assert_eq!((count(&gone, 2), count(&added, 2)), (1, 0));
        let (gone, added) = cid_delta(&list(&[1, 2]), &list(&[]));
        assert_eq!(
            (count(&gone, 1), count(&gone, 2), added.iter().flatten().count()),
            (1, 1, 0)
        );
    }
}
