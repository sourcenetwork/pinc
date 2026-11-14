//! The node's session state and everything the layers ask of it: the hub streams, the frames queued for a dial, the
//! evidence the transport gives, the dial backoff and the application event queue.
//!
//! One hub stream per peer, found by the protocol id the node registered. The dialer opens a bidirectional stream
//! when its session is up; the acceptor writes on the stream the dialer opened. A second stream per hub carries the
//! copies a publisher fans to hubs that are not its primary.
//!
//! Invariants: every table is bounded by [`TABLE_MAX`] and a full table refuses the new entry; bytes written to a
//! stream keep their order (a write behind pending bytes joins them); the bytes pending on a stream never exceed the
//! out cap; a frame that cannot be handed to a session reports `false` and is never retried here.

use alloc::collections::{BTreeMap, BTreeSet, VecDeque};
use alloc::vec::Vec;

use vinc_broadcast::Lane;
use vinc_connect::ticket::MAX_LEN as TICKET_MAX;
use vinc_core::{
    Command, CommandError, Event, QUIET_KEEP_ACCEPTOR, QUIET_KEEP_DIALER, SessionId, Value, is_relay_addr,
};
use vinc_crypto::IdentityAlg;
use vinc_membership::NodeId;
use vinc_membership::session::{Carrier, CloseReason, DENIED_CODE, Evidence, LEAVE_CODE};
use vinc_transport::stream::{RecvStatus, StreamError, StreamId};

use crate::bound;
use crate::config::{
    BACKOFF_CAP, BACKOFF_FIRST, BACKOFF_HUB_CAP, DENY_CAP, DENY_FIRST, EVENT_CAP, EVENT_HIGH, EVENT_LOW,
    HUB_RESERVE_MAX, Nanos, QUEUE_FRAMES, Store, TABLE_MAX,
};
use crate::ep::Ep;
use crate::event::NodeEvent;
use crate::layer::{LSess, Layer};
use crate::trace::{Body, NodeTrace, TraceQueue, tag};

/// A session of the hub protocol.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Sess {
    pub(crate) peer: NodeId,
    /// The peer dialed us.
    pub(crate) incoming: bool,
}

/// The current session of a peer and its streams.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct Link {
    pub(crate) conn: Option<SessionId>,
    pub(crate) out: Option<StreamId>,
    pub(crate) fan: Option<StreamId>,
    pub(crate) opened: Nanos,
}

/// The bytes of one stream: received and not yet parsed, written and not yet accepted.
#[derive(Debug)]
pub(crate) struct Strm {
    pub(crate) inb: Vec<u8>,
    pub(crate) outb: Vec<u8>,
    pub(crate) off: usize,
    /// End the stream once `outb` is written.
    pub(crate) fin: bool,
}

impl Strm {
    fn pending(&self) -> usize {
        self.outb.len().saturating_sub(self.off)
    }
}

/// The bounded queue of application events.
///
/// The node takes events from the endpoint only while the queue has room ([`can_take`](Self::can_take)), so the
/// endpoint's own rule applies when the host reads slowly: it keeps the events the application cannot recover. A
/// full queue drops what the application can recover by reading state, and an event it cannot recover only when
/// nothing else is queued.
#[derive(Debug, Default)]
pub(crate) struct EventQueue {
    q: VecDeque<NodeEvent>,
    lost: u32,
    /// The node stopped taking events from the endpoint and has not resumed.
    held: bool,
}

/// Whether the application can recover the event by reading state.
fn lossy(e: &NodeEvent) -> bool {
    matches!(e, NodeEvent::Endpoint(e) if e.lossy())
}

impl EventQueue {
    fn with_capacity(n: usize) -> Self {
        Self {
            q: VecDeque::with_capacity(n),
            lost: 0,
            held: false,
        }
    }

    /// Whether the node may take another event from the endpoint: not from [`EVENT_HIGH`] queued events until the
    /// queue is back to [`EVENT_LOW`].
    pub(crate) fn can_take(&mut self) -> bool {
        self.held = if self.held {
            self.q.len() > EVENT_LOW
        } else {
            self.q.len() >= EVENT_HIGH
        };
        !self.held
    }

    /// Whether the node stopped taking events and the queue has since fallen to the point it resumes.
    pub(crate) fn resumable(&self) -> bool {
        self.held && self.q.len() <= EVENT_LOW
    }

    pub(crate) fn push(&mut self, e: NodeEvent) {
        if self.q.len() >= EVENT_CAP {
            self.lost = self.lost.saturating_add(1);
            if lossy(&e) {
                return;
            }
            // vertexia: a scan for the oldest recoverable event, only at a full queue, which the pause above makes rare;
            // a count of them would make it O(1) if a host runs there.
            let victim = self.q.iter().position(lossy).unwrap_or(0);
            self.q.remove(victim);
        }
        self.q.push_back(e);
    }

    pub(crate) fn pop(&mut self) -> Option<NodeEvent> {
        if self.lost > 0 {
            let count = core::mem::take(&mut self.lost);
            return Some(NodeEvent::Lost { count });
        }
        self.q.pop_front()
    }
}

/// The session state of a node, and the host the layers talk to.
pub(crate) struct Io<E: Ep, St: Store> {
    pub(crate) ep: E,
    pub(crate) store: St,
    pub(crate) me: NodeId,
    pub(crate) my_alg: IdentityAlg,
    pub(crate) is_hub: bool,
    pub(crate) alpn: &'static [u8],
    pub(crate) version: u16,
    pub(crate) now: Nanos,
    wall: (Nanos, u64),
    pub(crate) hubs: Vec<NodeId>,
    pub(crate) hub_alive: Vec<NodeId>,
    pub(crate) algs: BTreeMap<NodeId, IdentityAlg>,
    pub(crate) sess: BTreeMap<SessionId, Sess>,
    pub(crate) links: BTreeMap<NodeId, Link>,
    pub(crate) strm: BTreeMap<(SessionId, StreamId), Strm>,
    pub(crate) failed: BTreeMap<NodeId, (Nanos, Nanos)>,
    pub(crate) connecting: BTreeMap<NodeId, Nanos>,
    queue: BTreeMap<NodeId, (VecDeque<Vec<u8>>, usize)>,
    pub(crate) dials: Vec<NodeId>,
    pub(crate) probes: Vec<(NodeId, NodeId)>,
    pub(crate) carriers: BTreeMap<NodeId, Carrier>,
    /// Per session: the packet count at the last look and when it last changed.
    pub(crate) rx_seen: BTreeMap<SessionId, (u64, Nanos)>,
    pub(crate) rtts: BTreeMap<NodeId, (Nanos, bool)>,
    pub(crate) revoked: BTreeSet<NodeId>,
    /// The sessions of the layers above broadcast, by session.
    pub(crate) lsess: BTreeMap<SessionId, LSess>,
    /// The session this node dialed for a layer, by layer and peer.
    pub(crate) lout: BTreeMap<(Layer, NodeId), SessionId>,
    /// The dials of a layer in progress.
    pub(crate) lconn: BTreeSet<(Layer, NodeId)>,
    /// The dials the layers asked for and the node has not made yet.
    pub(crate) ldials: Vec<(Layer, NodeId)>,
    /// The dial backoff of a layer's peer: when the next dial may start, and the wait that was used.
    pub(crate) lfailed: BTreeMap<(Layer, NodeId), (Nanos, Nanos)>,
    /// The sessions of the hub protocol or of a layer that the node closed without recording, until their `Closed`
    /// arrives: the events of such a session still queued belong to no one.
    pub(crate) shed: BTreeSet<SessionId>,
    pub(crate) evq: VecDeque<Event>,
    pub(crate) members: VecDeque<crate::relay::MemberNotice>,
    pub(crate) out: EventQueue,
    pub(crate) tq: TraceQueue,
    pub(crate) ticket: [u8; TICKET_MAX],
    pub(crate) ticket_len: usize,
    pub(crate) reflexive: bool,
    pub(crate) max_frame: usize,
    out_cap: usize,
}

impl<E: Ep, St: Store> Io<E, St> {
    #[allow(
        clippy::too_many_arguments,
        reason = "the node builds its session state once, from its configuration"
    )]
    pub(crate) fn new(
        ep: E,
        store: St,
        me: NodeId,
        my_alg: IdentityAlg,
        is_hub: bool,
        alpn: &'static [u8],
        version: u16,
        now: Nanos,
        wall_ms: u64,
        hubs: Vec<NodeId>,
        algs: BTreeMap<NodeId, IdentityAlg>,
        max_frame: usize,
        trace: bool,
    ) -> Self {
        Self {
            ep,
            store,
            me,
            my_alg,
            is_hub,
            alpn,
            version,
            now,
            wall: (now, wall_ms),
            hub_alive: Vec::with_capacity(hubs.len()),
            hubs,
            algs,
            sess: BTreeMap::new(),
            links: BTreeMap::new(),
            strm: BTreeMap::new(),
            failed: BTreeMap::new(),
            connecting: BTreeMap::new(),
            queue: BTreeMap::new(),
            dials: Vec::with_capacity(16),
            probes: Vec::with_capacity(16),
            carriers: BTreeMap::new(),
            rx_seen: BTreeMap::new(),
            rtts: BTreeMap::new(),
            revoked: BTreeSet::new(),
            lsess: BTreeMap::new(),
            lout: BTreeMap::new(),
            lconn: BTreeSet::new(),
            ldials: Vec::new(),
            lfailed: BTreeMap::new(),
            shed: BTreeSet::new(),
            evq: VecDeque::with_capacity(64),
            members: VecDeque::new(),
            out: EventQueue::with_capacity(256),
            tq: TraceQueue::new(trace),
            ticket: [0; TICKET_MAX],
            ticket_len: 0,
            reflexive: false,
            max_frame,
            out_cap: max_frame.saturating_mul(2).max(1 << 20),
        }
    }

    /// The wall clock in milliseconds at the node's current time.
    pub(crate) fn wall_ms(&self) -> u64 {
        self.wall
            .1
            .saturating_add(self.now.saturating_sub(self.wall.0) / 1_000_000)
    }

    /// The host reports the wall clock.
    pub(crate) fn set_wall(&mut self, wall_ms: u64) {
        self.wall = (self.now, wall_ms);
    }

    /// Queue a notice for the hub's relay; a full queue drops the oldest.
    pub(crate) fn notice(&mut self, n: crate::relay::MemberNotice) {
        if self.members.len() >= TABLE_MAX {
            self.members.pop_front();
        }
        self.members.push_back(n);
    }

    pub(crate) fn emit(&mut self, e: NodeEvent) {
        self.out.push(e);
    }

    pub(crate) fn trace(&mut self, t: NodeTrace) {
        let now = self.now;
        self.tq.push(now, Body::Node(t));
    }

    pub(crate) fn is_hub_id(&self, id: &NodeId) -> bool {
        self.hubs.contains(id)
    }

    /// The session table entries kept free for hub links: two per configured hub (its session, and the duplicate of
    /// a simultaneous dial that lives until it is closed), at most [`HUB_RESERVE_MAX`].
    pub(crate) fn hub_reserve(&self) -> usize {
        self.hubs.len().saturating_mul(2).min(HUB_RESERVE_MAX)
    }

    /// The full node id of a peer: the algorithm learned from a session or a configured relay, else ours.
    pub(crate) fn full_id(&self, id: &NodeId) -> vinc_crypto::NodeId {
        vinc_crypto::NodeId {
            alg: self.algs.get(id).copied().unwrap_or(self.my_alg),
            bytes: *id,
        }
    }

    pub(crate) fn learn_alg(&mut self, id: &vinc_crypto::NodeId) {
        if (self.algs.len() < TABLE_MAX || self.algs.contains_key(&id.bytes)) && id.alg != self.my_alg {
            self.algs.insert(id.bytes, id.alg);
        }
    }

    // ---------------------------------------------------------------- commands and streams

    /// Apply a command; the events its reply carries wait in the event queue for the loop.
    pub(crate) fn cmd(&mut self, c: Command<'_, E::Src>) -> Result<Value, CommandError> {
        let r = self.ep.command(self.now, c)?;
        self.evq.extend(r.events.iter().copied());
        Ok(r.value)
    }

    /// Close a session of the hub protocol or of a layer that the node cannot serve, and remember it until its close,
    /// so no event it still has queued reaches the application.
    // vertexia: a full set forgets the session, whose queued events the endpoint purges at its close; the set holds
    // a session only between this call and its `Closed`, so it does not fill in practice.
    pub(crate) fn shed(&mut self, session: SessionId) {
        if self.cmd(Command::Close { session, error: 0 }).is_ok() && self.shed.len() < TABLE_MAX {
            self.shed.insert(session);
        }
    }

    pub(crate) fn register_stream(&mut self, session: SessionId, stream: StreamId) {
        if self.strm.len() < TABLE_MAX || self.strm.contains_key(&(session, stream)) {
            self.strm.entry((session, stream)).or_insert_with(|| Strm {
                inb: Vec::with_capacity(512),
                outb: Vec::new(),
                off: 0,
                fin: false,
            });
        }
    }

    /// Open a bidirectional stream on `session`. `Err(true)` means the peer has not given credit for another stream yet, or
    /// the buffer pool has no room for its receive window: the caller keeps what it wanted and asks again on a later
    /// tick, when the peer raised its credit, streams have closed or data was read.
    pub(crate) fn try_open_stream(&mut self, session: SessionId) -> Result<StreamId, bool> {
        match self.cmd(Command::OpenStream { session, bidi: true }) {
            Ok(Value::Stream(s)) => {
                self.register_stream(session, s);
                self.strm.contains_key(&(session, s)).then_some(s).ok_or(false)
            }
            Err(CommandError::Stream(StreamError::Exhausted | StreamError::StreamLimit)) => Err(true),
            _ => Err(false),
        }
    }

    /// Open a bidirectional stream on `session`.
    pub(crate) fn open_stream(&mut self, session: SessionId) -> Option<StreamId> {
        self.try_open_stream(session).ok()
    }

    /// Like `try_open_stream`, at `urgency` (a lower number is sent first).
    pub(crate) fn try_open_stream_at(&mut self, session: SessionId, urgency: u8) -> Result<StreamId, bool> {
        let s = self.try_open_stream(session)?;
        let set = Command::SetUrgency {
            session,
            stream: s,
            urgency,
        };
        if self.cmd(set).is_err() {
            self.drop_strm(session, s);
            return Err(false);
        }
        Ok(s)
    }

    /// Open a bidirectional stream on `session` at `urgency` (a lower number is sent first).
    pub(crate) fn open_stream_at(&mut self, session: SessionId, urgency: u8) -> Option<StreamId> {
        self.try_open_stream_at(session, urgency).ok()
    }

    /// Write `data` to a stream behind whatever it already holds. False if the stream is gone or full.
    pub(crate) fn write(&mut self, session: SessionId, stream: StreamId, data: &[u8]) -> bool {
        let cap = self.out_cap;
        let Some(st) = self.strm.get_mut(&(session, stream)) else {
            return false;
        };
        if st.pending().saturating_add(data.len()) > cap {
            return false;
        }
        if st.pending() > 0 {
            st.outb.extend_from_slice(data);
            return true;
        }
        let n = match self.cmd(Command::Write { session, stream, data }) {
            Ok(Value::Written(n)) => n.min(data.len()),
            _ => return false,
        };
        if let Some(rest) = data.get(n..).filter(|r| !r.is_empty())
            && let Some(st) = self.strm.get_mut(&(session, stream))
        {
            st.outb.clear();
            st.off = 0;
            st.outb.extend_from_slice(rest);
        }
        true
    }

    /// The stream has room again: write what it holds.
    pub(crate) fn flush(&mut self, session: SessionId, stream: StreamId) {
        let Some(st) = self.strm.get_mut(&(session, stream)) else {
            return;
        };
        if st.pending() == 0 {
            return;
        }
        let buf = core::mem::take(&mut st.outb);
        let off = st.off;
        let Some(data) = buf.get(off..) else { return };
        let n = match self.cmd(Command::Write { session, stream, data }) {
            Ok(Value::Written(n)) => n.min(data.len()),
            _ => 0,
        };
        let mut finish = false;
        if let Some(st) = self.strm.get_mut(&(session, stream)) {
            st.outb = buf;
            st.off = off + n;
            if st.off >= st.outb.len() {
                st.outb.clear();
                st.off = 0;
                finish = core::mem::take(&mut st.fin);
            }
        }
        if finish {
            // A refused finish leaves the stream to the peer's reset or the session's end.
            let _ = self.cmd(Command::Finish { session, stream });
            self.strm.remove(&(session, stream));
        }
    }

    /// End our half of a stream once what it holds is written, then forget it. For a stream this node is done
    /// writing to.
    pub(crate) fn close_stream(&mut self, session: SessionId, stream: StreamId) {
        let Some(st) = self.strm.get_mut(&(session, stream)) else {
            return;
        };
        if st.pending() > 0 {
            st.fin = true;
            return;
        }
        // A refused finish leaves the stream to the peer's reset or the session's end.
        let _ = self.cmd(Command::Finish { session, stream });
        self.strm.remove(&(session, stream));
    }

    /// End the write side of a stream once everything written to it has been accepted.
    pub(crate) fn finish(&mut self, session: SessionId, stream: StreamId) -> bool {
        let Some(st) = self.strm.get_mut(&(session, stream)) else {
            return false;
        };
        if st.pending() > 0 {
            st.fin = true;
            return true;
        }
        self.cmd(Command::Finish { session, stream }).is_ok()
    }

    /// Release the first `n` unread bytes of a stream and report its receive state after that; `None` if the endpoint
    /// refused. Consuming nothing reads the state of the end: finished once the end arrived and every byte was
    /// consumed. The consume that releases the last byte is the one to read the end from: the endpoint forgets a
    /// stream once both of its sides are done, so a later call finds no stream.
    pub(crate) fn consume(&mut self, session: SessionId, stream: StreamId, n: usize) -> Option<RecvStatus> {
        match self.cmd(Command::Consume { session, stream, n }) {
            Ok(Value::Recv(st)) => Some(st),
            _ => None,
        }
    }

    /// Read what the endpoint holds for a stream into `into`, consuming it, and report the stream's receive state.
    /// `cap` bounds what `into` may hold; past it the stream is left unread and the second value is true.
    pub(crate) fn drain_stream(
        &mut self,
        session: SessionId,
        stream: StreamId,
        into: &mut Vec<u8>,
        cap: usize,
    ) -> (RecvStatus, bool) {
        let (mut over, mut last) = (false, None);
        while let Some(chunk) = self.ep.read_chunk(session, stream).filter(|c| !c.is_empty()) {
            let n = chunk.len();
            if into.len().saturating_add(n) > cap {
                over = true;
                break;
            }
            into.extend_from_slice(chunk);
            last = self.consume(session, stream, n);
            if last.is_none() {
                break;
            }
        }
        let status = match last {
            Some(st) if st != RecvStatus::Open => st,
            _ => self.consume(session, stream, 0).unwrap_or(RecvStatus::Open),
        };
        (status, over)
    }

    /// Hand a frame to the stream of `peer` on `lane`. With no stream the frame waits for a dial (at most
    /// [`QUEUE_FRAMES`] frames per peer), unless the peer is backing off.
    pub(crate) fn send_stream(&mut self, peer: &NodeId, lane: Lane, frame: &[u8]) -> bool {
        if self.revoked.contains(peer) || *peer == self.me {
            return false;
        }
        let target = self.links.get(peer).and_then(|l| {
            let conn = l.conn?;
            Some((conn, if lane == Lane::Fan { l.fan } else { l.out }))
        });
        match (lane, target) {
            (_, Some((conn, Some(s)))) => self.write(conn, s, frame),
            (Lane::Fan, Some((conn, None))) => {
                let Some(s) = self.open_stream_at(conn, vinc_core::FAN_URGENCY) else {
                    return false;
                };
                if let Some(l) = self.links.get_mut(peer) {
                    l.fan = Some(s);
                }
                self.write(conn, s, frame)
            }
            (Lane::Fan, None) | (Lane::Reply, _) => false,
            (Lane::Main, _) => self.enqueue(peer, frame),
        }
    }

    fn enqueue(&mut self, peer: &NodeId, frame: &[u8]) -> bool {
        let has_conn = self.links.get(peer).is_some_and(|l| l.conn.is_some());
        if !has_conn && self.failed.get(peer).is_some_and(|(until, _)| self.now < *until) {
            return false;
        }
        if self.queue.len() >= TABLE_MAX && !self.queue.contains_key(peer) {
            return false;
        }
        let cap = self.out_cap;
        let (q, bytes) = self.queue.entry(*peer).or_default();
        if q.len() >= QUEUE_FRAMES || bytes.saturating_add(frame.len()) > cap {
            return false;
        }
        q.push_back(frame.to_vec());
        *bytes += frame.len();
        if !has_conn && !self.connecting.contains_key(peer) && !self.dials.contains(peer) {
            self.dials.push(*peer);
        }
        true
    }

    /// The stream `stream` of `session` is up for `peer`: write what waited for it.
    pub(crate) fn flush_queue(&mut self, peer: &NodeId, session: SessionId, stream: StreamId) {
        let Some((q, _)) = self.queue.remove(peer) else {
            return;
        };
        for f in q {
            self.write(session, stream, &f);
        }
    }

    pub(crate) fn drop_queue(&mut self, peer: &NodeId) {
        self.queue.remove(peer);
    }

    /// Forget a stream and what it held.
    pub(crate) fn drop_strm(&mut self, session: SessionId, stream: StreamId) {
        self.strm.remove(&(session, stream));
    }

    /// Forget every stream of a session.
    pub(crate) fn drop_session_streams(&mut self, session: SessionId) {
        let keys: Vec<(SessionId, StreamId)> = self
            .strm
            .range((session, StreamId::MIN)..=(session, StreamId::MAX))
            .map(|(k, _)| *k)
            .collect();
        for k in keys {
            self.strm.remove(&k);
        }
    }

    // ---------------------------------------------------------------- evidence and backoff

    /// Look at every hub-protocol session's packet count and note when it last moved. The transport reports when the
    /// last packet arrived on the active path only, and a quiet session's direct path idles out; the count moves
    /// whatever the path.
    pub(crate) fn sample_rx(&mut self) {
        let now = self.now;
        for sid in self.sess.keys() {
            let Some(st) = self.ep.stats(*sid) else { continue };
            let n = st.transport.packets_received;
            let known = self.rx_seen.len();
            if let Some(e) = self.rx_seen.get_mut(sid) {
                if e.0 != n {
                    *e = (n, now);
                }
            } else if known < TABLE_MAX {
                self.rx_seen.insert(*sid, (n, now));
            }
        }
    }

    /// What the transport knows about the current session of `peer`.
    pub(crate) fn evidence_of(&self, peer: &NodeId) -> Option<Evidence> {
        let sid = self.links.get(peer)?.conn?;
        let st = self.ep.stats(sid).filter(|s| s.established)?;
        let extra = self.rx_seen.get(&sid).map_or(0, |e| e.1);
        Some(Evidence {
            last_rx: st.heard.max(extra),
            srtt: st.transport.srtt,
            pto: st.pto_count,
            inflight: u32::try_from(self.ep.in_flight(sid).unwrap_or(0)).unwrap_or(u32::MAX),
            direct: st.path_validated && st.route.is_some_and(|(_, r)| !is_relay_addr(&r)),
        })
    }

    /// The silence after which a peer heard again means a partition healed: one keepalive interval of a quiet session
    /// plus the time the transport takes to give the path up, at the live session's round trip or, with none, at the
    /// last round trip seen with the peer.
    pub(crate) fn give_up_of(&self, peer: &NodeId) -> Nanos {
        let sid = self.links.get(peer).and_then(|l| l.conn);
        let live = sid.and_then(|s| self.ep.stats(s)).map(|s| (s.transport.srtt, s.thin));
        let (srtt, thin) = live.or_else(|| self.rtts.get(peer).copied()).unwrap_or((0, false));
        let accepted = sid.and_then(|s| self.sess.get(&s)).is_some_and(|s| s.incoming);
        let keepalive = if accepted {
            QUIET_KEEP_ACCEPTOR
        } else {
            QUIET_KEEP_DIALER
        };
        bound::heal_after(keepalive, srtt, thin)
    }

    /// Remember the round trip of every live hub session, so the bound survives the session.
    pub(crate) fn note_rtts(&mut self) {
        for i in 0..self.hubs.len() {
            let Some(hub) = self.hubs.get(i).copied() else {
                continue;
            };
            let Some(sid) = self.links.get(&hub).and_then(|l| l.conn) else {
                continue;
            };
            if let Some(st) = self.ep.stats(sid).filter(|s| s.established && s.transport.srtt > 0) {
                self.rtts.insert(hub, (st.transport.srtt, st.thin));
            }
        }
    }

    pub(crate) fn backoff(&mut self, peer: &NodeId) {
        let cap = if self.is_hub_id(peer) {
            BACKOFF_HUB_CAP
        } else {
            BACKOFF_CAP
        };
        let back = self
            .failed
            .get(peer)
            .map_or(BACKOFF_FIRST, |(_, b)| b.saturating_mul(2).min(cap));
        self.set_failed(peer, back, false);
    }

    /// The peer's access check refused us: an authorization decision, not a path problem. Redial rarely.
    pub(crate) fn deny_back(&mut self, peer: &NodeId) {
        let back = match self.failed.get(peer) {
            Some((_, b)) if *b >= DENY_FIRST => b.saturating_mul(2).min(DENY_CAP),
            _ => DENY_FIRST,
        };
        self.set_failed(peer, back, true);
    }

    fn set_failed(&mut self, peer: &NodeId, back: Nanos, denied: bool) {
        if self.failed.len() < TABLE_MAX || self.failed.contains_key(peer) {
            self.failed.insert(*peer, (self.now.saturating_add(back), back));
        }
        self.trace(NodeTrace::Backoff {
            peer: tag(peer),
            wait_ms: back / 1_000_000,
            denied: u64::from(denied),
        });
    }

    /// Close the current session with `peer`.
    pub(crate) fn close_peer(&mut self, peer: &NodeId, reason: CloseReason) -> bool {
        let Some(session) = self.links.get(peer).and_then(|l| l.conn) else {
            return false;
        };
        let error = match reason {
            CloseReason::NoAck | CloseReason::Stale => 0,
            CloseReason::Leave => LEAVE_CODE,
            CloseReason::Revoked => DENIED_CODE,
        };
        // A refused close leaves the session to the transport's own timeout.
        self.cmd(Command::Close { session, error }).is_ok()
    }

    /// Hand a membership frame to the stream of `peer`. A frame the stream's backlog refuses because it is full is
    /// never lost silently: the session is closed (and counted), so the reconnect and the new HELLO repair what the
    /// frame carried.
    pub(crate) fn send_membership(&mut self, peer: &NodeId, lane: Lane, frame: &[u8]) -> bool {
        if self.send_stream(peer, lane, frame) {
            return true;
        }
        if self.backlog_full(peer, frame.len()) && self.close_peer(peer, CloseReason::Stale) {
            self.trace(NodeTrace::BacklogClosed { peer: tag(peer) });
        }
        false
    }

    pub(crate) fn backlog_full(&self, peer: &NodeId, len: usize) -> bool {
        let Some((conn, out)) = self.links.get(peer).and_then(|l| Some((l.conn?, l.out?))) else {
            return false;
        };
        self.strm
            .get(&(conn, out))
            .is_some_and(|st| st.pending().saturating_add(len) > self.out_cap)
    }
}

#[cfg(test)]
mod tests;
