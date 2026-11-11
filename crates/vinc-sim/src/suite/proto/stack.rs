//! The application and the harness protocols of one node, as the node adapter drives them.
//!
//! [`Stack`] implements [`Layers`]: it owns the four harness protocols (PUSHLOG, DOCSYNC, MANAGE, ECHO), the
//! application that turns scenario intents into work on them and records every delivery, and up to three on-top
//! layers ([`OnTop`]). Every session belongs to one owner by its protocol name; every stream carries a [`Framer`] and
//! a write queue that survives partial writes.
//!
//! Invariants: a stream's state exists only while its session does; a framing error resets the stream and records a
//! G-INT violation; nothing buffers more than one frame body per stream; durable state is written to the shared
//! [`Durable`] before the bytes that depend on it.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::rc::Rc;

use vinc_core::SessionId;
use vinc_transport::stream::StreamId;

use super::durable::Durable;
use super::frame::{Frame, Framer};
use super::host::{Host, LayerEvent, Layers};
use super::ontop::{OnTop, ValueIds};
use super::pushlog::PushPeer;
use super::reqresp::ReqResp;
use crate::suite::rec::Rec;
use crate::suite::world::model::{Intent, World};

/// The protocol name of PUSHLOG.
pub const ALPN_PUSHLOG: &[u8] = b"/defra/pushlog/1";
/// The protocol name of DOCSYNC.
pub const ALPN_DOCSYNC: &[u8] = b"/defra/docsync/1";
/// The protocol name of MANAGE.
pub const ALPN_MANAGE: &[u8] = b"/defra/manage/1";
/// The protocol name of ECHO.
pub const ALPN_ECHO: &[u8] = b"/echo/1";

/// A stream of a session.
pub(super) type Key = (SessionId, StreamId);

/// A harness protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Proto {
    PushLog,
    DocSync,
    Manage,
    Echo,
}

impl Proto {
    pub(super) fn alpn(self) -> &'static [u8] {
        match self {
            Self::PushLog => ALPN_PUSHLOG,
            Self::DocSync => ALPN_DOCSYNC,
            Self::Manage => ALPN_MANAGE,
            Self::Echo => ALPN_ECHO,
        }
    }

    /// The index into the request/response layers.
    pub(super) fn rr(self) -> usize {
        usize::from(self == Self::Manage)
    }
}

/// An on-top slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Slot {
    Broadcast,
    Values,
    Reconcile,
}

pub(super) const SLOTS: [Slot; 3] = [Slot::Broadcast, Slot::Values, Slot::Reconcile];

/// Who handles the events of a session.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Owner {
    Harness(Proto),
    OnTop(Slot),
}

/// A session of this node.
#[derive(Debug, Clone, Copy)]
pub(super) struct Sess {
    pub(super) peer: usize,
    pub(super) owner: Owner,
}

/// What a stream is for, beyond its protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum Role {
    None,
    /// The client side of an echo, waiting for the answer to this intent.
    EchoClient(u32),
}

/// A write queue: bytes the endpoint has not accepted yet, then the end of the stream.
#[derive(Debug, Default)]
pub(super) struct Out {
    buf: Vec<u8>,
    off: usize,
    fin: bool,
    fin_sent: bool,
}

impl Out {
    fn flush(&mut self, host: &mut dyn Host, key: Key) {
        while self.off < self.buf.len() {
            let n = host.write(key.0, key.1, &self.buf[self.off..]);
            self.off += n;
            if self.off < self.buf.len() {
                if self.off > 4096 && self.off * 2 > self.buf.len() {
                    self.buf.drain(..self.off);
                    self.off = 0;
                }
                return;
            }
        }
        self.buf.clear();
        self.off = 0;
        if self.fin && !self.fin_sent {
            host.finish(key.0, key.1);
            self.fin_sent = true;
        }
    }

    fn done(&self) -> bool {
        self.off >= self.buf.len() && (!self.fin || self.fin_sent)
    }
}

/// The state of a stream.
#[derive(Debug)]
pub(super) struct Stream {
    pub(super) framer: Framer,
    pub(super) out: Out,
    pub(super) rx_done: bool,
    pub(super) role: Role,
}

impl Stream {
    pub(super) fn new(role: Role) -> Self {
        Self {
            framer: Framer::new(),
            out: Out::default(),
            rx_done: false,
            role,
        }
    }
}

/// A timer set: the deadlines one layer asked for.
#[derive(Debug, Default)]
pub(super) struct Timers(pub(super) BTreeSet<u64>);

impl Timers {
    pub(super) fn pop_due(&mut self, now: u64) {
        while self.0.first().is_some_and(|&t| t <= now) {
            self.0.pop_first();
        }
    }
}

/// The application and the harness protocols of one node.
pub struct Stack {
    pub(super) idx: usize,
    pub(super) world: Rc<World>,
    pub(super) rec: Rc<RefCell<Rec>>,
    pub(super) durable: Rc<RefCell<Durable>>,
    pub(super) sessions: BTreeMap<SessionId, Sess>,
    pub(super) streams: BTreeMap<Key, Stream>,
    pub(super) pl_peers: BTreeMap<usize, PushPeer>,
    pub(super) pl_timers: Timers,
    pub(super) rr: [ReqResp; 2],
    pub(super) echo_pending: BTreeMap<usize, std::collections::VecDeque<u32>>,
    /// Fetch id to intent id.
    pub(super) fetch_ids: BTreeMap<u64, u32>,
    pub(super) broadcast: Option<Box<dyn OnTop>>,
    pub(super) values: Option<Box<dyn OnTop>>,
    pub(super) reconcile: Option<Box<dyn OnTop>>,
    pub(super) value_ids: Rc<ValueIds>,
    /// Intents that arrived for a layer that is not registered, by intent kind name: the work is waiting for the
    /// layer, not lost, and nothing was recorded for it.
    pub waiting: BTreeMap<&'static str, u64>,
}

impl Stack {
    /// The stack of node `idx` on top of the durable state `durable` (a restart passes the same one). Register the
    /// on-top layers with the `with_*` methods before the first [`Layers::boot`].
    pub fn new(idx: usize, world: Rc<World>, rec: Rc<RefCell<Rec>>, durable: Rc<RefCell<Durable>>) -> Self {
        Self {
            idx,
            world,
            rec,
            durable,
            sessions: BTreeMap::new(),
            streams: BTreeMap::new(),
            pl_peers: BTreeMap::new(),
            pl_timers: Timers::default(),
            rr: [ReqResp::default(), ReqResp::default()],
            echo_pending: BTreeMap::new(),
            fetch_ids: BTreeMap::new(),
            broadcast: None,
            values: None,
            reconcile: None,
            value_ids: Rc::new(ValueIds::new()),
            waiting: BTreeMap::new(),
        }
    }

    // Registration of the on-top layers: broadcast (S2 gossip, S13 late publishes), values, reconcile, and the
    // membership integration (the layers report member events through `OnTopEvent::Member`). Each is one call here.

    /// Registers the broadcast layer.
    #[must_use]
    pub fn with_broadcast(mut self, layer: Box<dyn OnTop>) -> Self {
        self.broadcast = Some(layer);
        self
    }

    /// Registers the values layer; `ids` maps the world's value names to their generated content.
    #[must_use]
    pub fn with_values(mut self, layer: Box<dyn OnTop>, ids: Rc<ValueIds>) -> Self {
        self.values = Some(layer);
        self.value_ids = ids;
        self
    }

    /// Registers the reconcile layer.
    #[must_use]
    pub fn with_reconcile(mut self, layer: Box<dyn OnTop>) -> Self {
        self.reconcile = Some(layer);
        self
    }

    pub(super) fn slot_mut(&mut self, slot: Slot) -> Option<&mut Box<dyn OnTop>> {
        match slot {
            Slot::Broadcast => self.broadcast.as_mut(),
            Slot::Values => self.values.as_mut(),
            Slot::Reconcile => self.reconcile.as_mut(),
        }
    }

    fn slots(&self) -> impl Iterator<Item = (Slot, &dyn OnTop)> {
        [
            (Slot::Broadcast, &self.broadcast),
            (Slot::Values, &self.values),
            (Slot::Reconcile, &self.reconcile),
        ]
        .into_iter()
        .filter_map(|(s, l)| l.as_deref().map(|l| (s, l)))
    }

    fn owner_of_alpn(&self, alpn: &[u8]) -> Option<Owner> {
        [Proto::PushLog, Proto::DocSync, Proto::Manage, Proto::Echo]
            .into_iter()
            .find(|p| p.alpn() == alpn)
            .map(Owner::Harness)
            .or_else(|| {
                self.slots()
                    .find(|(_, l)| l.alpns().contains(&alpn))
                    .map(|(s, _)| Owner::OnTop(s))
            })
    }

    /// Queues `bytes` on a stream and writes what the endpoint takes; `fin` ends the stream after them.
    pub(super) fn send(&mut self, host: &mut dyn Host, key: Key, bytes: &[u8], fin: bool) {
        if let Some(st) = self.streams.get_mut(&key) {
            st.out.buf.extend_from_slice(bytes);
            st.out.fin |= fin;
        }
        self.flush(host, key);
    }

    fn flush(&mut self, host: &mut dyn Host, key: Key) {
        if let Some(st) = self.streams.get_mut(&key) {
            st.out.flush(host, key);
        }
        self.gc(key);
    }

    fn gc(&mut self, key: Key) {
        if self.streams.get(&key).is_some_and(|s| s.rx_done && s.out.done()) {
            self.streams.remove(&key);
        }
    }

    pub(super) fn violation(&self, now: u64, gate: &str, msg: &str) {
        self.rec.borrow_mut().violation(now, gate, self.idx, msg);
    }

    /// A stream that cannot be read: record it, reset it, forget it.
    fn framing_error(&mut self, now: u64, host: &mut dyn Host, key: Key, proto: Proto, err: &str) {
        let msg = format!("{}: {err}", String::from_utf8_lossy(proto.alpn()));
        self.violation(now, "G-INT", &msg);
        host.reset(key.0, key.1, 1);
        self.streams.remove(&key);
    }

    fn on_data(&mut self, now: u64, host: &mut dyn Host, key: Key, proto: Proto, data: &[u8], fin: bool) {
        let mut frames: Vec<Frame> = Vec::new();
        let st = self.streams.entry(key).or_insert_with(|| Stream::new(Role::None));
        let mut err = st.framer.feed(data, &mut frames).err().map(|e| e.to_string());
        for f in frames {
            if let Err(e) = self.on_frame(now, host, key, proto, &f) {
                err = Some(e);
                break;
            }
        }
        if let Some(e) = err {
            self.framing_error(now, host, key, proto, &e);
            return;
        }
        if fin {
            if let Some(st) = self.streams.get_mut(&key) {
                st.rx_done = true;
            }
            self.on_stream_end(now, key, proto, false);
            self.gc(key);
        }
    }

    fn on_frame(&mut self, now: u64, host: &mut dyn Host, key: Key, proto: Proto, f: &Frame) -> Result<(), String> {
        match proto {
            Proto::PushLog => self.pl_frame(now, host, key, f),
            Proto::DocSync | Proto::Manage => self.rr_frame(now, host, key, proto, f),
            Proto::Echo => {
                self.echo_frame(now, host, key, f);
                Ok(())
            }
        }
    }

    fn on_stream_end(&mut self, now: u64, key: Key, proto: Proto, reset: bool) {
        if matches!(proto, Proto::DocSync | Proto::Manage) {
            self.rr_stream_end(now, key, proto, reset);
        }
    }

    fn harness_event(&mut self, now: u64, host: &mut dyn Host, p: Proto, ev: &LayerEvent<'_>) {
        match *ev {
            LayerEvent::Incoming { session, peer, .. } => {
                self.sessions.insert(
                    session,
                    Sess {
                        peer,
                        owner: Owner::Harness(p),
                    },
                );
            }
            LayerEvent::Connected { session, peer, .. } => {
                let owner = Owner::Harness(p);
                self.sessions.insert(session, Sess { peer, owner });
                match p {
                    Proto::PushLog => self.pl_connected(now, host, session, peer),
                    Proto::DocSync | Proto::Manage => self.rr_connected(now, host, p, session, peer),
                    Proto::Echo => self.echo_connected(now, host, session, peer),
                }
            }
            LayerEvent::ConnectFailed { peer, .. } => match p {
                Proto::PushLog => self.pl_connect_failed(now, peer),
                Proto::DocSync | Proto::Manage => self.rr_connect_failed(p, peer),
                Proto::Echo => self.echo_connect_failed(peer),
            },
            LayerEvent::Closed { session } => {
                let sess = self.sessions.remove(&session);
                self.streams.retain(|k, _| k.0 != session);
                let Some(sess) = sess else { return };
                match p {
                    Proto::PushLog => self.pl_closed(now, session, sess.peer),
                    Proto::DocSync | Proto::Manage => self.rr_closed(now, host, p, session, sess.peer),
                    Proto::Echo => {}
                }
            }
            LayerEvent::StreamOpened { session, stream } => {
                self.streams
                    .entry((session, stream))
                    .or_insert_with(|| Stream::new(Role::None));
            }
            LayerEvent::StreamData {
                session,
                stream,
                data,
                fin,
            } => self.on_data(now, host, (session, stream), p, data, fin),
            LayerEvent::StreamReset { session, stream } => {
                self.streams.remove(&(session, stream));
                self.on_stream_end(now, (session, stream), p, true);
            }
            LayerEvent::StreamWritable { session, stream } => self.flush(host, (session, stream)),
            LayerEvent::Message { .. } | LayerEvent::Member(_) => {}
        }
    }
}

impl Layers for Stack {
    fn alpns(&self) -> Vec<&'static [u8]> {
        let mut v = vec![ALPN_PUSHLOG, ALPN_DOCSYNC, ALPN_MANAGE, ALPN_ECHO];
        for (_, l) in self.slots() {
            for a in l.alpns() {
                if !v.contains(&a) {
                    v.push(a);
                }
            }
        }
        v
    }

    fn boot(&mut self, now: u64, host: &mut dyn Host) {
        self.reset_volatile();
        self.durable.borrow_mut().incarnations += 1;
        for slot in SLOTS {
            if let Some(l) = self.slot_mut(slot) {
                l.boot(now, host);
            }
        }
        self.pl_boot(now);
        self.app_boot(now, host);
        self.drain_ontop(now, host.registry());
    }

    fn intent(&mut self, now: u64, host: &mut dyn Host, intent: &Intent) {
        self.app_intent(now, host, intent);
        self.drain_ontop(now, host.registry());
    }

    fn event(&mut self, now: u64, host: &mut dyn Host, ev: LayerEvent<'_>) {
        let owner = match &ev {
            // The node's broadcast messages and membership events belong to the broadcast slot.
            LayerEvent::Message { .. } | LayerEvent::Member(_) => Some(Owner::OnTop(Slot::Broadcast)),
            LayerEvent::Incoming { alpn, .. }
            | LayerEvent::Connected { alpn, .. }
            | LayerEvent::ConnectFailed { alpn, .. } => self.owner_of_alpn(alpn),
            LayerEvent::Closed { session }
            | LayerEvent::StreamOpened { session, .. }
            | LayerEvent::StreamData { session, .. }
            | LayerEvent::StreamReset { session, .. }
            | LayerEvent::StreamWritable { session, .. } => self.sessions.get(session).map(|s| s.owner),
        };
        match owner {
            None => {}
            Some(Owner::Harness(p)) => self.harness_event(now, host, p, &ev),
            Some(Owner::OnTop(slot)) => {
                match &ev {
                    LayerEvent::Incoming { session, peer, .. } | LayerEvent::Connected { session, peer, .. } => {
                        self.sessions.insert(
                            *session,
                            Sess {
                                peer: *peer,
                                owner: Owner::OnTop(slot),
                            },
                        );
                    }
                    LayerEvent::Closed { session } => {
                        self.sessions.remove(session);
                    }
                    _ => {}
                }
                if let Some(l) = self.slot_mut(slot) {
                    l.event(now, host, ev);
                }
                self.drain_ontop(now, host.registry());
            }
        }
    }

    fn timeout(&mut self, now: u64, host: &mut dyn Host) {
        self.pl_timeout(now, host);
        self.rr_timeout(now, host);
        for slot in SLOTS {
            if let Some(l) = self.slot_mut(slot)
                && l.poll_timeout().is_some_and(|t| t <= now)
            {
                l.timeout(now, host);
            }
        }
        self.drain_ontop(now, host.registry());
    }

    fn poll_timeout(&self) -> Option<u64> {
        let own = [&self.pl_timers, &self.rr[0].timers, &self.rr[1].timers]
            .into_iter()
            .filter_map(|t| t.0.first().copied());
        let layers = self.slots().filter_map(|(_, l)| l.poll_timeout());
        own.chain(layers).min()
    }

    fn has_open_intents(&self, _now: u64) -> bool {
        let d = self.durable.borrow();
        if !d.open_fetches.is_empty() {
            return true;
        }
        let rec = self.rec.borrow();
        let undelivered = d
            .pl_out
            .values()
            .flat_map(|o| o.unacked.iter())
            .any(|u| rec.intents.get(&u.iid).is_some_and(|it| it.delivered.is_empty()));
        undelivered || self.world.nodes.get(self.idx).is_some_and(|n| !n.topics.is_empty())
    }

    fn stop(&mut self) {
        self.reset_volatile();
        for slot in SLOTS {
            if let Some(l) = self.slot_mut(slot) {
                l.stop();
            }
        }
    }
}

impl Stack {
    fn reset_volatile(&mut self) {
        self.sessions.clear();
        self.streams.clear();
        self.pl_peers.clear();
        self.pl_timers = Timers::default();
        self.rr = [ReqResp::default(), ReqResp::default()];
        self.echo_pending.clear();
        self.fetch_ids.clear();
    }
}
