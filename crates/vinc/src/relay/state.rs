//! The relay's state: the state machine, the accepted streams, and what the machine's effects turn into.
//!
//! Everything here is synchronous and never waits: the run loop (see `run`) moves bytes in and out of the host's
//! closures and calls these methods with what it got.
//!
//! Invariants: a node has at most one stream in the node table; the number of streams still in their handshake never
//! passes its limit; a stream's queue never passes the backlog limit; an effect is applied after the machine call that
//! produced it has returned.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, VecDeque};
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::net::SocketAddr;

use vinc_connect::carrier::ProtectedCarrier;
use vinc_connect::carrier::session::{self, OUT_LEN, Poll};
use vinc_connect::carrier::ws::{self, Opcode, WsFrame};
use vinc_connect::relay::{CloseReason, Config, SessionId, Trace, UdpTarget};
use vinc_crypto::{Drbg, NodeId, Software};
use vinc_keystore::KeyStore;
use vinc_security::{ConnId, Env, KeyRequest, KeyResponse, LocalIdentity, PrekeyInfo, ResponderStores};

use super::conn::Conn;
use super::fx::{Fx, Item};
use super::hub::{Hub, Note, Target};
use super::limits::{Limits, Machine};
use super::peers::{Peer, Slot};
use super::stats::{Closed, Counters, Event, Events, Reason, Stats};
use super::store::node_key;
use crate::carrier::CarrierKind;
use crate::keys::{Identity, Prekeys, is_identity};

mod keep;
mod mesh;

pub(crate) use keep::Job;

/// The most control datagrams waiting for the socket.
const UDP_BACKLOG: usize = 256;
/// The most steps one stream's handshake and frames take in one call, so one stream cannot hold the loop.
const STEP_BUDGET: usize = 256;
/// The interval of the checks of stream deadlines.
const CHECK_NS: u64 = 1_000_000_000;

/// What one step of a stream's carrier found.
enum Step {
    Idle,
    Progress,
    Frame,
    Open(NodeId),
    Dead,
    Gone,
}

pub(crate) struct Core<S, K: KeyStore> {
    pub(crate) sm: Box<Machine>,
    pub(crate) conns: Vec<Option<Conn<S>>>,
    free: Vec<usize>,
    by_node: BTreeMap<[u8; 33], usize>,
    identity: Identity<K>,
    local: LocalIdentity,
    drbg: Drbg,
    stores: Box<ResponderStores<4, 4>>,
    scid: u64,
    peers: Vec<Slot>,
    prekeys: Prekeys,
    dial_prekey: PrekeyInfo,
    pub(crate) limits: Limits,
    pub(crate) counters: Counters,
    events: Events,
    fx: Fx,
    unit: Vec<u8>,
    hs: Vec<u8>,
    handshaking: usize,
    check_at: u64,
    udp_out: VecDeque<(SocketAddr, Vec<u8>)>,
    udp_pool: Vec<Vec<u8>>,
    keep: keep::Keep,
    pub(crate) stopping: bool,
    hub: Option<Hub>,
    notes: Vec<Note>,
    hub_tx: Vec<u8>,
    last_now: u64,
}

#[inline(never)]
fn new_machine(cfg: Config) -> Box<Machine> {
    Box::new(Machine::new(cfg))
}

impl<S, K: KeyStore> Core<S, K> {
    pub(crate) fn new(
        mut identity: Identity<K>,
        peers: &[Peer],
        limits: Limits,
        hub: Option<(SocketAddr, Vec<Vec<u8>>)>,
        now: u64,
    ) -> crate::Result<Self> {
        let mut seed = [0u8; 32];
        identity.random(&mut seed)?;
        let mut key = [0u8; 8];
        identity.random(&mut key)?;
        let mut cfg = Config::new(identity.node_id(), u64::from_le_bytes(key));
        cfg.quota = limits.quota;
        cfg.mailbox_max_age_ns = limits.mailbox_max_age_ns;
        let local = identity.local()?;
        let mut prekeys = Prekeys::new()?;
        let dial_prekey = prekeys.rotate(now)?;
        let peers = mesh::slots(&identity.node_id(), peers, now);
        let hub = match hub {
            Some((addr, alpns)) => Some(Hub::new(addr, &alpns, &mut identity, &limits, now)?),
            None => None,
        };
        Ok(Self {
            sm: new_machine(cfg),
            conns: Vec::new(),
            free: Vec::new(),
            by_node: BTreeMap::new(),
            identity,
            local,
            drbg: Drbg::new(&seed),
            stores: Box::default(),
            scid: 0,
            peers,
            prekeys,
            dial_prekey,
            limits,
            counters: Counters::default(),
            events: Events::new(limits.events),
            fx: Fx::default(),
            unit: alloc::vec![0; vinc_connect::carrier::MAX_FRAME_LEN + 64],
            hs: alloc::vec![0; OUT_LEN],
            handshaking: 0,
            check_at: now.saturating_add(CHECK_NS),
            udp_out: VecDeque::new(),
            udp_pool: Vec::new(),
            keep: keep::Keep::default(),
            stopping: false,
            hub,
            notes: Vec::new(),
            hub_tx: alloc::vec![0; vinc_core::MAX_DATAGRAM + 64],
            last_now: now,
        })
    }

    pub(crate) fn node_id(&self) -> NodeId {
        self.identity.node_id()
    }

    pub(crate) fn pop_event(&mut self) -> Option<Event> {
        self.events.pop()
    }

    fn event(&mut self, e: Event) {
        if self.events.push(e) {
            self.counters.events_dropped += 1;
        }
    }

    pub(crate) fn stats(&self) -> Stats {
        let c = &self.counters;
        Stats {
            carriers: self.sm.sessions(),
            peers_up: self
                .conns
                .iter()
                .flatten()
                .filter(|c| c.peer && c.node.is_some() && c.dying.is_none())
                .count(),
            peer_dial_failures: c.peer_dial_failures,
            carriers_opened: c.carriers_opened,
            carriers_closed: c.carriers_closed,
            protocol_failures: c.protocol_failures,
            slow_closed: c.slow_closed,
            timed_out: c.timed_out,
            refused_carriers_full: c.refused_carriers_full,
            refused_handshakes_full: c.refused_handshakes_full,
            accept_errors: c.accept_errors,
            datagrams_in: c.datagrams_in,
            datagrams_out: c.datagrams_out,
            datagrams_dropped: c.datagrams_dropped,
            hub_dropped: c.hub_dropped,
            hub_sessions: self.hub.as_ref().map_or(0, Hub::sessions),
            records: self.sm.record_count(),
            store_errors: c.store_errors,
            events_dropped: c.events_dropped,
            refused: c.refused,
            machine: self.sm.stats(),
            mailbox: self.sm.mailbox_stats(),
            mailbox_members: self.sm.mailbox_members(),
        }
    }

    fn conn(&mut self, slot: usize) -> Option<&mut Conn<S>> {
        self.conns.get_mut(slot).and_then(Option::as_mut)
    }

    /// Admit an accepted stream, or give it back if too many streams are still in their handshake.
    pub(crate) fn add_conn(&mut self, stream: S, kind: CarrierKind, now: u64) -> Result<usize, S> {
        if self.handshaking >= self.limits.handshaking || self.stopping {
            self.counters.refused_handshakes_full += 1;
            return Err(stream);
        }
        self.scid += 1;
        let Some(scid) = ConnId::new(&self.scid.to_be_bytes()) else {
            return Err(stream);
        };
        let Ok(cfg) = session::responder_config(self.local, scid) else {
            return Err(stream);
        };
        let mut conn = Conn::new(
            stream,
            kind,
            Box::new(ProtectedCarrier::accept(cfg)),
            now.saturating_add(self.limits.handshake_ns),
        );
        conn.last_rx = now;
        self.handshaking += 1;
        Ok(self.place(conn))
    }

    /// Put a stream in a free slot.
    fn place(&mut self, conn: Conn<S>) -> usize {
        if let Some(slot) = self.free.pop()
            && let Some(entry) = self.conns.get_mut(slot)
        {
            *entry = Some(conn);
            return slot;
        }
        self.conns.push(Some(conn));
        self.conns.len() - 1
    }

    /// The stream and read buffer of a read to start, if the stream wants one.
    pub(crate) fn take_read(&mut self, slot: usize) -> Option<(Rc<S>, Vec<u8>)> {
        let c = self.conn(slot)?;
        let buf = c.take_read()?;
        Some((Rc::clone(&c.stream), buf))
    }

    /// The stream, bytes and offset of a write to start, if the stream has something to write.
    pub(crate) fn take_write(&mut self, slot: usize) -> Option<(Rc<S>, Vec<u8>, usize)> {
        let masked = self.conn(slot).is_some_and(|c| c.dialer && c.kind == CarrierKind::Ws);
        let mask = self.mask(masked);
        let c = self.conn(slot)?;
        let (buf, from) = c.take_write(mask)?;
        Some((Rc::clone(&c.stream), buf, from))
    }

    /// A WebSocket mask key if `masked` (this relay is the client of the stream).
    fn mask(&mut self, masked: bool) -> Option<[u8; 4]> {
        let mut m = [0u8; 4];
        (masked && self.drbg.fill(&mut m).is_ok()).then_some(m)
    }

    /// A write finished.
    pub(crate) fn on_write(&mut self, slot: usize, r: crate::Result<usize>, buf: Vec<u8>) {
        let Some(c) = self.conn(slot) else { return };
        match r {
            Ok(n) if n > 0 => {
                c.wrote(buf, n);
                if c.peer && !c.sync.is_empty() {
                    self.pump_sync(slot);
                }
            }
            _ => {
                c.wrote(buf, 0);
                self.dying(slot, Closed::Peer);
            }
        }
    }

    /// A read finished with `r` bytes in `buf`.
    pub(crate) fn on_read(&mut self, slot: usize, now: u64, r: crate::Result<usize>, buf: Vec<u8>) {
        self.last_now = now;
        match r {
            Ok(n) if n > 0 => {
                if let Some(c) = self.conn(slot) {
                    c.last_rx = now;
                    if c.kind == CarrierKind::Ws {
                        self.read_ws(slot, now, &buf, n);
                    } else {
                        self.feed(slot, now, buf.get(..n).unwrap_or_default());
                    }
                }
            }
            _ => self.dying(slot, Closed::Peer),
        }
        if let Some(c) = self.conn(slot) {
            c.put_read(buf);
        }
        self.pump_hub(now);
    }

    fn read_ws(&mut self, slot: usize, now: u64, buf: &[u8], n: usize) {
        let Some(c) = self.conn(slot) else { return };
        let mut acc = core::mem::take(&mut c.ws_in);
        let mut dec = c.dec;
        acc.extend_from_slice(buf.get(..n).unwrap_or_default());
        let mut pos = 0;
        while self.conn(slot).is_some_and(|c| c.dying.is_none()) {
            let Some(win) = acc.get_mut(pos..) else { break };
            match dec.decode(win) {
                Ok(None) => break,
                Ok(Some((WsFrame::Data(p), used))) => {
                    self.feed(slot, now, p);
                    pos += used;
                }
                Ok(Some((WsFrame::Ping(p), used))) => {
                    let mut f = [0u8; 2 + 4 + 125];
                    let masked = self.conn(slot).is_some_and(|c| c.dialer);
                    let mask = self.mask(masked);
                    if let Some(c) = self.conn(slot)
                        && let Ok(len) = ws::encode(Opcode::Pong, p, mask, &mut f)
                    {
                        c.push_ctl(f.get(..len).unwrap_or_default());
                    }
                    pos += used;
                }
                Ok(Some((WsFrame::Pong(_), used))) => pos += used,
                Ok(Some((WsFrame::Close(_), _))) => {
                    self.dying(slot, Closed::Peer);
                    break;
                }
                Err(_) => {
                    self.dying(slot, Closed::Protocol);
                    break;
                }
            }
        }
        acc.drain(..pos.min(acc.len()));
        let too_long = acc.len() > ws::MAX_PAYLOAD + ws::MAX_HEADER;
        if too_long {
            self.dying(slot, Closed::Protocol);
            acc.clear();
        }
        if let Some(c) = self.conn(slot) {
            c.ws_in = acc;
            c.dec = dec;
        }
    }

    /// Give bytes of the stream to its carrier and handle what comes out.
    fn feed(&mut self, slot: usize, now: u64, mut bytes: &[u8]) {
        while !bytes.is_empty() {
            let Some(c) = self.conn(slot).filter(|c| c.dying.is_none()) else {
                return;
            };
            let n = c.carrier.receive(bytes);
            bytes = bytes.get(n..).unwrap_or_default();
            let progressed = self.drive(slot, now);
            if n == 0 && !progressed {
                self.dying(slot, Closed::Protocol);
                return;
            }
        }
    }

    /// Run the carrier until it needs more bytes; whether anything happened.
    fn drive(&mut self, slot: usize, now: u64) -> bool {
        let mut any = false;
        for _ in 0..STEP_BUDGET {
            match self.step(slot, now) {
                Step::Idle | Step::Gone => break,
                Step::Progress => {
                    any = true;
                    self.transmit_handshake(slot);
                }
                Step::Frame => {
                    any = true;
                    self.flush();
                }
                Step::Open(peer) => {
                    any = true;
                    self.transmit_handshake(slot);
                    self.on_open(slot, peer, now);
                }
                Step::Dead => {
                    any = true;
                    self.dying(slot, Closed::Protocol);
                    break;
                }
            }
        }
        any
    }

    fn step(&mut self, slot: usize, now: u64) -> Step {
        let Self {
            conns,
            sm,
            drbg,
            stores,
            identity,
            prekeys,
            fx,
            ..
        } = self;
        let Some(c) = conns.get_mut(slot).and_then(Option::as_mut) else {
            return Step::Gone;
        };
        if c.dying.is_some() {
            return Step::Gone;
        }
        let mut env = Env {
            provider: &Software,
            now,
            drbg,
        };
        let polled = if c.carrier.key_request().is_some() {
            let (sig, secret) = match c.carrier.key_request() {
                Some(KeyRequest::Sign { key, message, .. }) if is_identity(key) => (identity.sign(message).ok(), None),
                Some(KeyRequest::Decapsulate { key, ct }) => (None, prekeys.decapsulate(key, ct)),
                _ => (None, None),
            };
            match (sig, secret) {
                (Some(s), _) => c.carrier.key_response(&mut env, KeyResponse::Signature(&s)),
                (None, Some(s)) => c.carrier.key_response(&mut env, KeyResponse::SharedSecret(s)),
                (None, None) => c.carrier.key_response(&mut env, KeyResponse::Failed),
            }
        } else {
            c.carrier.poll(&mut env, stores)
        };
        match polled {
            Ok(Poll::Idle) => Step::Idle,
            Ok(Poll::Open(peer)) => Step::Open(peer),
            Ok(Poll::Frame(f)) => {
                // vertexia: a rejected input is already counted and traced by the machine; the stream stays up
                let _ = match (c.peer, c.node, c.session) {
                    (true, Some(node), _) => sm.peer_frame(now, &node, &f, fx),
                    (false, Some(node), Some(session)) => sm.carrier_frame(now, &node, session, &f, fx),
                    _ => Ok(()),
                };
                Step::Frame
            }
            Err(e) if e.is_fatal() => Step::Dead,
            Ok(Poll::Handshake | Poll::KeyRequest) | Err(_) => Step::Progress,
        }
    }

    /// Move the handshake bytes the carrier produced into the stream's queue.
    fn transmit_handshake(&mut self, slot: usize) {
        let limit = self.limits.write_backlog;
        let Self { conns, hs, .. } = self;
        let Some(c) = conns.get_mut(slot).and_then(Option::as_mut) else {
            return;
        };
        let mut ok = true;
        while c.carrier.pending_transmit() > 0 {
            let n = c.carrier.transmit(hs);
            if n == 0 {
                break;
            }
            ok &= c.push(hs.get(..n).unwrap_or_default(), limit);
        }
        if !ok {
            self.dying(slot, Closed::Slow);
        }
    }

    fn on_open(&mut self, slot: usize, peer: NodeId, now: u64) {
        let Some(kind) = self.conn(slot).map(|c| c.kind) else {
            return;
        };
        let key = node_key(&peer);
        if self.conn(slot).is_some_and(|c| c.dialer || c.carrier.is_peer_relay()) {
            self.peer_open(slot, peer, kind);
            if self.conn(slot).is_some_and(|c| c.dying.is_some()) {
                return;
            }
        } else {
            if !self.by_node.contains_key(&key) && self.sm.sessions() >= self.limits.carriers {
                self.counters.refused_carriers_full += 1;
                self.dying(slot, Closed::Full);
                return;
            }
            let Ok(session) = self.sm.carrier_opened(now, peer, &mut self.fx) else {
                self.counters.refused_carriers_full += 1;
                self.dying(slot, Closed::Full);
                self.flush();
                return;
            };
            if let Some(c) = self.conn(slot) {
                c.node = Some(peer);
                c.session = Some(session);
            }
            self.handshaking -= 1;
            self.by_node.insert(key, slot);
            self.counters.carriers_opened += 1;
            self.event(Event::CarrierUp { node: peer, kind });
        }
        self.flush();
    }

    /// Mark a stream to be closed; the run loop drops its operations and calls [`Core::finish`].
    pub(crate) fn dying(&mut self, slot: usize, why: Closed) {
        let Some(c) = self.conn(slot) else { return };
        if c.dying.is_some() {
            return;
        }
        c.dying = Some(why);
        match why {
            Closed::Protocol => self.counters.protocol_failures += 1,
            Closed::Slow => self.counters.slow_closed += 1,
            Closed::Idle | Closed::HandshakeTimeout => self.counters.timed_out += 1,
            _ => {}
        }
    }

    /// The slots of streams that are to be closed.
    pub(crate) fn dying_slots(&self) -> impl Iterator<Item = usize> + '_ {
        self.conns
            .iter()
            .enumerate()
            .filter_map(|(i, c)| c.as_ref().filter(|c| c.dying.is_some()).map(|_| i))
    }

    /// End a stream whose operations have been dropped: tell the machine and return the stream to close.
    pub(crate) fn finish(&mut self, slot: usize, now: u64) -> Option<Rc<S>> {
        let c = self.conns.get_mut(slot)?.take()?;
        self.free.push(slot);
        let why = c.dying.unwrap_or(Closed::Peer);
        if c.node.is_none() {
            self.handshaking -= 1;
        }
        if c.peer || c.dial.is_some() {
            self.peer_closed(slot, c.node, c.dial, now);
        } else if let Some(node) = c.node {
            let key = node_key(&node);
            if self.by_node.get(&key) == Some(&slot) {
                self.by_node.remove(&key);
            }
            if let Some(session) = c.session {
                self.sm.carrier_closed(now, &node, session, &mut self.fx);
                self.flush();
            }
        }
        self.counters.carriers_closed += 1;
        self.event(Event::CarrierDown { node: c.node, why });
        Some(c.stream)
    }

    /// Mark every stream to be closed and refuse new ones.
    pub(crate) fn begin_shutdown(&mut self) {
        self.stopping = true;
        for slot in 0..self.conns.len() {
            self.dying(slot, Closed::Shutdown);
        }
    }

    /// Close every stream at once, for a run that ended: the streams are dropped here.
    pub(crate) fn abort_all(&mut self, now: u64) {
        self.begin_shutdown();
        for slot in 0..self.conns.len() {
            drop(self.finish(slot, now));
        }
        self.stopping = false;
    }

    /// Apply the effects of the machine's last call.
    fn flush(&mut self) {
        let mut fx = core::mem::take(&mut self.fx);
        for item in fx.items.drain(..) {
            match item {
                Item::Carrier(to, s, e) | Item::Peer(to, s, e) => {
                    self.send_frame(&to, fx.arena.get(s..e).unwrap_or_default());
                }
                Item::Udp(UdpTarget::Reply(addr), s, e) => self.queue_udp(addr, fx.arena.get(s..e).unwrap_or_default()),
                Item::Udp(UdpTarget::Member(node), s, e) => {
                    let addr = self.hub.as_ref().and_then(|h| h.member_addr(&node));
                    match addr {
                        Some(a) => self.queue_udp(a, fx.arena.get(s..e).unwrap_or_default()),
                        None => self.counters.datagrams_dropped += 1,
                    }
                }
                Item::Local(from, s, e) => self.local_packet(&from, fx.arena.get(s..e).unwrap_or_default()),
                Item::Close(node, session, reason) => self.close_session(&node, session, reason),
                Item::Wake(node) => self.event(Event::Wake { node }),
                Item::Trace(t) => self.trace(t),
            }
        }
        self.counters.datagrams_dropped += fx.lost;
        fx.lost = 0;
        fx.arena.clear();
        self.fx = fx;
    }

    fn local_packet(&mut self, from: &NodeId, packet: &[u8]) {
        let now = self.last_now;
        match self.hub.as_mut() {
            Some(h) => h.local_packet(now, from, packet),
            None => self.counters.hub_dropped += 1,
        }
    }

    /// Answer the hub endpoint's events and send what it wants to send.
    fn pump_hub(&mut self, now: u64) {
        for _ in 0..STEP_BUDGET {
            let mut did = false;
            let Self {
                hub, identity, notes, ..
            } = self;
            let Some(hub) = hub.as_mut() else { return };
            notes.clear();
            hub.events(now, identity, notes);
            for note in core::mem::take(&mut self.notes) {
                did = true;
                match note {
                    Note::Awake(n) => {
                        self.sm.member_returned(now, &n, &mut self.fx);
                        self.flush();
                    }
                    Note::Gone(n) => self.sm.udp_gone(&n),
                }
            }
            let mut buf = core::mem::take(&mut self.hub_tx);
            while let Some((target, len)) = self.hub.as_mut().and_then(|h| h.transmit(now, &mut buf)) {
                did = true;
                let bytes = buf.get(..len).unwrap_or_default();
                match target {
                    Target::Udp(a) => self.queue_udp(a, bytes),
                    Target::Member(n) => {
                        // vertexia: a refused packet is counted and traced by the machine
                        let _ = self.sm.send_local(now, &n, 0, bytes, &mut self.fx);
                        self.flush();
                    }
                    Target::Nowhere => self.counters.hub_dropped += 1,
                }
            }
            self.hub_tx = buf;
            if !did {
                return;
            }
        }
    }

    fn close_session(&mut self, node: &NodeId, session: SessionId, reason: CloseReason) {
        let slot = self.conns.iter().position(|c| {
            c.as_ref()
                .is_some_and(|c| c.node.as_ref() == Some(node) && c.session == Some(session))
        });
        if let Some(slot) = slot {
            self.dying(
                slot,
                match reason {
                    CloseReason::SessionTime => Closed::SessionTime,
                    CloseReason::Replaced => Closed::Replaced,
                },
            );
        }
    }

    fn trace(&mut self, t: Trace) {
        match t {
            Trace::Rejected { reason, node } => {
                let r = Reason::of(reason);
                if let Some(n) = self.counters.refused.get_mut(r as usize) {
                    *n += 1;
                }
                self.event(Event::Refused { reason: r, node });
            }
            Trace::QuotaExceeded { node } => {
                if let Some(n) = self.counters.refused.get_mut(Reason::Quota as usize) {
                    *n += 1;
                }
                self.event(Event::Refused {
                    reason: Reason::Quota,
                    node: Some(node),
                });
            }
            Trace::Pulse { node } => {
                let now = self.last_now;
                if let Some(h) = self.hub.as_mut() {
                    h.pulse(now, &node);
                }
            }
            Trace::RecordStored { node, seq, .. } => {
                self.note_record(node);
                self.event(Event::RecordStored { node, seq });
            }
            Trace::MailboxStored { node, .. } | Trace::MailboxDelivered { node, .. } => self.note_mail(node),
            _ => {}
        }
    }

    /// Seal `plain` as a frame for the stream of `to`.
    fn send_frame(&mut self, to: &NodeId, plain: &[u8]) {
        let Some(&slot) = self.by_node.get(&node_key(to)) else {
            return;
        };
        let limit = self.limits.write_backlog;
        let Self { conns, unit, .. } = self;
        let Some(c) = conns.get_mut(slot).and_then(Option::as_mut) else {
            return;
        };
        if c.dying.is_some() {
            return;
        }
        let sealed = c.carrier.seal_bytes(&Software, plain, unit);
        let Ok(n) = sealed else {
            self.dying(slot, Closed::Protocol);
            return;
        };
        let ok = c.push(unit.get(..n).unwrap_or_default(), limit);
        if !ok {
            self.dying(slot, Closed::Slow);
        }
    }

    fn queue_udp(&mut self, to: SocketAddr, bytes: &[u8]) {
        if self.udp_out.len() >= UDP_BACKLOG {
            self.counters.datagrams_dropped += 1;
            return;
        }
        let mut v = self.udp_pool.pop().unwrap_or_default();
        v.clear();
        v.extend_from_slice(bytes);
        self.udp_out.push_back((to, v));
    }

    /// The next datagram to send.
    pub(crate) fn take_udp(&mut self) -> Option<(SocketAddr, Vec<u8>)> {
        self.udp_out.pop_front()
    }

    /// A datagram sent (or failed); its buffer is kept for the next one.
    pub(crate) fn udp_sent(&mut self, ok: bool, buf: Vec<u8>) {
        if ok {
            self.counters.datagrams_out += 1;
        } else {
            self.counters.datagrams_dropped += 1;
        }
        if self.udp_pool.len() < 8 {
            self.udp_pool.push(buf);
        }
    }

    /// A datagram arrived from `src`.
    pub(crate) fn on_datagram(&mut self, now: u64, src: SocketAddr, bytes: &mut [u8]) {
        self.last_now = now;
        self.counters.datagrams_in += 1;
        let member = self.hub.as_ref().and_then(|h| h.member_at(&src));
        if bytes.first().is_some_and(|b| *b < 0x40) {
            // vertexia: the machine counts and traces a refused datagram; nothing else to do with the result
            let _ = self.sm.datagram(now, src, member.as_ref(), bytes, &mut self.fx);
            self.flush();
        } else if let Some(hub) = self.hub.as_mut() {
            if let Some(n) = member {
                let _ = self.sm.udp_heard(&n, now);
            }
            hub.handle_datagram(now, src, bytes);
        } else {
            self.counters.hub_dropped += 1;
        }
        self.pump_hub(now);
    }

    /// Run the machine's timers and the checks of stream deadlines.
    pub(crate) fn on_timeout(&mut self, now: u64) {
        self.last_now = now;
        self.sm.handle_timeout(now, &mut self.fx);
        self.flush();
        self.note_sweep();
        if let Some(h) = self.hub.as_mut() {
            h.handle_timeout(now);
        }
        self.pump_hub(now);
        if now < self.check_at {
            return;
        }
        self.check_at = now.saturating_add(CHECK_NS);
        let idle = self.limits.idle_ns;
        for slot in 0..self.conns.len() {
            let Some(c) = self.conn(slot).filter(|c| c.dying.is_none()) else {
                continue;
            };
            if c.node.is_none() && now >= c.deadline {
                self.dying(slot, Closed::HandshakeTimeout);
            } else if now.saturating_sub(c.last_rx) >= idle {
                self.dying(slot, Closed::Idle);
            }
        }
    }

    /// When the loop must call [`Core::on_timeout`].
    pub(crate) fn next_wake(&self) -> u64 {
        let hub = self.hub.as_ref().and_then(Hub::next_timeout).unwrap_or(u64::MAX);
        let dial = self.next_dial_at();
        self.sm
            .next_deadline()
            .unwrap_or(u64::MAX)
            .min(self.check_at)
            .min(hub)
            .min(dial)
    }

    pub(crate) fn store_failed(&mut self) {
        self.counters.store_errors += 1;
        self.event(Event::StoreFailed);
    }

    pub(crate) fn accept_failed(&mut self) {
        self.counters.accept_errors += 1;
    }

    /// Streams and datagrams are all gone and nothing is left to close.
    pub(crate) fn idle(&self) -> bool {
        self.conns.iter().all(Option::is_none)
    }
}
