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
use core::cell::RefCell;
use core::net::SocketAddr;

use pinc_connect::carrier::ProtectedCarrier;
use pinc_connect::carrier::session::{self, OUT_LEN, Poll};
use pinc_connect::carrier::ws::{self, Opcode, WsFrame};
use pinc_connect::relay::{CloseReason, Config, SessionId, Trace, UdpTarget};
use pinc_crypto::{Drbg, NodeId, Software};
use pinc_keystore::KeyStore;
use pinc_security::{ConnId, Env, KeyRequest, KeyResponse, LocalIdentity, PrekeyInfo, ResponderStores};
use zeroize::Zeroizing;

use super::access::Access;
use super::carriers::{Completion, Done, Tag};
use super::conn::Conn;
use super::fx::{Fx, Item};
use super::limits::{Limits, Machine};
use super::peers::{Peer, Slot};
use super::stats::{Closed, Counters, Event, Events, Reason, Stats};
use super::store::node_key;
use crate::carrier::CarrierKind;
use crate::keys::{Identity, Prekeys, is_identity};

mod keep;
mod mesh;
#[cfg(test)]
mod tests;
mod tunnel;

#[cfg(feature = "trace")]
pub(super) mod probe;

pub(crate) use keep::Job;
#[cfg(test)]
pub(crate) use keep::Mark;

/// The most control datagrams waiting for the socket.
const UDP_BACKLOG: usize = 256;
/// The most steps one stream's handshake and frames take in one call, so one stream cannot hold the loop.
const STEP_BUDGET: usize = 256;
/// The interval of the checks of stream deadlines.
const CHECK_NS: u64 = 1_000_000_000;
/// How long accepting pauses after a failed accept, in nanoseconds.
const ACCEPT_PAUSE_NS: u64 = 100_000_000;

/// What one step of a stream's carrier found.
enum Step {
    Idle,
    Progress,
    Frame,
    Open(NodeId),
    Dead,
    Gone,
}

pub(crate) struct Core<S, K: KeyStore, A> {
    pub(crate) sm: Box<Machine>,
    pub(crate) conns: Vec<Option<Conn<S>>>,
    free: Vec<usize>,
    by_node: BTreeMap<[u8; 33], usize>,
    identity: Rc<RefCell<Identity<K>>>,
    access: A,
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
    /// Slots with a read or a write to start, and slots to close: the loop works through these and never scans the
    /// streams (only the timer checks every carrier's deadlines, once a second).
    pub(crate) submit: Vec<usize>,
    reap: Vec<(usize, u64)>,
    next_conn: u64,
    live: usize,
    accept_out: bool,
    accept_pause: u64,
    pub(crate) stopping: bool,
    hub: Option<tunnel::Tunnel>,
    last_now: u64,
}

#[inline(never)]
fn new_machine(cfg: Config) -> Box<Machine> {
    Box::new(Machine::new(cfg))
}

impl<S, K: KeyStore, A: Access> Core<S, K, A> {
    pub(crate) fn new(
        identity: Rc<RefCell<Identity<K>>>,
        access: A,
        peers: &[Peer],
        limits: Limits,
        tunnel: Option<SocketAddr>,
        now: u64,
    ) -> crate::Result<Self> {
        let mut seed = [0u8; 32];
        let mut key = [0u8; 8];
        let (id, local) = {
            let mut ident = identity.borrow_mut();
            ident.random(&mut seed)?;
            ident.random(&mut key)?;
            (ident.node_id(), ident.local()?)
        };
        let mut cfg = Config::new(id, u64::from_le_bytes(key));
        cfg.quota = limits.quota;
        cfg.mailbox_max_age_ns = limits.mailbox_max_age_ns;
        let mut entropy = Zeroizing::new([0u8; 32]);
        identity.borrow_mut().random(entropy.as_mut_slice())?;
        let mut prekeys = Prekeys::new(*entropy);
        let dial_prekey = prekeys.rotate(now, &mut |out| identity.borrow_mut().random(out))?;
        let peers = mesh::slots(&id, peers, now);
        Ok(Self {
            sm: new_machine(cfg),
            conns: Vec::new(),
            free: Vec::new(),
            by_node: BTreeMap::new(),
            identity,
            access,
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
            unit: alloc::vec![0; pinc_connect::carrier::MAX_FRAME_LEN + 64],
            hs: alloc::vec![0; OUT_LEN],
            handshaking: 0,
            check_at: now.saturating_add(CHECK_NS),
            udp_out: VecDeque::new(),
            udp_pool: Vec::new(),
            keep: keep::Keep::default(),
            submit: Vec::new(),
            reap: Vec::new(),
            next_conn: 0,
            live: 0,
            accept_out: false,
            accept_pause: 0,
            stopping: false,
            hub: tunnel.map(tunnel::Tunnel::new),
            last_now: now,
        })
    }

    pub(crate) fn identity(&self) -> Rc<RefCell<Identity<K>>> {
        Rc::clone(&self.identity)
    }

    pub(crate) const fn now_hint(&self) -> u64 {
        self.last_now
    }

    pub(crate) fn node_id(&self) -> NodeId {
        self.identity.borrow().node_id()
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
            wakes: c.wakes,
            stream_ops: c.stream_ops,
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
            hub_sessions: self.hub.as_ref().map_or(0, tunnel::Tunnel::sessions),
            carriers_denied: c.carriers_denied,
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
        if self.stopping {
            self.accept_failed();
            return Err(stream);
        }
        if self.handshaking >= self.limits.handshaking {
            self.counters.refused_handshakes_full += 1;
            return Err(stream);
        }
        self.scid += 1;
        // eight bytes of a counter that is at least one are always a valid connection id
        let Some(scid) = ConnId::new(&self.scid.to_be_bytes()) else {
            self.accept_failed();
            return Err(stream);
        };
        // the carrier names are constants: this fails only if the relay cannot build a session, not for the peer's fault
        let Ok(cfg) = session::responder_config(self.local, scid) else {
            self.accept_failed();
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
    fn place(&mut self, mut conn: Conn<S>) -> usize {
        self.next_conn += 1;
        conn.id = self.next_conn;
        self.live += 1;
        let slot = match self.free.pop() {
            Some(slot) if self.conns.get(slot).is_some() => {
                if let Some(entry) = self.conns.get_mut(slot) {
                    *entry = Some(conn);
                }
                slot
            }
            _ => {
                self.conns.push(Some(conn));
                self.conns.len() - 1
            }
        };
        self.mark(slot);
        slot
    }

    /// The stream in `slot` has an operation to start: a read to repeat, or bytes to write.
    pub(crate) fn mark(&mut self, slot: usize) {
        let Some(c) = self.conn(slot) else { return };
        if !c.queued {
            c.queued = true;
            self.submit.push(slot);
        }
    }

    /// The tag of an operation on the stream in `slot`.
    pub(crate) fn tag(&self, slot: usize) -> Tag {
        let id = self.conns.get(slot).and_then(Option::as_ref).map_or(0, |c| c.id);
        Tag::new(id << 16 | slot as u64)
    }

    /// The slot a tag names, if its stream is still the one the operation was started on.
    fn slot_of(&self, tag: Tag) -> Option<usize> {
        let slot = usize::try_from(tag.conn() & 0xffff).ok()?;
        let c = self.conns.get(slot)?.as_ref()?;
        (c.id == tag.conn() >> 16).then_some(slot)
    }

    /// The next stream with an operation to start; `take_read` and `take_write` give the operations.
    pub(crate) fn pop_submit(&mut self) -> Option<usize> {
        let slot = self.submit.pop()?;
        if let Some(c) = self.conn(slot) {
            c.queued = false;
        }
        Some(slot)
    }

    /// The next stream to close.
    pub(crate) fn pop_reap(&mut self) -> Option<usize> {
        while let Some((slot, id)) = self.reap.pop() {
            if self
                .conns
                .get(slot)
                .and_then(Option::as_ref)
                .is_some_and(|c| c.id == id)
            {
                return Some(slot);
            }
        }
        None
    }

    /// Whether the loop should submit an accept.
    pub(crate) fn want_accept(&mut self, now: u64) -> bool {
        let want = !self.accept_out && !self.stopping && now >= self.accept_pause;
        self.accept_out |= want;
        want
    }

    /// Whether accepting waits for a time after a failed accept.
    pub(crate) fn accept_paused(&self, now: u64) -> bool {
        !self.accept_out && !self.stopping && self.accept_pause > now
    }

    /// When accepting resumes after a failed accept.
    pub(crate) const fn accept_resume(&self) -> u64 {
        self.accept_pause
    }

    /// A finished operation; the stream to close, if one was refused.
    pub(crate) fn complete(&mut self, c: Completion<S>, now: u64) -> Option<(Tag, Rc<S>)> {
        let tag = c.tag;
        self.counters.stream_ops += 1;
        match c.done {
            Done::Accepted(r) => {
                self.accept_out = false;
                if let Ok((s, kind)) = r {
                    self.add_conn(s, kind, now).err().map(|s| (tag, Rc::new(s)))
                } else {
                    self.accept_failed();
                    self.accept_pause = now.saturating_add(ACCEPT_PAUSE_NS);
                    None
                }
            }
            Done::Opened(r) => {
                let i = usize::try_from(tag.conn()).unwrap_or(usize::MAX);
                if let Ok(s) = r {
                    let kind = self
                        .peers
                        .get(i)
                        .and_then(|p| p.peer.kind())
                        .unwrap_or(CarrierKind::Tcp);
                    self.dialed(i, s, kind, now).err().map(|s| (tag, Rc::new(s)))
                } else {
                    self.dial_failed(i, now);
                    None
                }
            }
            Done::Read(r, buf) => {
                if let Some(slot) = self.slot_of(tag) {
                    self.on_read(slot, now, r, buf);
                }
                None
            }
            Done::Written(r, buf) => {
                if let Some(slot) = self.slot_of(tag) {
                    self.on_write(slot, r, buf);
                }
                None
            }
        }
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
                self.mark(slot);
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
        self.mark(slot);
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
                        c.push_pong(f.get(..len).unwrap_or_default());
                        self.mark(slot);
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
                Some(KeyRequest::Sign { key, message, .. }) if is_identity(key) => {
                    (identity.borrow_mut().sign(message).ok(), None)
                }
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
        if ok {
            self.mark(slot);
        } else {
            self.dying(slot, Closed::Slow);
        }
    }

    fn on_open(&mut self, slot: usize, peer: NodeId, now: u64) {
        let Some(kind) = self.conn(slot).map(|c| c.kind) else {
            return;
        };
        let key = node_key(&peer);
        let mut replaced = None;
        if self.conn(slot).is_some_and(|c| c.dialer || c.carrier.is_peer_relay()) {
            self.peer_open(slot, peer, kind);
            if self.conn(slot).is_some_and(|c| c.dying.is_some()) {
                return;
            }
        } else {
            if !self.access.admit(&peer) {
                self.counters.carriers_denied += 1;
                self.dying(slot, Closed::Denied);
                return;
            }
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
            // the machine closes the session this one replaces, which names the node's new slot: the old carrier is
            // closed here, by the slot the table held
            replaced = self
                .by_node
                .insert(key, slot)
                .filter(|&old| old != slot && self.conn(old).is_some_and(|c| c.session.is_some()));
            self.counters.carriers_opened += 1;
            self.event(Event::CarrierUp { node: peer, kind });
        }
        if let Some(old) = replaced {
            self.dying(old, Closed::Replaced);
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
        let id = c.id;
        self.reap.push((slot, id));
        match why {
            Closed::Protocol => self.counters.protocol_failures += 1,
            Closed::Slow => self.counters.slow_closed += 1,
            Closed::Idle | Closed::HandshakeTimeout => self.counters.timed_out += 1,
            _ => {}
        }
    }

    /// End a stream whose operations have been dropped: tell the machine and return the stream to close.
    pub(crate) fn finish(&mut self, slot: usize, now: u64) -> Option<Rc<S>> {
        let c = self.conns.get_mut(slot)?.take()?;
        self.free.push(slot);
        self.live -= 1;
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
        // the accept in flight was dropped with the run: the next run asks again
        self.accept_out = false;
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
                    self.queue_member_udp(&node, fx.arena.get(s..e).unwrap_or_default());
                }
                Item::Local(from, s, e) => self.queue_local(&from, fx.arena.get(s..e).unwrap_or_default()),
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

    fn close_session(&mut self, node: &NodeId, session: SessionId, reason: CloseReason) {
        let named = |c: &Option<Conn<S>>| {
            c.as_ref()
                .is_some_and(|c| c.node.as_ref() == Some(node) && c.session == Some(session))
        };
        // a replaced carrier is no longer the node's entry (its replacement is): `on_open` closed it already
        let slot = self
            .by_node
            .get(&node_key(node))
            .copied()
            .filter(|&s| self.conns.get(s).is_some_and(named));
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
            Trace::Pulse { node } => self.queue_pulse(node),
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
        if ok {
            self.mark(slot);
        } else {
            self.dying(slot, Closed::Slow);
        }
    }

    pub(crate) fn queue_udp(&mut self, to: SocketAddr, bytes: &[u8]) {
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

    /// A datagram arrived from `src`, which the hub endpoint knows as `member`. Whether it was the relay's own (the
    /// machine took it); if not, the endpoint's owner takes it.
    pub(crate) fn on_datagram(&mut self, now: u64, src: SocketAddr, member: Option<NodeId>, bytes: &mut [u8]) -> bool {
        self.last_now = now;
        self.counters.datagrams_in += 1;
        if let Some(n) = member.as_ref() {
            self.fx.set_direct(n, true);
        }
        if bytes.first().is_some_and(|b| *b < 0x40) {
            // vertexia: the machine counts and traces a refused datagram; nothing else to do with the result
            let _ = self.sm.datagram(now, src, member.as_ref(), bytes, &mut self.fx);
            self.flush();
            return true;
        }
        if self.hub.is_none() {
            self.counters.hub_dropped += 1;
        }
        false
    }

    /// The endpoint read a session packet from the validated direct address of `member` (asked after the read): the
    /// member's UDP session was heard now. Asked after the read, the packet that validated the address, or that moved
    /// the session onto it, counts, as the reference model stamps the path a packet came in on. This is the one call
    /// per packet that stamps and releases what the member's mailbox holds; it flushes only when it emitted something.
    pub(crate) fn on_heard(&mut self, now: u64, member: Option<NodeId>) {
        let Some(n) = member else { return };
        self.fx.set_direct(&n, true);
        if self.hub.is_some() {
            // vertexia: the machine counts and traces a refused stamp; the effects of a released message go out here
            let _ = self.sm.udp_heard(now, &n, &mut self.fx);
            if self.fx.pending() {
                self.flush();
            }
        }
    }

    /// Run the machine's timers and the checks of stream deadlines.
    pub(crate) fn on_timeout(&mut self, now: u64) {
        self.last_now = now;
        self.sm.handle_timeout(now, &mut self.fx);
        self.flush();
        self.note_sweep(now);
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
        let dial = self.next_dial_at();
        self.sm
            .next_deadline()
            .unwrap_or(u64::MAX)
            .min(self.check_at)
            .min(dial)
            .min(self.keep_wake())
    }

    pub(crate) fn store_failed(&mut self) {
        self.counters.store_errors += 1;
        self.event(Event::StoreFailed);
    }

    /// A packet for the relay's own endpoint or a member was dropped before the relay could take it.
    pub(crate) fn hub_lost(&mut self) {
        self.counters.hub_dropped += 1;
    }

    pub(crate) fn accept_failed(&mut self) {
        self.counters.accept_errors += 1;
    }

    /// Streams and datagrams are all gone and nothing is left to close.
    pub(crate) fn idle(&self) -> bool {
        self.live == 0
    }
}
