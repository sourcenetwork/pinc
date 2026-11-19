//! Datagrams in: find the session a datagram belongs to, or decide whether it may create one.
//!
//! The destination connection id of the first packet picks the candidates in the demultiplexing table. One
//! candidate owns the datagram; several (two sessions derived the same four bytes) are tried in turn on a copy of the
//! datagram, because opening a packet changes the bytes in place. For a short datagram the first holder that does
//! not answer undecryptable or unroutable owns it, whatever it did with it (a closed or back-pressured holder takes
//! it too); a long packet is offered to each holder, oldest first, until one owns it (one that refuses a handshake
//! message, has ended or only added a part to a message not complete yet does not, so the parts of a Finish reach every
//! holder), and a first flight that every holder says differs from its own gets a
//! half-open session of its own under the same id, up to four holders, so a forged flight never displaces the first.
//! The candidate list can name the same slot twice, which only costs a second trial. An id no session holds can only
//! start a session if the datagram is a first handshake message that meets its size floor
//! (1200 bytes for a full Initial, 464 for a short one, 93 for a Hello) and fewer than 256 sessions are
//! unauthenticated; a ticket resumption Hello is exempt from the count only when its ticket opens under this node's
//! ticket store and is unused (single use), checked before any state is held, because that binder proves a past
//! session. A short Initial and a Hello are screened first (`screen_first`): one the responder would only reject (a
//! prekey or ticket this node does not hold) is answered by the endpoint without a session (`stateless`), one it would
//! not answer at all is dropped, and neither takes a half-open slot. Every server session a first flight makes is owed to
//! the host until the host reads its `Incoming` (`session_taken`) or it ends, and while the owed sessions fill the room
//! the host has left to accept them (`set_backlog_room`) no first flight starts one, before a ticket is opened and with
//! nothing kept, so a session that finishes its handshake always has a place to wait. Of that room the sessions that
//! count towards the 256 hold at most half (rounded up), so first flights that never finish cannot reserve all of it
//! and a peer that resumes with a ticket still finds a place. A later part of a first message that arrives before
//! the part that starts it is held for a moment in the endpoint's small table of such datagrams (see `orphan`) and
//! handed to the session once the first part has created it.
//!
//! Invariants: a datagram larger than [`MAX_DATAGRAM`] or shorter than a header is dropped and counted; a datagram
//! that cannot create a session, matches none and is not held is dropped and counted; the copy used for trials and
//! the held datagrams are the only extra buffers, held inside the endpoint.

use core::net::SocketAddr;

use pinc_security::message::{FULL_INITIAL_MIN, MAX_MESSAGE_LEN, MessageType, RESUME_HELLO_MIN, SHORT_INITIAL_MIN};
use pinc_security::responder::{Screen, screen_first};
use pinc_security::{AeadSet, ConnId, Env, Failure};
use pinc_transport::conn::{Connection, Drop, PathId, ServerParams, connect_limit};
use pinc_transport::packet::{LongHeader, LongType, short_dcid};
use pinc_wire::Reader;

use crate::endpoint::{CID_LEN, MAX_DATAGRAM, env, ep_impl};
use crate::orphan::ORPHAN_MAX;
use crate::relay_net::is_relay_addr;
use crate::slot::State;
use crate::trace::trace;

/// The most sessions that may hold the same four bytes and still be tried.
const MAX_CANDIDATES: usize = 4;
/// The most unauthenticated sessions.
pub const MAX_HALF_OPEN: usize = 256;
/// How long an unauthenticated session lives on a node that is not thin (30 s), until it answers as a responder. It
/// lives as long as an unestablished handshake may last ([`connect_limit`]), so a thin node keeps it twice as long.
pub const HALF_OPEN_LIFE: u64 = connect_limit(false);
/// How long an unauthenticated session lives once it answered as a responder (60 s, the transport's
/// [`RESPONDER_HOLD`](pinc_transport::conn::RESPONDER_HOLD)), whatever the node is: a slow dialer's Finish still finds
/// it. The half-open cap bounds the cost at [`MAX_HALF_OPEN`] times this hold.
pub const HALF_OPEN_HOLD: u64 = pinc_transport::conn::RESPONDER_HOLD;

/// What the first packet of an unroutable datagram says.
struct First<'a> {
    odcid: ConnId,
    /// The id the dialer chose for itself.
    scid: ConnId,
    /// The length of the whole message.
    total: u64,
    kind: MessageType,
    /// The whole message when this packet carries all of it.
    message: Option<&'a [u8]>,
}

/// The destination id of the first packet of a datagram, and whether it is a long header.
fn peek(buf: &[u8]) -> Option<(ConnId, bool)> {
    let first = *buf.first()?;
    if first & 0x80 == 0 {
        short_dcid(buf, CID_LEN).ok().map(|d| (d, false))
    } else {
        LongHeader::parse(buf).ok().map(|(h, _)| (h.dcid, true))
    }
}

/// The destination id and first message type of a long Handshake packet that starts a message.
fn classify(buf: &[u8]) -> Option<First<'_>> {
    let (h, hlen) = LongHeader::parse(buf).ok()?;
    if h.ty != LongType::Handshake {
        return None;
    }
    let body = buf.get(hlen..hlen.checked_add(h.body_len)?)?;
    let mut r = Reader::new(body);
    let total = r.read_varint().ok()?;
    let off = r.read_varint().ok()?;
    if off != 0 || total == 0 {
        return None;
    }
    let data = r.read_bytes(r.remaining()).ok()?;
    let kind = MessageType::of(&[*data.first()?]).ok()?;
    let message = usize::try_from(total).ok().and_then(|t| data.get(..t));
    Some(First {
        odcid: h.dcid,
        scid: h.scid,
        total,
        kind,
        message,
    })
}

/// The destination id and message length of a long Handshake packet that carries a part of a message other than its
/// start.
fn later_part(buf: &[u8]) -> Option<(ConnId, u64)> {
    let (h, hlen) = LongHeader::parse(buf).ok()?;
    if h.ty != LongType::Handshake {
        return None;
    }
    let body = buf.get(hlen..hlen.checked_add(h.body_len)?)?;
    let mut r = Reader::new(body);
    let total = r.read_varint().ok()?;
    let off = r.read_varint().ok()?;
    let plausible = off != 0 && off < total && usize::try_from(total).is_ok_and(|t| t <= MAX_MESSAGE_LEN);
    plausible.then_some((h.dcid, total))
}

ep_impl! {
    /// Process a datagram that arrived on `local` from `remote`. The bytes are changed in place. Nothing is returned:
    /// what the datagram caused shows in [`poll_transmit`](Self::poll_transmit), [`poll_event`](Self::poll_event) and
    /// [`poll_timeout`](Self::poll_timeout).
    pub fn handle_datagram(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        self.last_now = now;
        self.counters.datagrams_in += 1;
        if buf.is_empty() || buf.len() > MAX_DATAGRAM {
            self.counters.dropped_in += 1;
            return;
        }
        self.rx_held = self.ledger.on_receive(remote, buf.len() as u64);
        trace!(self, now, LedgerRx {
            addr: addr_key(&remote),
            rx: self.ledger.get(&remote).map_or(0, |e| e.rx),
        });
        let Some((dcid, long)) = peek(buf) else {
            self.counters.dropped_in += 1;
            return;
        };
        let (found, n) = self.demux.matches::<MAX_CANDIDATES>(&dcid);
        trace!(self, now, Demux {
            slot: found.first().copied().flatten().map_or(u64::MAX, u64::from),
            candidates: n as u64,
        });
        match n {
            0 => self.unrouted(now, local, remote, buf),
            // A long packet is not sealed: each holder is offered it in turn and the one it belongs to takes it.
            _ if long && n < MAX_CANDIDATES && self.starts_held_message(now, remote, buf) => {
                self.unrouted(now, local, remote, buf);
            }
            _ if long => self.offer(&found, n, now, local, remote, buf),
            1 => {
                if let Some(i) = found.first().copied().flatten() {
                    // A drop reason is counted by the connection itself.
                    let _ = self.deliver(i as usize, now, local, remote, buf);
                }
            }
            _ => self.trial(&found, now, local, remote, buf),
        }
    }

    /// Try each session that holds the id on a fresh copy; the first whose keys open the packet owns it.
    fn trial(&mut self, found: &[Option<u32>], now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        let len = buf.len();
        if let Some(d) = self.scratch.get_mut(..len) {
            d.copy_from_slice(buf);
        }
        for (k, i) in found.iter().flatten().enumerate() {
            if k > 0 {
                match self.scratch.get(..len) {
                    Some(s) => buf.copy_from_slice(s),
                    None => return,
                }
            }
            let r = self.deliver(*i as usize, now, local, remote, buf);
            let mine = !matches!(r, Err(Drop::Undecryptable | Drop::Unroutable));
            trace!(self, now, Trial { slot: u64::from(*i), ok: u64::from(mine) });
            if mine {
                return;
            }
        }
        self.counters.dropped_in += 1;
    }

    /// Offer a long packet to each of the `n` sessions that hold its id, oldest first, until one owns it: a holder
    /// that refuses a handshake message (a Finish it does not authenticate, a first flight other than its own) or
    /// cannot open it, or has ended, does not own it, and neither does one that only added a part to a message that is
    /// not complete yet, since the parts of a Finish reach every holder and only the one whose key opens the whole
    /// message takes it. When every live holder says the packet is a first flight different from its own, the packet
    /// is the start of another dial under the same id and gets a session of its own, unless the id already has
    /// [`MAX_CANDIDATES`] holders. An id with one holder gets that one delivery and nothing else.
    fn offer(&mut self, found: &[Option<u32>], n: usize, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        let len = buf.len();
        let Some(copy) = self.scratch.get_mut(..len) else { return };
        copy.copy_from_slice(buf);
        let (mut different, mut other, mut parted) = (false, false, false);
        // The table lists the newest holder first; the first holder of an id is never displaced, so it is asked first.
        for (k, i) in found.iter().flatten().rev().enumerate() {
            if k > 0 {
                match self.scratch.get(..len) {
                    Some(s) => buf.copy_from_slice(s),
                    None => return,
                }
            }
            let r = self.deliver(*i as usize, now, local, remote, buf);
            let refused = matches!(r, Err(Drop::Handshake(_) | Drop::Closed | Drop::Undecryptable));
            let part = n > 1 && r.is_ok() && self.took_part(*i as usize);
            if n > 1 {
                trace!(self, now, Trial { slot: u64::from(*i), ok: u64::from(!refused && !part) });
            }
            if part {
                parted = true;
                continue;
            }
            if !refused {
                return;
            }
            match r {
                Err(Drop::Handshake(Failure::DifferentFirst)) => different = true,
                Err(Drop::Closed) => {}
                _ => other = true,
            }
        }
        if !different || other || parted {
            return;
        }
        match self.scratch.get(..len) {
            Some(s) => buf.copy_from_slice(s),
            None => return,
        }
        if classify(buf).is_none() {
            // A later part that completed a message other than every holder's: it waits for the start of that message,
            // which then gets a session of its own (see `starts_held_message`).
            let held = later_part(buf)
                .is_some_and(|(dcid, total)| self.orphans.hold(now, dcid, total, local, remote, buf));
            self.counters.dropped_in += u64::from(!held);
        } else if n >= MAX_CANDIDATES {
            self.counters.dropped_in += 1;
            self.counters.holders_refused += 1;
        } else {
            self.unrouted(now, local, remote, buf);
        }
    }

    /// Whether session `i` only added a part to a handshake message from the datagram it was just given.
    fn took_part(&mut self, i: usize) -> bool {
        self.slots
            .get_mut(i)
            .and_then(|s| s.conn.as_mut())
            .is_some_and(Connection::take_handshake_part)
    }

    /// Whether `buf` starts a first message whose later part the endpoint holds: every session that holds the id has
    /// refused that part as a different message, so the start gets a session of its own, which the part then joins.
    fn starts_held_message(&self, now: u64, remote: SocketAddr, buf: &[u8]) -> bool {
        classify(buf).is_some_and(|f| self.orphans.holds(now, &f.odcid, f.total, &remote))
    }

    /// Hand a datagram to session `i`, then bring the endpoint's view of it up to date.
    fn deliver(
        &mut self,
        i: usize,
        now: u64,
        local: SocketAddr,
        remote: SocketAddr,
        buf: &mut [u8],
    ) -> Result<(), Drop> {
        let pid = self.path_id(local, remote);
        let Some(slot) = self.slots.get_mut(i) else { return Err(Drop::Unroutable) };
        let Some(conn) = slot.conn.as_mut() else { return Err(Drop::Closed) };
        // Back-pressure: while the session's held events are all unrecoverable, or the host's queue is near full of
        // events it cannot recover, the connection refuses packets that would raise an event, and the peer sends them
        // again. Packets that raise none (ACK, CLOSE) are still taken.
        conn.set_gated(slot.m.held.stalled() || self.events.stalled());
        let mut env = env!(self, now);
        let r = conn.handle_datagram_with(&mut env, &mut self.stores, pid, buf);
        self.counters.stalled_in += u64::from(r == Err(Drop::Gated));
        let returned = conn.take_rejoined();
        if r.is_ok() {
            // An established session's packets are authenticated: a sub-session reported at once hears its peer here.
            // `drain` tells the application: a packet taken while the host leaves events unread raises nothing.
            if slot.m.announced && !slot.m.answered && slot.m.state == State::Established {
                slot.m.answered = true;
                slot.m.answer_due = true;
            }
            // The connection took the path of a first packet to be direct; the address says if it is a relay's.
            if is_relay_addr(&remote) {
                conn.set_path_info(pid, crate::commands::path_info(&remote, self.cfg.conn.interface_mtu));
            }
            slot.m.last_rx = now;
            if let Some(p) = slot.m.stamp(pid) {
                p.rx = now;
            }
            // Only a validated direct path counts: a short Initial is not for a node that hears no UDP and reaches its
            // peers through a carrier.
            if conn.path_validated(pid) && !is_relay_addr(&remote) {
                self.udp_heard = Some(now);
            }
        }
        // A source the ledger does not hold, on a session with no held path, has nothing to set: nothing is looked up.
        if self.rx_held || conn.has_held_paths() {
            conn.set_path_held(pid, self.rx_held);
        }
        self.settle(i, now);
        if let Some((path, rtt)) = returned {
            self.share_rejoin(i, path, rtt, now);
        }
        r
    }

    /// Session `i` found the address of `path` working again after it abandoned it: the peer's other sessions that wait
    /// for the same address take it back at once.
    fn share_rejoin(&mut self, i: usize, path: PathId, rtt: u64, now: u64) {
        let Some(peer) = self.slots.get(i).and_then(|s| s.m.peer) else { return };
        let mut at = self.by_peer.get(&peer).copied();
        while let Some(idx) = at {
            let Some(s) = self.slots.get_mut(idx as usize) else { break };
            at = Some(s.m.peer_next).filter(|n| *n != crate::slot::NIL);
            if idx as usize == i || s.m.state != State::Established {
                continue;
            }
            if s.conn.as_mut().is_some_and(|c| c.path_returned(path, rtt, now)) {
                self.settle(idx as usize, now);
            }
        }
    }

    /// A datagram for an id no session holds: it may start a server session.
    fn unrouted(&mut self, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        // Back-pressure: a new session raises events; with the host's queue near full of events it cannot recover,
        // none starts.
        if self.events.stalled() {
            self.counters.stalled_in += 1;
            return;
        }
        let Some(first) = classify(buf) else {
            // A later part of a first message that overtook the part that starts it waits a moment for its session.
            let held = later_part(buf)
                .is_some_and(|(dcid, total)| self.orphans.hold(now, dcid, total, local, remote, buf));
            self.counters.dropped_in += u64::from(!held);
            return;
        };
        let floor = match first.kind {
            MessageType::Initial => FULL_INITIAL_MIN,
            MessageType::ShortInitial => SHORT_INITIAL_MIN,
            MessageType::ResumeHello => RESUME_HELLO_MIN,
            _ => {
                self.counters.dropped_in += 1;
                return;
            }
        };
        // A first packet under the least its type has is never admitted: it costs the sender less than the session.
        if buf.len() < floor {
            self.counters.first_too_short += 1;
            self.counters.dropped_in += 1;
            self.note_first(now, 0, false);
            return;
        }
        // Back-pressure: every session this node owes its host would have to wait to be accepted, so while they fill
        // the room the host has left none starts, before a ticket is opened and with nothing kept (the holders of the
        // flight's id are left as they are); the dialer sends the flight again on its own timer.
        if self.owed >= self.backlog_room {
            self.counters.backlog_refused += 1;
            self.note_first(now, 0, false);
            return;
        }
        let resume = match first.kind {
            MessageType::ShortInitial | MessageType::ResumeHello => match self.screen(now, &first) {
                Screen::Admit { resume } => resume,
                Screen::Reject(message) => {
                    self.note_first(now, 2, false);
                    self.reject_stateless(now, local, remote, (first.odcid, first.scid), &message);
                    return;
                }
                Screen::Drop => {
                    self.counters.dropped_in += 1;
                    self.note_first(now, 3, false);
                    return;
                }
            },
            _ => false,
        };
        // Sessions whose peer is not authenticated yet hold at most half of that room (rounded up): what first flights
        // that never finish can reserve leaves the other half to peers that resume with a ticket.
        let cap = MAX_HALF_OPEN.min(self.backlog_room.div_ceil(2));
        let admitted = resume || self.half_open < cap;
        self.note_first(now, u64::from(admitted), resume);
        if !admitted {
            self.counters.dropped_in += 1;
            return;
        }
        let (odcid, total) = (first.odcid, first.total);
        let Some(i) = self.accept(now, odcid, resume) else {
            self.counters.dropped_in += 1;
            return;
        };
        // A drop reason is counted by the connection itself.
        let _ = self.deliver(i, now, local, remote, buf);
        self.replay_held(i, now, odcid, total, remote);
    }

    /// Give session `i`, just created by the first part of a message of `total` bytes for `odcid` from `remote`, the
    /// later parts of that message held from the same address, oldest first, while the session lives.
    fn replay_held(&mut self, i: usize, now: u64, odcid: ConnId, total: u64, remote: SocketAddr) {
        let id = self.session_id(i);
        let mut held = [0u8; ORPHAN_MAX];
        while self.slot_of(id).is_some() {
            let Some((local, n)) = self.orphans.take(now, &odcid, total, &remote, &mut held) else { return };
            if let Some(d) = held.get_mut(..n) {
                // A drop reason is counted by the connection itself.
                let _ = self.deliver(i, now, local, remote, d);
            }
        }
    }

    /// Record the decision on a first message: `admitted` 1 a session may start, 0 refused (the floor, the room or the
    /// cap), 2 answered with a reject because the prekey or ticket is not held, 3 dropped without an answer.
    #[cfg_attr(
        not(feature = "trace"),
        allow(unused_variables, clippy::unused_self, reason = "only the trace reads them")
    )]
    fn note_first(&mut self, now: u64, admitted: u64, resume: bool) {
        trace!(self, now, HalfOpen {
            admitted,
            half_open: self.half_open as u64,
            resume: u64::from(resume),
            room: self.backlog_room.min(i32::MAX as usize) as u64,
            owed: self.owed as u64,
        });
    }

    /// What the responder would do with the first message of `first`: a message that is not whole in its first packet
    /// is dropped (a short Initial and a Hello are never longer than a datagram). Without a protocol registered
    /// nothing is admitted either.
    fn screen(&mut self, now: u64, first: &First<'_>) -> Screen {
        let (Some(message), Some(alpns)) = (first.message, self.alpn_list()) else { return Screen::Drop };
        let own = AeadSet::offer(self.provider.capabilities());
        screen_first(&mut self.stores, &alpns, own, now, first.kind, message)
    }

    /// Create the server session for a first handshake message.
    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    fn accept(&mut self, now: u64, odcid: ConnId, resume: bool) -> Option<usize> {
        let alpns = self.alpn_list()?;
        let (i, mem) = self.alloc_slot(false, now)?;
        let cfg = self.conn_config(None);
        let params = ServerParams {
            identity: self.identity,
            alpns,
            tickets_per_session: self.cfg.tickets_per_session,
            ticket_lifetime_s: self.cfg.ticket_lifetime_s,
        };
        let mut env: Env<'_, P> = env!(self, now);
        let Ok(conn) = Connection::server(cfg, &params, mem, &mut env) else {
            self.retire_slot(i);
            return None;
        };
        if !self.register_cid(i, odcid) {
            // The table is full: there is no room to route this session, so it is not created.
            if let Some(slot) = self.slots.get_mut(i) {
                slot.conn = Some(conn);
            }
            self.free_slot(i, now);
            return None;
        }
        let slot = self.slots.get_mut(i)?;
        slot.conn = Some(conn);
        slot.m.odcid = Some(odcid);
        slot.m.unauth = true;
        slot.m.owed = true;
        slot.m.half_open = !resume;
        self.owed += 1;
        if !resume {
            self.half_open += 1;
        }
        self.sync_cids(i, true);
        trace!(self, now, Session { slot: i as u64, step: 0, dialer: 0 });
        Some(i)
    }

    /// How many more sessions the host can take waiting to be accepted. While the server sessions this node owes the
    /// host ([`NodeStats::owed`](crate::NodeStats::owed)) would fill it, a first flight is refused before any work and
    /// nothing is kept for it (counted in [`NodeStats::backlog_refused`](crate::NodeStats::backlog_refused)); the
    /// dialer sends it again on its own timer. A host that sets a room calls [`session_taken`](Self::session_taken) for
    /// every [`Event::Incoming`](crate::Event::Incoming) it reads, so every session that finishes its handshake has a
    /// place to wait. Sessions whose peer is not authenticated yet hold at most half of the room (rounded up, and
    /// never more than [`MAX_HALF_OPEN`]): a flood of first flights that never finish, each of which keeps its place
    /// for [`HALF_OPEN_LIFE`] (for [`HALF_OPEN_HOLD`] once it answered), leaves the rest to peers that resume with a
    /// ticket. Unlimited until set.
    pub const fn set_backlog_room(&mut self, room: usize) {
        self.backlog_room = room;
    }

    /// The host read the `Incoming` of server session `id`: this node no longer owes it, and the answer says whether
    /// the host keeps a place for it. A session that ended before the host read its `Incoming` stopped being owed when
    /// it ended; it is [`Taken::Gone`] and gets no place (its `Closed` follows).
    pub fn session_taken(&mut self, id: crate::SessionId) -> Taken {
        let Some(slot) = self.slot_of(id).and_then(|i| self.slots.get_mut(i)) else { return Taken::Gone };
        if !slot.m.owed {
            return Taken::Unreserved { owed: self.owed };
        }
        slot.m.owed = false;
        self.owed = self.owed.saturating_sub(1);
        Taken::Reserved
    }
}

/// What [`Endpoint::session_taken`](crate::Endpoint::session_taken) found.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Taken {
    /// A session its first flight made under the room
    /// ([`Endpoint::set_backlog_room`](crate::Endpoint::set_backlog_room)): its place was held for it.
    Reserved,
    /// A live session no first flight made (a sub-session its peer opened inside a session it already has): no place
    /// was held for it, and `owed` places are held for the sessions this node still owes, which it must not take.
    Unreserved {
        /// The sessions this node still owes the host.
        owed: usize,
    },
    /// The session ended before the host read its `Incoming`.
    Gone,
}

/// What the half-open bookkeeping holds for one slot in use, for trace validation (cargo feature `trace`).
#[cfg(feature = "trace")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HalfOpenSlot {
    /// When the session was created.
    pub created: u64,
    /// The peer is not authenticated yet, so the session ends `life` after `created`.
    pub unauth: bool,
    /// How long the session lives while unauthenticated: the node's connect limit ([`HALF_OPEN_LIFE`], twice that on a
    /// thin node), and at least [`HALF_OPEN_HOLD`] once it answered. Never above [`HALF_OPEN_HOLD`].
    pub life: u64,
    /// The session counts against [`MAX_HALF_OPEN`].
    pub counted: bool,
    /// The deadline the session holds in the endpoint's heap.
    pub deadline: Option<u64>,
    /// A server session the host has not taken yet (`session_taken`), counted in `NodeStats::owed`.
    pub owed: bool,
}

#[cfg(feature = "trace")]
ep_impl! {
    /// The half-open bookkeeping of slot `i`, `None` for a slot not in use (cargo feature `trace`).
    #[must_use]
    pub fn half_open_slot(&self, i: usize) -> Option<HalfOpenSlot> {
        let s = self.slots.get(i).filter(|s| s.m.in_use)?;
        Some(HalfOpenSlot {
            created: s.m.created,
            unauth: s.m.unauth,
            life: s.half_open_life(self.rtt.thin_node()),
            counted: s.m.half_open,
            deadline: self.heap.deadline(i),
            owed: s.m.owed,
        })
    }

    /// Whether the host left so many events unread that the endpoint starts no session and runs no timer (cargo
    /// feature `trace`).
    #[must_use]
    pub const fn events_stalled(&self) -> bool {
        self.events.stalled()
    }
}

#[cfg(feature = "trace")]
ep_impl! {
    /// The deadline slot `i` holds in the heap, in use or not (cargo feature `trace`).
    #[must_use]
    pub fn slot_deadline(&self, i: usize) -> Option<u64> {
        self.heap.deadline(i)
    }

    /// The id the session in slot `i` was first dialed under, `None` for a slot not in use (cargo feature `trace`).
    #[must_use]
    pub fn slot_odcid(&self, i: usize) -> Option<ConnId> {
        self.slots.get(i).filter(|s| s.m.in_use).and_then(|s| s.m.odcid)
    }

    /// How many routing entries point at slot `i` (cargo feature `trace`).
    #[must_use]
    pub fn slot_routes(&self, i: usize) -> usize {
        self.demux.iter().filter(|(_, v)| **v as usize == i).count()
    }

    /// The slots the routing table lists for `cid` (up to 4) and how many it holds (cargo feature `trace`).
    #[must_use]
    pub fn routes_of(&self, cid: &ConnId) -> ([Option<u32>; 4], usize) {
        self.demux.matches::<4>(cid)
    }

    /// Entry `k` of the table of held fragments (cargo feature `trace`).
    #[must_use]
    pub fn held_fragment(&self, k: usize) -> Option<crate::OrphanEntry> {
        self.orphans.entry(k)
    }
}

/// A number standing for an address in a trace line.
#[cfg(feature = "trace")]
pub(crate) fn addr_key(a: &SocketAddr) -> u64 {
    match a {
        SocketAddr::V4(v) => u64::from(u32::from(*v.ip())) << 16 | u64::from(v.port()),
        SocketAddr::V6(v) => {
            let o = v.ip().octets();
            let mut x = u64::from(v.port());
            for c in o.chunks(8) {
                let mut w = [0u8; 8];
                if let Some(d) = w.get_mut(..c.len()) {
                    d.copy_from_slice(c);
                }
                x ^= u64::from_be_bytes(w).rotate_left(17);
            }
            x
        }
    }
}

/// The route-table bookkeeping of one slot, for trace validation (cargo feature `trace`).
#[cfg(feature = "trace")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RouteView {
    /// The slot holds a session.
    pub live: bool,
    /// The remote address of the session's active path when it is validated and direct.
    pub direct: Option<core::net::SocketAddr>,
    /// The address the slot's entry in the table is under.
    pub route: Option<core::net::SocketAddr>,
}

#[cfg(feature = "trace")]
ep_impl! {
    /// The route-table view of slot `i`, `None` past the last slot (cargo feature `trace`).
    #[must_use]
    pub fn route_view(&self, i: usize) -> Option<RouteView> {
        let s = self.slots.get(i)?;
        Some(RouteView {
            live: s.m.in_use,
            direct: self.direct_remote(i),
            route: s.m.route,
        })
    }

    /// The entries of the table of sessions by address, oldest first, as (address, slot) (cargo feature `trace`).
    pub fn route_entries(&self) -> impl Iterator<Item = (core::net::SocketAddr, usize)> + '_ {
        self.by_route.iter().map(|(a, i)| (*a, *i as usize))
    }
}
