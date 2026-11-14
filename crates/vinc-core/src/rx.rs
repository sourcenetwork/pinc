//! Datagrams in: find the session a datagram belongs to, or decide whether it may create one.
//!
//! The destination connection id of the first packet picks the candidates in the demultiplexing table. One
//! candidate owns the datagram; several (two sessions derived the same four bytes) are tried in turn on a copy of the
//! datagram, because opening a packet changes the bytes in place. For a short datagram the first holder that does
//! not answer undecryptable or unroutable owns it, whatever it did with it (a closed or back-pressured holder takes
//! it too); a long packet is offered to each holder in the order they were made until one takes it (one that refuses
//! a handshake message or has ended does not), and a first flight that every holder says differs from its own gets a
//! half-open session of its own under the same id, up to four holders, so a forged flight never displaces the first.
//! The candidate list can name the same slot twice, which only costs a second trial. An id no session holds can only
//! start a session if the datagram is a first handshake message that meets its size floor
//! (1200 bytes for a full Initial, 464 for a short one) and fewer than 256 sessions are unauthenticated; a ticket
//! resumption Hello is exempt from the count only when its ticket opens under this node's ticket store and is unused
//! (single use), checked before any state is held, because that binder proves a past session. Every other Hello, a
//! forged or replayed one included, counts like a full Initial. A later part of a first message that arrives before
//! the part that starts it is held for a moment in the endpoint's small table of such datagrams (see `orphan`) and
//! handed to the session once the first part has created it.
//!
//! Invariants: a datagram larger than [`MAX_DATAGRAM`] or shorter than a header is dropped and counted; a datagram
//! that cannot create a session, matches none and is not held is dropped and counted; the copy used for trials and
//! the held datagrams are the only extra buffers, held inside the endpoint.

use core::net::SocketAddr;

use vinc_security::message::{FULL_INITIAL_MIN, MAX_MESSAGE_LEN, MessageType, SHORT_INITIAL_MIN};
use vinc_security::responder::hello_opens_ticket;
use vinc_security::{ConnId, Env, Failure};
use vinc_transport::conn::{Connection, Drop, PathId, ServerParams};
use vinc_transport::packet::{LongHeader, LongType, short_dcid};
use vinc_wire::Reader;

use crate::endpoint::{CID_LEN, MAX_DATAGRAM, env, ep_impl};
use crate::orphan::ORPHAN_MAX;
use crate::relay_net::is_relay_addr;
use crate::slot::State;
use crate::trace::trace;

/// The most sessions that may hold the same four bytes and still be tried.
const MAX_CANDIDATES: usize = 4;
/// The most unauthenticated sessions.
pub const MAX_HALF_OPEN: usize = 256;
/// How long an unauthenticated session lives (30 s).
pub const HALF_OPEN_LIFE: u64 = 30_000_000_000;

/// What the first packet of an unroutable datagram says.
struct First<'a> {
    odcid: ConnId,
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
        self.ledger.on_receive(remote, buf.len() as u64);
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

    /// Offer a long packet to each of the `n` sessions that hold its id, in the order they were made, until one takes
    /// it: a holder that refuses a handshake message (a Finish it does not authenticate, a first flight other than its
    /// own) or has ended does not. When every live holder says the packet is a first flight different from its own, the
    /// packet is the start of another dial under the same id and gets a session of its own, unless the id already has
    /// [`MAX_CANDIDATES`] holders.
    fn offer(&mut self, found: &[Option<u32>], n: usize, now: u64, local: SocketAddr, remote: SocketAddr, buf: &mut [u8]) {
        let len = buf.len();
        let Some(copy) = self.scratch.get_mut(..len) else { return };
        copy.copy_from_slice(buf);
        let (mut different, mut other) = (false, false);
        for (k, i) in found.iter().flatten().enumerate() {
            if k > 0 {
                match self.scratch.get(..len) {
                    Some(s) => buf.copy_from_slice(s),
                    None => return,
                }
            }
            let r = self.deliver(*i as usize, now, local, remote, buf);
            let refused = matches!(r, Err(Drop::Handshake(_) | Drop::Closed));
            if n > 1 {
                trace!(self, now, Trial { slot: u64::from(*i), ok: u64::from(!refused) });
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
        if !different || other {
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
            MessageType::ResumeHello => 0,
            _ => {
                self.counters.dropped_in += 1;
                return;
            }
        };
        let resume = first.kind == MessageType::ResumeHello && self.opens_ticket(now, first.message);
        let admitted = buf.len() >= floor && (resume || self.half_open < MAX_HALF_OPEN);
        trace!(self, now, HalfOpen {
            admitted: u64::from(admitted),
            half_open: self.half_open as u64,
            resume: u64::from(resume),
        });
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

    /// Whether a resumption Hello names an unused ticket that opens, so it needs no half-open slot.
    fn opens_ticket(&self, now: u64, message: Option<&[u8]>) -> bool {
        message.is_some_and(|m| {
            self.alpn_list()
                .is_some_and(|alpns| hello_opens_ticket(&self.stores.tickets, &alpns, now, m))
        })
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
        slot.m.half_open = !resume;
        if !resume {
            self.half_open += 1;
        }
        self.sync_cids(i, true);
        trace!(self, now, Session { slot: i as u64, step: 0, dialer: 0 });
        Some(i)
    }
}

/// What the half-open bookkeeping holds for one slot in use, for trace validation (cargo feature `trace`).
#[cfg(feature = "trace")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HalfOpenSlot {
    /// When the session was created.
    pub created: u64,
    /// The peer is not authenticated yet, so the session ends [`HALF_OPEN_LIFE`] after `created`.
    pub unauth: bool,
    /// The session counts against [`MAX_HALF_OPEN`].
    pub counted: bool,
    /// The deadline the session holds in the endpoint's heap.
    pub deadline: Option<u64>,
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
            counted: s.m.half_open,
            deadline: self.heap.deadline(i),
        })
    }

    /// Whether the host left so many events unread that the endpoint starts no session and runs no timer (cargo
    /// feature `trace`).
    #[must_use]
    pub const fn events_stalled(&self) -> bool {
        self.events.stalled()
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
