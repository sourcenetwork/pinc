//! Commands and queries: how the application drives and reads the endpoint.
//!
//! [`Endpoint::command`] applies a [`Command`] and returns the [`Reply`]: the command's value and the events it caused
//! at once (up to eight; any more wait in the queue for [`Endpoint::poll_event`]). A command that fails changes no
//! session and queues no event, and its error says why, with two exceptions: a dial of the node's own id queues
//! [`Event::ConnectFailed`], and a sub-session whose open cannot be queued has taken a session slot, which it undoes
//! and redials, so the redial may queue events. It may leave two traces: an address the endpoint learned a path id
//! for, and, for a dial whose connection could not be built, the resumption ticket it took.
//! [`Endpoint::query`] reads state and changes nothing.
//!
//! A dial first looks for an established session with the peer: if there is one, the new protocol opens as a
//! sub-session with no round trip. Otherwise it starts a handshake with the best ticket held for the peer and the
//! protocol, the round trips the node remembers, and the first address with an interface that can reach it; the other
//! addresses become candidate paths. A dial towards a peer with a fresh cached allow reports `Connected` at once.
//!
//! Invariants: a refused command leaves no event behind except those it queued before failing; the interface for a
//! dial is chosen by address family only; a dial of this node's own identity is refused.

use core::net::SocketAddr;

use pinc_crypto::NodeId;
use pinc_security::Alpn;
use pinc_transport::conn::{ClientParams, Connection, PathInfo, code};
use pinc_transport::recovery::PathKind;

use crate::acp::ACP_RECHECK;
use crate::api::{
    Answer, Command, CommandError, ConnectFailure, Event, Events, PeerInfo, Query, Reply, SendState, SessionId,
    SessionStats, Value,
};
use crate::endpoint::{env, ep_impl, lent};
use crate::keepalive::{LATE_START, MTU_PROBE_DELAY, Role};
use crate::relay_net::is_relay_addr;
use crate::slot::{NIL, State};
use crate::trace::trace;

/// A short Initial is used only while a validated UDP path was heard within this long (90 s).
pub const UDP_FRESH: u64 = 90_000_000_000;
/// The urgency of the second broadcast stream of a gossip session. Data written to it does not count as activity on
/// a quiet session, so a secondary hub session stays quiet.
pub const FAN_URGENCY: u8 = 2;
/// Application data above this many bytes counts as activity on a quiet session.
const CTRL_SMALL: usize = 72;
/// A session this node dialed to a hub acknowledges every this many ack-eliciting packets.
const HUB_ACK_EVERY: u32 = 4;

/// What the endpoint knows about the path to `remote`: through a relay, and the address family.
pub(crate) fn path_info(remote: &SocketAddr, interface_mtu: u16) -> PathInfo {
    PathInfo {
        kind: if is_relay_addr(remote) {
            PathKind::Relay
        } else {
            PathKind::Direct
        },
        v6: remote.is_ipv6(),
        interface_mtu,
    }
}

ep_impl! {
    /// Apply a command at time `now`.
    ///
    /// # Errors
    /// A [`CommandError`] if the session is unknown, the table is full, the stream or datagram layer refuses, or the
    /// command cannot be carried out.
    pub fn command(&mut self, now: u64, cmd: Command<'_, S>) -> Result<Reply, CommandError> {
        self.last_now = now;
        self.capture = Some(Events::default());
        let r = self.apply(now, cmd);
        let events = self.capture.take().unwrap_or_default();
        match r {
            Ok(value) => {
                // A Closed in the reply reaches the host ahead of the session's events still queued from before the
                // command: they would name the session after its Closed, so they go.
                for ev in events.iter() {
                    if let Event::Closed { session, .. } = *ev {
                        self.events.purge(session);
                    }
                }
                Ok(Reply { value, events })
            }
            Err(e) => {
                for ev in events.iter() {
                    self.events.push(*ev);
                }
                Err(e)
            }
        }
    }

    /// Copy the oldest received datagram of `session` into `out` and remove it from the session's bounded receive
    /// queue. `Ok(None)` means none is waiting. Read until `None` after each [`Event::DatagramReceived`](crate::Event):
    /// a notification may stand for several datagrams, and a datagram the queue had no room for is counted in
    /// `SessionStats::transport.datagrams_dropped_recv`.
    ///
    /// # Errors
    /// [`CommandError::NoSession`] if the session is unknown; [`CommandError::BufferTooSmall`] if the datagram is
    /// longer than `out` (it stays queued; read it again with a larger buffer).
    pub fn read_datagram(&mut self, session: SessionId, out: &mut [u8]) -> Result<Option<usize>, CommandError> {
        let i = self.live(session)?;
        let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
        let Some(d) = conn.recv_datagram() else { return Ok(None) };
        let len = d.len();
        out.get_mut(..len).ok_or(CommandError::BufferTooSmall { len })?.copy_from_slice(d);
        conn.pop_datagram();
        Ok(Some(len))
    }

    /// Copy the oldest extension frame held for the application into `out` and remove it: its session, its type and
    /// its length. `Ok(None)` means none is waiting. Read until `None` after each input call (no event announces a
    /// frame); a ring that filled up has dropped its oldest frame. A frame of a session the access check has not
    /// allowed is not kept.
    ///
    /// # Errors
    /// [`CommandError::BufferTooSmall`] if the frame is longer than `out` (it stays held; read it again with a larger
    /// buffer, [`EXT_BODY_MAX`](crate::EXT_BODY_MAX) always fits).
    pub fn read_extension(&mut self, out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, CommandError> {
        self.ext_in.take(out).map_err(|len| CommandError::BufferTooSmall { len })
    }

    fn live(&self, id: SessionId) -> Result<usize, CommandError> {
        self.slot_of(id).ok_or(CommandError::NoSession)
    }

    fn apply(&mut self, now: u64, cmd: Command<'_, S>) -> Result<Value, CommandError> {
        match cmd {
            Command::Connect { node, alpn, addrs, role } => self.connect(now, node, alpn, addrs, role).map(Value::Session),
            Command::OpenStream { session, bidi } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let id = if bidi { conn.open_bi() } else { conn.open_uni() }.map_err(CommandError::Stream)?;
                self.settle(i, now);
                Ok(Value::Stream(id))
            }
            Command::Write { session, stream, data } => {
                let i = self.live(session)?;
                let slot = self.slots.get_mut(i).ok_or(CommandError::NoSession)?;
                let conn = slot.conn.as_mut().ok_or(CommandError::NoSession)?;
                let n = conn.write(stream, data).map_err(CommandError::Stream)?;
                // A quiet session is armed only by the dialing side's own writes above a control message, and
                // never on the fan stream.
                if !slot.m.role.quiet()
                    || (slot.m.client && data.len() > CTRL_SMALL && conn.urgency(stream) != Some(FAN_URGENCY))
                {
                    slot.m.last_app = now;
                }
                self.settle(i, now);
                Ok(Value::Written(n))
            }
            Command::WriteSource { session, stream, source, len } => {
                self.with_conn(session, now, |c| c.write_source(stream, source, len).map_err(CommandError::Stream))
            }
            Command::SetUrgency { session, stream, urgency } => {
                self.with_conn(session, now, |c| c.set_urgency(stream, urgency).map_err(CommandError::Stream))
            }
            Command::SendExtension { session, ty, body } => {
                self.with_conn(session, now, |c| c.send_extension(ty, body).map_err(CommandError::Extension))
            }
            Command::Finish { session, stream } => {
                self.with_conn(session, now, |c| c.finish(stream).map_err(CommandError::Stream))
            }
            Command::Reset { session, stream, error } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                conn.reset(&mut lent!(self), stream, error).map_err(CommandError::Stream)?;
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::StopSending { session, stream, error } => {
                self.with_conn(session, now, |c| c.stop_sending(stream, error).map_err(CommandError::Stream))
            }
            Command::Consume { session, stream, n } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                let st = conn.consume(&mut env, &mut lent!(self), stream, n).map_err(CommandError::Stream)?;
                self.settle(i, now);
                Ok(Value::Recv(st))
            }
            Command::SendDatagram { session, data } => {
                let i = self.live(session)?;
                let slot = self.slots.get_mut(i).ok_or(CommandError::NoSession)?;
                let conn = slot.conn.as_mut().ok_or(CommandError::NoSession)?;
                conn.send_datagram(data).map_err(CommandError::Datagram)?;
                if !slot.m.role.quiet() || data.len() > CTRL_SMALL {
                    slot.m.last_app = now;
                }
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::Close { session, error } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                conn.close(&mut env, &mut lent!(self), error);
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::Shutdown => {
                for i in 0..K {
                    let Some(slot) = self.slots.get_mut(i) else { break };
                    if !slot.m.in_use {
                        continue;
                    }
                    if let Some(conn) = slot.conn.as_mut() {
                        let mut env = env!(self, now);
                        conn.close(&mut env, &mut lent!(self), code::LEAVE);
                    }
                    self.settle(i, now);
                }
                Ok(Value::None)
            }
            Command::AcpForget { peer } => {
                self.acp.remove(&peer);
                Ok(Value::None)
            }
            Command::AcpAnswer { check, allow } => self.acp_answer(check, allow, now).map(|()| Value::None),
            Command::KeyResponse { session, response } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                if conn.pending_key_request().is_none() {
                    return Err(CommandError::NoKeyRequest);
                }
                let mut env = env!(self, now);
                let r = conn.on_key_response(&mut env, response);
                self.settle(i, now);
                r.map(|()| Value::None).map_err(CommandError::Failure)
            }
            Command::Suspend => {
                self.suspend(now);
                Ok(Value::None)
            }
            Command::Resume { moved } => {
                self.resume(now, moved);
                Ok(Value::None)
            }
            Command::FlightPaths { session, addrs, skip_primary } => {
                let i = self.live(session)?;
                let mut ids: [Option<(pinc_transport::conn::PathId, PathInfo)>; NP] = [None; NP];
                // The table holds NP paths, the dial's own among them. A relay path reaches any peer that has a
                // carrier, a direct address only a peer that can be reached there, so when the list is longer than the
                // table the relay paths go first and the direct ones follow in the order given.
                let relay_first = addrs
                    .iter()
                    .filter(|a| is_relay_addr(a))
                    .chain(addrs.iter().filter(|a| !is_relay_addr(a)));
                for (d, a) in ids.iter_mut().zip(relay_first) {
                    *d = self.route_for(a).map(|l| (self.path_id(l, *a), path_info(a, self.cfg.conn.interface_mtu)));
                }
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                // A full table makes room by dropping its oldest unvalidated path, so the paths are added from the
                // least wanted to the most wanted, and the fan-out names the ones that are still tracked.
                for (id, info) in ids.iter().flatten().rev() {
                    let _ = conn.add_path(&mut env, *id, *info);
                }
                let mut list: [pinc_transport::conn::PathId; NP] = [pinc_transport::conn::PathId(0); NP];
                let mut n = 0;
                for (id, _) in ids.iter().flatten() {
                    if conn.path_last_rx(*id).is_some()
                        && let Some(s) = list.get_mut(n)
                    {
                        *s = *id;
                        n += 1;
                    }
                }
                conn.set_flight_fanout(list.get(..n).unwrap_or_default());
                conn.set_flight_skip_primary(skip_primary);
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::Pulse { session, sent } => {
                let i = self.live(session)?;
                if let Some(s) = self.slots.get_mut(i) {
                    if sent {
                        s.m.last_tx = now;
                    } else {
                        s.m.last_rx = now;
                    }
                    if let Some(c) = s.conn.as_mut() {
                        c.pulse(now, sent);
                    }
                }
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::SetPulse { session, on } => {
                let i = self.live(session)?;
                if let Some(s) = self.slots.get_mut(i) {
                    s.m.pulse = on;
                    s.m.plan.ping_at = None;
                }
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::FirstResend { session, delay } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                conn.set_first_retransmit(now.saturating_add(delay));
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::HoldFlight { session, hold } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                conn.hold_first_flight(hold);
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::ReachOut { session, body } => {
                if body.is_empty() || body.len() > crate::reach::REACH_BODY_MAX {
                    return Err(CommandError::BadAlpn);
                }
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                conn.send_extension(pinc_transport::frame::ext::REACH_OUT, body).map_err(|_| CommandError::NoSession)?;
                // The round also probes the direct paths the session already tracks, as the reference model's does.
                let mut env = env!(self, now);
                conn.punch_known(&mut env);
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::Punch { session, addr } => {
                let i = self.live(session)?;
                let local = self.route_for(&addr).ok_or(CommandError::NoRoute)?;
                let pid = self.path_id(local, addr);
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                conn.punch(&mut env, pid, path_info(&addr, self.cfg.conn.interface_mtu)).map_err(|_| CommandError::Full)?;
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::SetRole { session, role } => {
                let i = self.live(session)?;
                if let Some(s) = self.slots.get_mut(i) {
                    s.m.role = role;
                }
                self.sync_ack_every(i);
                self.defer_mtu_for_quiet(i);
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::Ping { session } => self.with_conn(session, now, |c| {
                c.ping();
                Ok(())
            }),
            Command::CarrierHeard { session, at } => {
                let i = self.live(session)?;
                if let Some(c) = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()) {
                    c.set_carrier_heard(Some(at).filter(|t| *t > 0));
                }
                Ok(Value::None)
            }
            Command::SetGossip { session, gossip } => {
                let i = self.live(session)?;
                if let Some(s) = self.slots.get_mut(i) {
                    s.m.gossip = gossip;
                }
                self.dirty_promote(i, now);
                Ok(Value::None)
            }
        }
    }

    /// Run `f` on session `session`'s connection, then settle it.
    fn with_conn(
        &mut self,
        session: SessionId,
        now: u64,
        f: impl FnOnce(&mut Connection<'a, P, S, N, C, F, NP>) -> Result<(), CommandError>,
    ) -> Result<Value, CommandError> {
        let i = self.live(session)?;
        let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
        f(conn)?;
        self.settle(i, now);
        Ok(Value::None)
    }

    /// The acknowledgement policy of session `i` follows its role: a session this node dialed to a hub acknowledges
    /// every 4th ack-eliciting packet, any other the transport's default.
    pub(crate) fn sync_ack_every(&mut self, i: usize) {
        if let Some(s) = self.slots.get_mut(i)
            && let Some(c) = s.conn.as_mut()
        {
            c.set_ack_every((s.m.client && s.m.role == Role::Hub).then_some(HUB_ACK_EVERY));
        }
    }

    /// A late-start quiet session defers its first path MTU probe by 3 s from its creation.
    pub(crate) fn defer_mtu_for_quiet(&mut self, i: usize) {
        let late = self.t_first.is_some_and(|t| t.saturating_sub(self.started) > LATE_START);
        if let Some(s) = self.slots.get_mut(i)
            && late
            && s.m.role.quiet()
            && let Some(c) = s.conn.as_mut()
        {
            c.defer_mtu_probe(s.m.created.saturating_add(MTU_PROBE_DELAY));
        }
    }

    /// Until when a short Initial may be sent: a validated UDP path was heard within [`UDP_FRESH`] before (0: never).
    /// The one place that decides, for the first flight of a dial and for every resend of it.
    pub(crate) fn short_until(&self) -> u64 {
        self.udp_heard.map_or(0, |t| t.saturating_add(UDP_FRESH))
    }

    /// The local address of the first interface that can reach `remote`.
    fn route_for(&self, remote: &SocketAddr) -> Option<SocketAddr> {
        self.ifaces.iter().flatten().find(|l| l.is_ipv4() == remote.is_ipv4()).copied()
    }

    // Out of line, as `free_slot`: a whole connection moves here.
    #[inline(never)]
    fn connect(
        &mut self,
        now: u64,
        node: NodeId,
        alpn: &[u8],
        addrs: &[SocketAddr],
        role: Role,
    ) -> Result<SessionId, CommandError> {
        if self.events.stalled() {
            return Err(CommandError::EventsPending);
        }
        let alpn_t = Alpn::new(alpn).filter(|_| !alpn.is_empty()).ok_or(CommandError::BadAlpn)?;
        if node == self.identity.node_id() {
            self.emit(Event::ConnectFailed {
                session: None,
                node,
                alpn: alpn_t,
                reason: ConnectFailure::Refused,
            });
            return Err(CommandError::Refused);
        }
        if let Some(parent) = self.find_parent(&node, now) {
            return self.open_sub(parent, node, alpn, role, now);
        }
        // Another protocol to a peer whose handshake is still running waits for it instead of starting a second one.
        if let Some(parent) = self.find_waiting_parent(&node, alpn) {
            return self.open_sub_wait(parent, node, alpn, role, now);
        }
        let prekey = self.prekey.clone().ok_or(CommandError::NoPrekey)?;
        let first = addrs.iter().copied().find(|a| self.route_for(a).is_some()).ok_or(CommandError::NoRoute)?;
        let local = self.route_for(&first).ok_or(CommandError::NoRoute)?;
        let (i, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        let pid = self.path_id(local, first);
        let ticket = self.tickets.take(&node, alpn, now);
        let resume = ticket.is_some();
        let short_until = self.short_until();
        let peer_has_prekey = now < short_until && self.ekk.get(&node) == Some(prekey.hash());
        let late = self.t_first.unwrap_or(now).saturating_sub(self.started) > LATE_START;
        let mut extra: [Option<(pinc_transport::conn::PathId, PathInfo)>; NP] = [None; NP];
        for (d, a) in extra.iter_mut().zip(addrs.iter().filter(|a| **a != first)) {
            *d = self.route_for(a).map(|l| (self.path_id(l, *a), path_info(a, self.cfg.conn.interface_mtu)));
        }
        let cfg = self.conn_config(Some(&node));
        let params = ClientParams {
            peer: node,
            alpn,
            identity: &self.identity,
            prekey: &prekey,
            peer_has_prekey,
            ticket,
            path: pid,
            path_info: path_info(&first, self.cfg.conn.interface_mtu),
        };
        let optimistic = self.acp_cached(&node, now).is_some_and(|a| a.allow && a.until > now.saturating_add(ACP_RECHECK));
        let hub_resend = self.rtt.hub_resend(&node);
        let mut env = env!(self, now);
        // The connection is built in its slot: by value it would be copied through every frame on the way there.
        let built = match self.slots.get_mut(i) {
            Some(slot) => Connection::client_in(&mut slot.conn, cfg, params, mem, &mut env).map(|_| ()),
            None => Err(pinc_security::Failure::InvalidParameter),
        };
        if let Err(e) = built {
            self.retire_slot(i);
            return Err(CommandError::Failure(e));
        }
        self.t_first.get_or_insert(now);
        let Some(slot) = self.slots.get_mut(i) else { return Err(CommandError::Full) };
        let Some(conn) = slot.conn.as_mut() else { return Err(CommandError::Full) };
        conn.set_short_until(short_until);
        for a in addrs {
            self.ledger.open(*a);
        }
        // The other addresses are candidate paths; one that cannot be added is not worth failing the dial.
        for (p, info) in extra.iter().flatten() {
            let _ = conn.add_path(&mut env, *p, *info);
        }
        // A ticket resume to a hub after a late start waits for the remembered round trip before its first resend.
        if resume
            && late
            && role.quiet()
            && let Some(delay) = hub_resend
        {
            conn.set_first_retransmit(now.saturating_add(delay));
        }
        // Reported before the peer answered: a peer that stopped ends it after its 4th unanswered flight, not at 30 s
        // (a thin node keeps its 60 s).
        if optimistic {
            conn.end_unanswered();
            // A resumed dial carries its remembered credit; a fresh one may open streams before the peer's limits arrive.
            if !resume {
                conn.allow_early_streams();
            }
        }
        slot.m.peer = Some(node);
        slot.m.alpn = Some(alpn_t);
        slot.m.role = role;
        slot.m.optimistic = optimistic;
        trace!(self, now, Session { slot: i as u64, step: 0, dialer: 1 });
        self.link_peer(node, u32::try_from(i).unwrap_or(0));
        self.sync_cids(i, true);
        self.sync_ack_every(i);
        self.defer_mtu_for_quiet(i);
        if optimistic {
            trace!(self, now, Early { slot: i as u64, rule: 1 });
            self.announce(i);
        }
        self.settle(i, now);
        Ok(self.session_id(i))
    }

    /// Read state.
    pub fn query(&self, q: Query) -> Answer<'_> {
        match q {
            Query::Stats(id) => self.slot_of(id).map_or(Answer::None, |i| self.stats_of(i)),
            Query::SessionAt(n) => self
                .slots
                .iter()
                .enumerate()
                .filter(|(_, s)| s.m.in_use && s.conn.is_some())
                .nth(n)
                .map_or(Answer::None, |(i, _)| self.stats_of(i)),
            Query::PeerSession { node, after } => self.peer_session(&node, after),
            Query::Access(node) => self.acp.get(&node).map_or(Answer::None, |a| Answer::Access {
                allow: a.allow,
                until: a.until,
            }),
            Query::PeerAt(n) => self
                .rtt
                .peers()
                .nth(n)
                .map_or(Answer::None, |(node, krtt)| Answer::Peer(PeerInfo { node: *node, krtt: *krtt })),
            Query::Peer(node) => self
                .rtt
                .krtt(&node)
                .filter(|r| *r > 0)
                .map_or(Answer::None, |krtt| Answer::Peer(PeerInfo { node, krtt })),
            Query::Read { session, stream } => self
                .slot_of(session)
                .and_then(|i| self.slots.get(i))
                .and_then(|s| s.conn.as_ref())
                .and_then(|c| c.read_chunk(stream))
                .map_or(Answer::None, Answer::Chunk),
            Query::ReadAt { session, stream, offset } => self
                .conn_of(session)
                .and_then(|c| c.read_at(&self.spill, stream, offset))
                .map_or(Answer::None, Answer::Chunk),
            Query::StoredAfter { session, stream, from } => self
                .conn_of(session)
                .and_then(|c| c.stored_after(&self.spill, stream, from))
                .map_or(Answer::None, Answer::Stored),
            Query::SendState { session, stream } => self.conn_of(session).map_or(Answer::None, |c| {
                let v = c.send_view(stream);
                Answer::SendState(SendState {
                    sent: v.map_or(0, |v| v.sent),
                    lost: v.and_then(|v| v.lost),
                    window: c.recovery().cwnd(),
                    done: v.is_none_or(|v| v.done),
                })
            }),
            Query::InFlight(id) => self
                .conn_of(id)
                .map_or(Answer::None, |c| Answer::InFlight(c.recovery().bytes_in_flight())),
            Query::KeyRequest(id) => self
                .slot_of(id)
                .and_then(|i| self.slots.get(i))
                .and_then(|s| s.conn.as_ref())
                .and_then(pinc_transport::conn::Connection::pending_key_request)
                .map_or(Answer::None, Answer::KeyRequest),
            Query::Node => Answer::Node(self.node_stats()),
            Query::ReachOut(id) => self.reach_in.get(id).map_or(Answer::None, Answer::ReachOut),
            Query::Ledger(a) => self.ledger.get(&a).map_or(Answer::None, Answer::Ledger),
            Query::ByConnId(cid) => self
                .slots
                .iter()
                .position(|s| s.m.in_use && s.conn.is_some() && s.m.cids.contains(&Some(cid)))
                .map_or(Answer::None, |i| self.stats_of(i)),
        }
    }

    /// The connection of a live session.
    fn conn_of(&self, id: SessionId) -> Option<&Connection<'a, P, S, N, C, F, NP>> {
        self.slot_of(id).and_then(|i| self.slots.get(i)).and_then(|s| s.conn.as_ref())
    }

    /// The counters of the session of `peer` that follows `after` in the peer's list, or of its oldest.
    fn peer_session(&self, peer: &NodeId, after: Option<SessionId>) -> Answer<'_> {
        let mut next = match after {
            None => self.by_peer.get(peer).copied(),
            Some(id) => self
                .slot_of(id)
                .and_then(|i| self.slots.get(i))
                .filter(|s| s.m.linked && s.m.peer == Some(*peer))
                .map(|s| s.m.peer_next),
        };
        while let Some(i) = next.filter(|n| *n != NIL) {
            let found = self.stats_of(i as usize);
            if !matches!(found, Answer::None) {
                return found;
            }
            next = self.slots.get(i as usize).map(|s| s.m.peer_next);
        }
        Answer::None
    }

    fn stats_of(&self, i: usize) -> Answer<'_> {
        let Some(slot) = self.slots.get(i) else { return Answer::None };
        let Some(conn) = slot.conn.as_ref() else { return Answer::None };
        let transport = conn.stats();
        let path = conn.active_path();
        let min_rtt = conn.recovery().rtt().min_rtt().unwrap_or(0);
        Answer::Stats(SessionStats {
            session: self.session_id(i),
            node: slot.m.peer,
            alpn: slot.m.alpn,
            role: slot.m.role,
            gossip: slot.m.gossip,
            dialer: slot.m.client,
            established: slot.m.state == State::Established,
            allowed: slot.m.allowed,
            path,
            route: path.and_then(|p| self.path_addrs(p)),
            thin: self.rtt.thin(transport.srtt, min_rtt),
            held: slot.m.held.len(),
            held_dropped: slot.m.held.dropped,
            pto: conn.recovery().pto_duration(),
            pto_count: conn.recovery().pto_count(),
            path_validated: path.is_some_and(|p| conn.path_validated(p)),
            heard: path.and_then(|p| conn.path_last_rx(p)).unwrap_or(0),
            heard_any: conn.recovery().last_heard(),
            pulse_due: slot.m.pulse_due,
            last_app: slot.m.last_app,
            sub: slot.m.sub,
            answered: slot.m.answered,
            transport,
        })
    }
}
