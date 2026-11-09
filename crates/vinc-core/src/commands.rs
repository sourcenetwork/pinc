//! Commands and queries: how the application drives and reads the endpoint.
//!
//! [`Endpoint::command`] applies a [`Command`] and returns the [`Reply`]: the command's value and the events it caused
//! at once (up to eight; any more wait in the queue for [`Endpoint::poll_event`]). A command that fails changes
//! nothing and its error says why. [`Endpoint::query`] reads state and changes nothing.
//!
//! A dial first looks for an established session with the peer: if there is one, the new protocol opens as a
//! sub-session with no round trip. Otherwise it starts a handshake with the best ticket held for the peer and the
//! protocol, the round trips the node remembers, and the first address with an interface that can reach it; the other
//! addresses become candidate paths. A dial towards a peer with a fresh cached allow reports `Connected` at once.
//!
//! Invariants: a refused command leaves no event behind except those it queued before failing; the interface for a
//! dial is chosen by address family only; a dial of this node's own identity is refused.

use core::net::SocketAddr;

use vinc_crypto::NodeId;
use vinc_security::Alpn;
use vinc_transport::conn::{ClientParams, Connection, PathInfo, code};
use vinc_transport::recovery::PathKind;

use crate::acp::ACP_RECHECK;
use crate::api::{
    Answer, Command, CommandError, ConnectFailure, Event, Events, PeerInfo, Query, Reply, SessionId, SessionStats,
    Value,
};
use crate::endpoint::{env, ep_impl};
use crate::keepalive::{LATE_START, MTU_PROBE_DELAY, Role};
use crate::relay_net::is_relay_addr;
use crate::slot::State;
use crate::trace::trace;

/// A short Initial is used only while a validated UDP path was heard within this long (90 s).
pub const UDP_FRESH: u64 = 90_000_000_000;
/// Application data above this many bytes counts as activity on a quiet session.
const CTRL_SMALL: usize = 72;

/// What the endpoint knows about the path to `remote`: through a relay, and the address family.
pub(crate) fn path_info(remote: &SocketAddr) -> PathInfo {
    PathInfo {
        kind: if is_relay_addr(remote) {
            PathKind::Relay
        } else {
            PathKind::Direct
        },
        v6: remote.is_ipv6(),
        ..PathInfo::default()
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
            Ok(value) => Ok(Reply { value, events }),
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
                if !slot.m.role.quiet() || data.len() > CTRL_SMALL {
                    slot.m.last_app = now;
                }
                self.settle(i, now);
                Ok(Value::Written(n))
            }
            Command::WriteSource { session, stream, source, len } => {
                self.with_conn(session, now, |c| c.write_source(stream, source, len).map_err(CommandError::Stream))
            }
            Command::Finish { session, stream } => {
                self.with_conn(session, now, |c| c.finish(stream).map_err(CommandError::Stream))
            }
            Command::Reset { session, stream, error } => {
                self.with_conn(session, now, |c| c.reset(stream, error).map_err(CommandError::Stream))
            }
            Command::Consume { session, stream, n } => {
                let i = self.live(session)?;
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                let st = conn.consume(&mut env, stream, n).map_err(CommandError::Stream)?;
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
                conn.close(&mut env, error);
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
                        conn.close(&mut env, code::LEAVE);
                    }
                    self.settle(i, now);
                }
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
                let mut ids: [Option<(vinc_transport::conn::PathId, PathInfo)>; NP] = [None; NP];
                for (d, a) in ids.iter_mut().zip(addrs) {
                    *d = self.route_for(a).map(|l| (self.path_id(l, *a), path_info(a)));
                }
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                let mut list: [vinc_transport::conn::PathId; NP] = [vinc_transport::conn::PathId(0); NP];
                let mut n = 0;
                for (id, info) in ids.iter().flatten() {
                    // A path the connection cannot track is left out of the fan-out.
                    if conn.add_path(&mut env, *id, *info).is_ok()
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
                    s.m.last_rx = now;
                    if sent {
                        s.m.last_tx = now;
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
            Command::ReachOut { session, body } => {
                if body.is_empty() || body.len() > crate::reach::REACH_BODY_MAX {
                    return Err(CommandError::BadAlpn);
                }
                self.with_conn(session, now, |c| {
                    c.send_extension(vinc_transport::frame::ext::REACH_OUT, body).map_err(|_| CommandError::NoSession)
                })
            }
            Command::Punch { session, addr } => {
                let i = self.live(session)?;
                let local = self.route_for(&addr).ok_or(CommandError::NoRoute)?;
                let pid = self.path_id(local, addr);
                let conn = self.slots.get_mut(i).and_then(|s| s.conn.as_mut()).ok_or(CommandError::NoSession)?;
                let mut env = env!(self, now);
                conn.punch(&mut env, pid, path_info(&addr)).map_err(|_| CommandError::Full)?;
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::SetRole { session, role } => {
                let i = self.live(session)?;
                if let Some(s) = self.slots.get_mut(i) {
                    s.m.role = role;
                }
                self.defer_mtu_for_quiet(i);
                self.settle(i, now);
                Ok(Value::None)
            }
            Command::SetGossip { session, gossip } => {
                let i = self.live(session)?;
                if let Some(s) = self.slots.get_mut(i) {
                    s.m.gossip = gossip;
                }
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

    /// The local address of the first interface that can reach `remote`.
    fn route_for(&self, remote: &SocketAddr) -> Option<SocketAddr> {
        self.ifaces.iter().flatten().find(|l| l.is_ipv4() == remote.is_ipv4()).copied()
    }

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
            self.emit(Event::ConnectFailed { node, alpn: alpn_t, reason: ConnectFailure::Refused });
            return Err(CommandError::Refused);
        }
        if let Some(parent) = self.find_parent(&node) {
            return self.open_sub(parent, node, alpn, role, now);
        }
        // Another protocol to a peer whose handshake is still running waits for it instead of starting a second one.
        if let Some(parent) = self.find_waiting_parent(&node, alpn) {
            return self.open_sub_wait(parent, node, alpn, role, now);
        }
        let prekey = self.prekey.clone().ok_or(CommandError::NoPrekey)?;
        let first = addrs.iter().copied().find(|a| self.route_for(a).is_some()).ok_or(CommandError::NoRoute)?;
        let local = self.route_for(&first).ok_or(CommandError::NoRoute)?;
        let pid = self.path_id(local, first);
        let ticket = self.tickets.take(&node, alpn, now);
        let resume = ticket.is_some();
        let short_ok = self.udp_heard.is_some_and(|t| now.saturating_sub(t) < UDP_FRESH);
        let peer_has_prekey = short_ok && self.ekk.get(&node) == Some(prekey.hash());
        self.t_first.get_or_insert(now);
        let late = self.t_first.is_some_and(|t| t.saturating_sub(self.started) > LATE_START);
        let (i, mem) = self.alloc_slot(true, now).ok_or(CommandError::Full)?;
        let mut extra: [Option<(vinc_transport::conn::PathId, PathInfo)>; NP] = [None; NP];
        for (d, a) in extra.iter_mut().zip(addrs.iter().filter(|a| **a != first)) {
            *d = self.route_for(a).map(|l| (self.path_id(l, *a), path_info(a)));
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
            path_info: path_info(&first),
        };
        let mut env = env!(self, now);
        let mut conn = match Connection::client(cfg, params, mem, &mut env) {
            Ok(c) => c,
            Err(e) => {
                self.retire_slot(i);
                return Err(CommandError::Failure(e));
            }
        };
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
            && let Some(delay) = self.rtt.hub_resend(&node)
        {
            conn.set_first_retransmit(now.saturating_add(delay));
        }
        let optimistic = self.acp_cached(&node, now).is_some_and(|a| a.allow && a.until > now.saturating_add(ACP_RECHECK));
        let Some(slot) = self.slots.get_mut(i) else { return Err(CommandError::Full) };
        slot.conn = Some(conn);
        slot.m.peer = Some(node);
        slot.m.alpn = Some(alpn_t);
        slot.m.role = role;
        slot.m.optimistic = optimistic;
        trace!(self, now, Session { slot: i as u64, step: 0, dialer: 1 });
        self.link_peer(node, u32::try_from(i).unwrap_or(0));
        self.sync_cids(i, true);
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
            Query::PeerAt(n) => self
                .rtt
                .peers()
                .nth(n)
                .map_or(Answer::None, |(node, krtt)| Answer::Peer(PeerInfo { node: *node, krtt: *krtt })),
            Query::Read { session, stream } => self
                .slot_of(session)
                .and_then(|i| self.slots.get(i))
                .and_then(|s| s.conn.as_ref())
                .and_then(|c| c.read_chunk(stream))
                .map_or(Answer::None, Answer::Chunk),
            Query::KeyRequest(id) => self
                .slot_of(id)
                .and_then(|i| self.slots.get(i))
                .and_then(|s| s.conn.as_ref())
                .and_then(vinc_transport::conn::Connection::pending_key_request)
                .map_or(Answer::None, Answer::KeyRequest),
            Query::Node => Answer::Node(self.node_stats()),
            Query::ReachOut(id) => self.reach_in.get(id).map_or(Answer::None, Answer::ReachOut),
            Query::Ledger(a) => self.ledger.get(&a).map_or(Answer::None, Answer::Ledger),
        }
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
            pulse_due: slot.m.pulse_due,
            transport,
        })
    }
}
