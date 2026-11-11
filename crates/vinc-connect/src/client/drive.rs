//! The connectivity layer driving a `vinc-core` endpoint: dials, first flights, relay paths, hole punching, the hub
//! tunnel and suspension.
//!
//! The host calls these around its own endpoint loop:
//! - [`Connectivity::dial`] in place of a plain connect;
//! - [`Connectivity::observe`] with every endpoint event, before handling it;
//! - [`Connectivity::drive`] after any input and at [`Connectivity::next_deadline`];
//! - [`Connectivity::route`] for every datagram the endpoint transmits;
//! - [`Connectivity::deliver_inbound`] to hand the endpoint what relays carried;
//! - [`Connectivity::poll_event`] for the endpoint events that commands of the layer itself produced (handle them
//!   exactly like polled ones, `observe` first);
//! - [`Connectivity::sign_request`] and [`Connectivity::key_request`] after any call, answered from the node's key
//!   (a software key, or a TPM through a key host) with [`Connectivity::sign_response`] and
//!   [`Connectivity::key_response`]: the record, the sleep notices, the beacons and the carrier handshake all take
//!   the same path, so the private key never has to be in this process.
//!
//! Nothing here allocates; the endpoint's own types carry the commands.

use core::net::SocketAddr;

use vinc_core::{
    Answer, Command, CommandError, Endpoint, Event, PathState, Query, Reply, Role, SessionId, SessionStats, Value,
    is_relay_addr,
};
use vinc_crypto::{NodeId, Provider};
use vinc_security::{ConnId, Env};
use vinc_transport::stream::StreamSource;

use super::conn::{Connectivity, LOCAL_PEERS, SESSIONS};
use super::dial::HUB_RELAY_PATH_DELAY;
use super::dial::{Cand, HUB_FIRST_ADDRS, HUB_RELAY_DELAY, RelayView, Try, direct_first, flight_relays, select};
use super::punch::Born;
use super::punch::{self, Puncher, Step, View};
use super::tunnel::{self, HubSession, Rides, ThinSplice, Via};
use crate::carrier::Frame;
use crate::carrier::frame::MAX_PACKET_LEN;
use crate::local::{self, Beacon};
use crate::record::MAX_ADDRS;
use crate::relay::datagram::Datagram;
use vinc_transport::packet::LongHeader;

/// A session the layer follows.
#[derive(Debug, Clone, Copy)]
pub(super) struct Sess {
    id: SessionId,
    node: NodeId,
    hub: Option<usize>,
    dialed: u64,
    punch: Puncher,
    handshaking: bool,
    tries: u32,
    relay_at: Option<u64>,
    /// A direct-first hub dial gets its relay path back at this time once established.
    readd_at: Option<u64>,
    pulse_on: bool,
    last_relay: Option<(u8, u64, u64)>,
    primary: Option<SocketAddr>,
    /// The active path was a relay path when the layer last looked.
    relay_route: bool,
}

/// A peer heard by local discovery.
#[derive(Debug, Clone, Copy)]
pub(super) struct LocalPeer {
    node: NodeId,
    addrs: [Option<SocketAddr>; local::MAX_ADDRS],
    at: u64,
}

macro_rules! drive_impl {
    ($($body:tt)*) => {
        impl<P: Provider, const R: usize, const PEERS: usize> Connectivity<P, R, PEERS> {
            $($body)*
        }
    };
}

/// The connectivity layer talks to the endpoint through the typed surface only: commands in, events and queries out.
/// A generic `Endpoint` parameter list would be repeated on every method, so each method takes a closure pair instead.
/// See [`Port`].
pub trait Port {
    /// The type of source-backed stream data the endpoint takes.
    type Src: StreamSource;
    /// Apply a command.
    ///
    /// # Errors
    /// The endpoint's refusal.
    fn command(&mut self, now: u64, cmd: Command<'_, Self::Src>) -> Result<vinc_core::Reply, CommandError>;
    /// Read state.
    fn stats(&self, session: SessionId) -> Option<SessionStats>;
    /// Read the node-wide numbers.
    fn node(&self) -> Option<vinc_core::NodeStats>;
    /// The remembered round trip of a peer, if the endpoint holds one.
    fn peer(&self, node: &NodeId) -> Option<vinc_core::PeerInfo>;
    /// The body of the latest REACH_OUT of a session, copied into `out`; returns its length.
    fn reach_body(&self, session: SessionId, out: &mut [u8; vinc_core::REACH_BODY_MAX]) -> usize;
    /// The session that accepts datagrams for this connection id, if any.
    fn by_conn_id(&self, cid: &ConnId) -> Option<SessionStats>;
}

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
> Port for Endpoint<'_, '_, P, S, N, C, F, NP, K, D, PK, TK, CT>
where
    P: Provider,
    S: StreamSource,
{
    type Src = S;
    fn command(&mut self, now: u64, cmd: Command<'_, S>) -> Result<vinc_core::Reply, CommandError> {
        Endpoint::command(self, now, cmd)
    }
    fn stats(&self, session: SessionId) -> Option<SessionStats> {
        match self.query(Query::Stats(session)) {
            Answer::Stats(s) => Some(s),
            _ => None,
        }
    }
    fn node(&self) -> Option<vinc_core::NodeStats> {
        match self.query(Query::Node) {
            Answer::Node(n) => Some(n),
            _ => None,
        }
    }
    fn peer(&self, node: &NodeId) -> Option<vinc_core::PeerInfo> {
        match self.query(Query::Peer(*node)) {
            Answer::Peer(p) => Some(p),
            _ => None,
        }
    }
    fn reach_body(&self, session: SessionId, out: &mut [u8; vinc_core::REACH_BODY_MAX]) -> usize {
        match self.query(Query::ReachOut(session)) {
            Answer::ReachOut(b) => {
                let n = b.len().min(out.len());
                if let (Some(d), Some(s)) = (out.get_mut(..n), b.get(..n)) {
                    d.copy_from_slice(s);
                }
                n
            }
            _ => 0,
        }
    }
    fn by_conn_id(&self, cid: &ConnId) -> Option<SessionStats> {
        match self.query(Query::ByConnId(*cid)) {
            Answer::Stats(s) => Some(s),
            _ => None,
        }
    }
}

drive_impl! {
    /// Apply `c` to the endpoint. Events its reply carries are kept for [`Connectivity::poll_event`], so the host
    /// sees every event, including those of commands the layer issued itself.
    fn cmd<E: Port>(&mut self, ep: &mut E, now: u64, c: Command<'_, E::Src>) -> Result<Reply, CommandError> {
        let r = ep.command(now, c)?;
        for e in r.events.iter() {
            if !super::conn::push(&mut self.evq, *e) {
                self.dropped += 1;
            }
        }
        Ok(r)
    }

    /// The next endpoint event a command of the layer produced. The host handles these exactly as the events it
    /// polls from the endpoint (observe, then act).
    pub fn poll_event(&mut self) -> Option<Event> {
        super::conn::pop(&mut self.evq)
    }

    fn sess_mut(&mut self, id: SessionId) -> Option<&mut Sess> {
        self.sess.iter_mut().flatten().find(|s| s.id == id)
    }

    /// The first instant a followed session has something to do on its own: the relay copy of a direct-first dial,
    /// the relay path that follows it, or a punch round.
    pub(super) fn session_deadline(&self) -> Option<u64> {
        self.sess
            .iter()
            .flatten()
            .flat_map(|s| [s.relay_at, s.readd_at, s.punch.deadline()])
            .flatten()
            .min()
    }

    /// The candidate paths for a dial to `node`: its known UDP addresses, then the relay path.
    fn candidates_for(&mut self, node: &NodeId, hints: &[SocketAddr], out: &mut [Cand; 16]) -> usize {
        let mut n = 0;
        let add = |c: Cand, out: &mut [Cand; 16], n: &mut usize| {
            if *n < out.len() && !out.get(..*n).unwrap_or_default().contains(&c)
                && let Some(s) = out.get_mut(*n) {
                    *s = c;
                    *n += 1;
                }
        };
        for a in hints {
            add(Cand::Udp(*a), out, &mut n);
        }
        if let Some(lp) = self.beacons.iter().flatten().find(|b| b.node == *node) {
            for a in lp.addrs.iter().flatten() {
                add(Cand::Udp(*a), out, &mut n);
            }
        }
        let found = self.found(node);
        if let Some(f) = &found {
            for a in f.addrs() {
                add(Cand::Udp(a), out, &mut n);
            }
        }
        // The peer's own relay when the record named one, and ours (RELAY_FORWARD on the first flight).
        let peer = found.and_then(|f| self.relay_of(&f.home)).and_then(|r| u8::try_from(r).ok());
        let own = self
            .home()
            .or_else(|| (0..R).find(|i| self.relay_cfg(*i).is_some()))
            .and_then(|r| u8::try_from(r).ok());
        for r in flight_relays(peer, own, |r| self.carrier_state(usize::from(r)) == super::link::State::Open)
            .into_iter()
            .flatten()
        {
            add(Cand::Relay(r), out, &mut n);
        }
        n
    }

    fn to_addr(&mut self, c: &Cand, node: &NodeId) -> SocketAddr {
        match c {
            Cand::Udp(a) => *a,
            Cand::Relay(r) => self.path_addr(usize::from(*r), node),
        }
    }

    /// Dial `node` for `alpn`. `hints` are addresses the caller already knows (a ticket, a record). A peer with no
    /// known address is looked up while the first flight goes through the home relay.
    ///
    /// # Errors
    /// The endpoint's refusal.
    pub fn dial<E: Port>(
        &mut self,
        now: u64,
        ep: &mut E,
        node: NodeId,
        alpn: &[u8],
        role: Role,
        hints: &[SocketAddr],
    ) -> Result<SessionId, CommandError> {
        let first = self.first_dial.is_none();
        let first_dial = *self.first_dial.get_or_insert(now);
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(&node, hints, &mut cands);
        let hub = self.relay_of(&node);
        let direct = hub.is_some() && direct_first(true, true, first_dial, self.start);
        let mut chosen = [Cand::Relay(0); 16];
        let list: &[Cand] = cands.get(..nc).unwrap_or_default();
        let (m, carried) = if direct {
            // B8: a hub's first flight goes to its known UDP address only; the relay copy joins at the first resend.
            let mut k = 0;
            for c in list.iter().filter(|c| matches!(c, Cand::Udp(_))).take(HUB_FIRST_ADDRS) {
                if let Some(s) = chosen.get_mut(k) {
                    *s = *c;
                    k += 1;
                }
            }
            (k, None)
        } else {
            let t = Try {
                now,
                dialer: true,
                tries: 1,
                link_rtt: self.net.best_rtt(),
                no_rtt: self.node_rtt == 0,
                hs0: false,
                last_relay: None,
            };
            select(list, &t, |r| Some(RelayView { live: self.relay_live(usize::from(r)), generation: self.generation(usize::from(r)) }), &mut chosen)
        };
        let _ = first;
        let m = if m == 0 { let _ = (&mut chosen, list); 0 } else { m };
        let mut addrs = [self.me_addr_pub(); 16];
        let mut na = 0;
        for c in chosen.get(..m).unwrap_or_default() {
            let a = self.to_addr(c, &node);
            if let Some(s) = addrs.get_mut(na) {
                *s = a;
                na += 1;
            }
        }
        let primary = addrs.first().copied();
        let rep = self.cmd(ep,
            now,
            Command::Connect { node, alpn, addrs: addrs.get(..na.min(1)).unwrap_or_default(), role },
        )?;
        let Value::Session(id) = rep.value else { return Err(CommandError::NoSession) };
        if na > 1 {
            let _ = self.cmd(ep,
                now,
                Command::FlightPaths { session: id, addrs: addrs.get(1..na).unwrap_or_default(), skip_primary: false },
            );
        }
        let mut relay_at = None;
        let mut readd_at = None;
        if direct {
            let _ = self.cmd(ep, now, Command::FirstResend { session: id, delay: HUB_RELAY_DELAY });
            relay_at = Some(now.saturating_add(HUB_RELAY_DELAY));
            readd_at = Some(now.saturating_add(HUB_RELAY_PATH_DELAY));
        }
        let entry = Sess {
            id,
            node,
            hub,
            dialed: now,
            punch: Puncher::off(),
            handshaking: true,
            tries: 1,
            relay_at,
            readd_at,
            pulse_on: false,
            last_relay: carried.map(|(r, g)| (r, g, now)),
            primary,
            relay_route: false,
        };
        if let Some(s) = self.sess.iter_mut().find(|s| s.is_none()) {
            *s = Some(entry);
        }
        if hub.is_none() && self.found_fresh(now, &node).is_none() && hints.is_empty() {
            self.pending.add(node, id);
            self.lookup(now, &node);
        }
        Ok(id)
    }

    /// The node has no round trip of any kind yet (no address-discovery answer, no handshake average or
    /// peak, none remembered for `peer`).
    fn heard_nothing<E: Port>(&self, ep: &E, peer: &NodeId) -> bool {
        self.net.best_rtt() == 0 && self.node_rtt == 0 && ep.peer(peer).is_none()
    }

    fn relay_live(&self, r: usize) -> bool {
        !matches!(self.carrier_state(r), super::link::State::Down)
    }

    /// Follow an endpoint event. Call it for every event before the host handles it.
    pub fn observe<E: Port>(&mut self, now: u64, ep: &mut E, ev: &Event) {
        match *ev {
            Event::Connected { session, node, .. } | Event::Incoming { session, node, .. } => {
                let dialer = matches!(ev, Event::Connected { .. });
                let hub = self.relay_of(&node);
                if let Some(s) = self.sess_mut(session) {
                    s.handshaking = false;
                    s.hub = hub;
                } else if let Some(slot) = self.sess.iter_mut().find(|s| s.is_none()) {
                    *slot = Some(Sess {
                        id: session,
                        node,
                        hub,
                        dialed: now,
                        punch: Puncher::off(),
                        handshaking: false,
                        tries: 0,
                        relay_at: None,
                        readd_at: None,
                        pulse_on: false,
                        last_relay: None,
                        primary: None,
                        relay_route: false,
                    });
                }
                let st = ep.stats(session);
                let late = self.first_dial.is_some_and(|f| self.late_start(f));
                if let Some(s) = self.sess_mut(session) {
                    s.relay_route = st.is_some_and(|st| st.route.is_some_and(|(_, r)| is_relay_addr(&r)));
                    let udp = st.is_some_and(|st| st.route.is_some_and(|(_, r)| !is_relay_addr(&r)));
                    let born = match st {
                        Some(st) if st.sub && udp && st.path_validated => Born::SubDirect,
                        Some(st) if !st.sub && dialer && hub.is_some() && late && udp => Born::LateHubDirect,
                        _ => Born::Plain,
                    };
                    s.punch = Puncher::born(now, born);
                }
                if hub.is_some() && dialer {
                    let _ = self.cmd(ep, now, Command::SetRole { session, role: Role::Hub });
                }
                if st.and_then(|st| st.alpn).is_some_and(|a| self.gossip_alpn == Some(a)) {
                    let _ = self.cmd(ep, now, Command::SetGossip { session, gossip: true });
                }
            }
            Event::PathChanged { session, state: PathState::Failed, .. } => self.path_failed(now, ep, session),
            Event::Closed { session, .. } => {
                for s in &mut self.sess {
                    if s.is_some_and(|s| s.id == session) {
                        *s = None;
                    }
                }
            }
            Event::ReachOut { session } => {
                let mut body = [0u8; vinc_core::REACH_BODY_MAX];
                let n = ep.reach_body(session, &mut body);
                let mut cands = [self.me_addr_pub(); MAX_ADDRS];
                if let Some(k) = punch::decode(body.get(..n).unwrap_or_default(), &mut cands) {
                    for a in cands.iter().take(k) {
                        let _ = self.cmd(ep, now, Command::Punch { session, addr: *a });
                    }
                }
            }
            _ => {}
        }
    }

    /// Everything the layer does between events: timers, lookups, dials waiting for an address, punching, the first
    /// flight rules on later tries, beacons and the record. `wall_ms` is the node's wall clock in milliseconds; the
    /// signatures it needs are requested through [`Connectivity::sign_request`].
    pub fn drive<E: Port>(&mut self, now: u64, ep: &mut E, env: &mut Env<'_, P>, wall_ms: Option<u64>) {
        if let Some(n) = ep.node() {
            self.set_node_rtt(n.tgr.max(n.lrtt), n.tgr);
        }
        let mut rides = [false; R];
        for s in self.sess.iter().flatten() {
            let Some(st) = ep.stats(s.id) else { continue };
            if let Some((_, remote)) = st.route
                && let Some((r, _)) = self.path_parts(&remote)
                && let Some(x) = rides.get_mut(r)
            {
                *x = true;
            }
        }
        for (i, r) in rides.iter().enumerate() {
            self.set_rides(i, *r);
        }
        self.tick(now, env, wall_ms);
        // DIAL_PRUNE: pending dials keep only the sessions still in handshake; a dial that ended drops its lookup.
        let mut dropped = [None; 8];
        let mut nd = 0;
        self.pending.prune(
            |id| ep.stats(id).is_some_and(|s| !s.established),
            |p| {
                if let Some(s) = dropped.get_mut(nd) {
                    *s = Some(*p);
                    nd += 1;
                }
            },
        );
        for p in dropped.into_iter().flatten() {
            self.lookups.answered(&p);
        }
        // A pending dial whose lookup is gone asks again.
        let peers: [Option<NodeId>; 8] = {
            let mut a = [None; 8];
            for (d, p) in a.iter_mut().zip(self.pending.peers()) {
                *d = Some(p);
            }
            a
        };
        for p in peers.into_iter().flatten() {
            if !self.lookups.contains(&p) {
                self.lookup(now, &p);
            }
        }
        while let Some(p) = super::conn::pop(&mut self.found_q) {
            self.found_dial(now, ep, &p);
        }
        self.carrier_follow_up(now, ep);
        self.each_session(now, ep);
        self.pulse_pongs(now, ep);
        self.beacon(now, wall_ms);
    }

    fn found_dial<E: Port>(&mut self, now: u64, ep: &mut E, peer: &NodeId) {
        let waiting = self.pending.take(peer);
        let Some(f) = self.found(peer) else { return };
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(peer, &[], &mut cands);
        for id in waiting.into_iter().flatten() {
            let mut addrs = [self.me_addr_pub(); 16];
            let mut na = 0;
            for c in cands.get(..nc).unwrap_or_default() {
                let a = self.to_addr(c, peer);
                if let Some(s) = addrs.get_mut(na) {
                    *s = a;
                    na += 1;
                }
            }
            let _ = self.cmd(ep,
                now,
                Command::FlightPaths { session: id, addrs: addrs.get(..na).unwrap_or_default(), skip_primary: false },
            );
        }
        let _ = f;
    }

    /// A session's active path stopped answering (three probe timeouts in a row). On a relay path the carrier of that
    /// relay and the home relay are checked. Off a relay path the session falls back to its relay path: one is
    /// registered if the session has none, the peer is looked up if there is no relay to name, and the punch timer
    /// is armed 2 s out.
    fn path_failed<E: Port>(&mut self, now: u64, ep: &mut E, session: SessionId) {
        let Some(s) = self.sess.iter().flatten().find(|s| s.id == session).copied() else { return };
        if s.relay_route {
            if let Some(st) = ep.stats(session)
                && let Some((_, remote)) = st.route
                && let Some((r, _)) = self.path_parts(&remote)
            {
                self.check_carrier(now, r);
            }
            if let Some(h) = self.home() {
                self.check_carrier(now, h);
            }
            return;
        }
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(&s.node, &[], &mut cands);
        if cands.get(..nc).unwrap_or_default().iter().any(|c| matches!(c, Cand::Relay(_))) {
            self.add_paths(now, ep, &s);
        } else {
            self.lookups.answered(&s.node);
            self.lookup(now, &s.node);
        }
        if let Some(x) = self.sess_mut(session) {
            x.punch.arm(now.saturating_add(punch::FALLBACK_PUNCH));
        }
    }

    fn each_session<E: Port>(&mut self, now: u64, ep: &mut E) {
        for i in 0..SESSIONS {
            let Some(mut s) = self.sess.get(i).copied().flatten() else { continue };
            let Some(st) = ep.stats(s.id) else {
                // The endpoint no longer has the session (a dial that failed raises no close event): its timers go
                // with it, or they would stay due forever.
                if let Some(slot) = self.sess.get_mut(i) {
                    *slot = None;
                }
                continue;
            };
            if let Some(h) = s.hub
                && st.established
                && st.path_validated
                && let Some((_, remote)) = st.route
                && !is_relay_addr(&remote)
            {
                self.relay_seen_at(h, remote);
            }
            // B8: the relay copy joins the flight of a direct-first dial at its first resend.
            if let Some(at) = s.relay_at
                && now >= at
            {
                s.relay_at = None;
                if !st.established {
                    self.add_paths(now, ep, &s);
                }
            }
            // An established hub session dialed direct-first gets its relay path back, whatever the
            // first flight did.
            if let Some(at) = s.readd_at
                && now >= at
            {
                // A session still in its handshake got every path from the resends already.
                s.readd_at = None;
                if st.established {
                    self.add_paths(now, ep, &s);
                }
            }
            // B9: later tries of a handshake choose their paths again.
            let tries = u32::try_from(st.transport.handshake_retransmits).unwrap_or(u32::MAX).saturating_add(1);
            if !st.established && st.dialer && tries != s.tries && s.relay_at.is_none() {
                s.tries = tries;
                self.reselect(now, ep, &mut s);
            }
            s.relay_route = st.route.is_some_and(|(_, r)| is_relay_addr(&r));
            // Hole punching.
            if st.established && s.punch.deadline().is_some() {
                let relay_active = s.relay_route;
                // vertexia: the 20 s idle rule applies to a session on a direct path only. A relayed session keeps
                // punching every 60 s: with the rule on those too, the node layer's churn scenario loses a member's
                // failure (it passes with the rule off for relayed or for quiet sessions). Upgrade: apply it to every
                // path once the node layer no longer depends on those rounds.
                let v = View {
                    // vertexia: the idle time is not passed yet, so the idle punch rule stays off. With it on, the
                    // quiet hub sessions of an idle network are declared stale and dialed again (two hubs and
                    // four members: eight sessions down and up in five quiet minutes). Pass the time since
                    // `st.last_app` on direct paths once that is understood and fixed.
                    app_idle: 0,
                    direct: !relay_active && st.path_validated,
                    rtt: st.transport.srtt,
                    quiet_until: 0,
                };
                if s.punch.due(now, &v) == Step::Punch {
                    self.punch_now(now, ep, &s);
                }
            }
            if let Some(h) = s.hub {
                self.pulse_session(now, ep, &mut s, &st, h);
            }
            if let Some(slot) = self.sess.get_mut(i) {
                *slot = Some(s);
            }
        }
    }

    /// Register every known path of the session's peer but its first one, and fan the flight out over them.
    fn add_paths<E: Port>(&mut self, now: u64, ep: &mut E, s: &Sess) {
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(&s.node, &[], &mut cands);
        let mut addrs = [self.me_addr_pub(); 16];
        let mut na = 0;
        for c in cands.get(..nc).unwrap_or_default() {
            let a = self.to_addr(c, &s.node);
            if Some(a) != s.primary && let Some(d) = addrs.get_mut(na) {
                *d = a;
                na += 1;
            }
        }
        let _ = self.cmd(ep,
            now,
            Command::FlightPaths { session: s.id, addrs: addrs.get(..na).unwrap_or_default(), skip_primary: false },
        );
    }

    /// Whether the active path of `st` is the relay path to relay `h` itself (a hub session on the hub's carrier).
    fn rides_own_relay(&self, st: &SessionStats, h: usize) -> bool {
        st.route.is_some_and(|(_, r)| {
            self.path_parts(&r)
                .is_some_and(|(rr, peer)| rr == h && self.relay_cfg(h).is_some_and(|c| c.id == peer))
        })
    }

    /// CARRIER_PULSE: a quiet hub session riding its hub's own carrier, with nothing in flight, is kept alive by a
    /// carrier PING instead of a session PING. The endpoint hands such a session's keepalive over and reports when
    /// one is due; when the carrier is not open the keepalive goes back to the endpoint.
    fn pulse_session<E: Port>(&mut self, now: u64, ep: &mut E, s: &mut Sess, st: &SessionStats, h: usize) {
        let want = st.established
            && st.dialer
            && st.role.quiet()
            && st.pto_count == 0
            && self.carrier_state(h) == super::link::State::Open
            && self.rides_own_relay(st, h);
        if want != s.pulse_on {
            s.pulse_on = want;
            let _ = self.cmd(ep, now, Command::SetPulse { session: s.id, on: want });
        }
        if want && st.pulse_due {
            let ctx = self.ctx(h);
            let pulse = self.rly.get_mut(h).map(|r| r.link.pulse(now, &ctx));
            if pulse == Some(super::link::Pulse::Ping) {
                self.frame_to(now, h, &Frame::Ping);
            }
            if pulse.is_some_and(|p| p != super::link::Pulse::Closed) {
                let _ = self.cmd(ep, now, Command::Pulse { session: s.id, sent: true });
            }
        }
    }

    /// CARRIER_PULSE: a PONG on a carrier counts as a datagram heard by the sessions riding it.
    fn pulse_pongs<E: Port>(&mut self, now: u64, ep: &mut E) {
        for h in 0..R {
            if !self.rly.get_mut(h).is_some_and(|r| core::mem::take(&mut r.pong)) {
                continue;
            }
            for i in 0..SESSIONS {
                let Some(s) = self.sess.get(i).copied().flatten().filter(|s| s.hub == Some(h)) else { continue };
                if ep.stats(s.id).is_some_and(|st| st.established && self.rides_own_relay(&st, h)) {
                    let _ = self.cmd(ep, now, Command::Pulse { session: s.id, sent: false });
                }
            }
        }
    }

    /// Work the carriers' held packets and re-opened carriers need the endpoint for.
    fn carrier_follow_up<E: Port>(&mut self, now: u64, ep: &mut E) {
        for h in 0..R {
            if self.rly.get_mut(h).is_some_and(|r| core::mem::take(&mut r.drain_due)) {
                self.trim_held(h, true, |held| {
                    LongHeader::parse(held.packet)
                        .ok()
                        .and_then(|(hdr, _)| ep.by_conn_id(&hdr.scid))
                        .is_some_and(|st| st.established && st.dialer)
                });
                self.drain_held(now, h);
            }
            if !self.rly.get_mut(h).is_some_and(|r| core::mem::take(&mut r.reverify)) {
                continue;
            }
            // A carrier that came back: a session riding it that heard nothing for a while asks its peer whether it
            // still holds the session.
            for i in 0..SESSIONS {
                let Some(s) = self.sess.get(i).copied().flatten() else { continue };
                let Some(st) = ep.stats(s.id) else { continue };
                if st.established
                    && now.saturating_sub(st.heard) > super::dial::REVERIFY_AGE
                    && st.route.is_some_and(|(_, r)| self.path_parts(&r).is_some_and(|(rr, _)| rr == h))
                {
                    let _ = self.cmd(ep, now, Command::Ping { session: s.id });
                }
            }
        }
    }

    fn reselect<E: Port>(&mut self, now: u64, ep: &mut E, s: &mut Sess) {
        let mut cands = [Cand::Relay(0); 16];
        let nc = self.candidates_for(&s.node, &[], &mut cands);
        let t = Try {
            now,
            dialer: true,
            tries: s.tries,
            link_rtt: self.net.best_rtt(),
            no_rtt: self.node_rtt == 0,
            hs0: super::dial::hs0(
                s.hub.is_some(),
                s.tries,
                now.saturating_sub(s.dialed),
                self.heard_nothing(ep, &s.node),
            ),
            last_relay: s.last_relay,
        };
        let mut chosen = [Cand::Relay(0); 16];
        let (m, carried) = select(
            cands.get(..nc).unwrap_or_default(),
            &t,
            |r| Some(RelayView { live: self.relay_live(usize::from(r)), generation: self.generation(usize::from(r)) }),
            &mut chosen,
        );
        if let Some((r, g)) = carried {
            s.last_relay = Some((r, g, now));
        }
        let mut addrs = [self.me_addr_pub(); 16];
        let mut na = 0;
        let mut primary_kept = false;
        for c in chosen.get(..m).unwrap_or_default() {
            let a = self.to_addr(c, &s.node);
            if Some(a) == s.primary {
                primary_kept = true;
            } else if let Some(d) = addrs.get_mut(na) {
                *d = a;
                na += 1;
            }
        }
        // THIN_HS: a try that does not include the primary path leaves it out of the flight.
        let skip_primary = s.primary.is_some() && !primary_kept;
        let _ = self.cmd(ep,
            now,
            Command::FlightPaths { session: s.id, addrs: addrs.get(..na).unwrap_or_default(), skip_primary },
        );
    }

    fn punch_now<E: Port>(&mut self, now: u64, ep: &mut E, s: &Sess) {
        let mut cands = [self.me_addr_pub(); MAX_ADDRS];
        let n = self.candidates(&mut cands);
        let mut body = [0u8; vinc_core::REACH_BODY_MAX];
        if let Some(len) = punch::encode(cands.get(..n).unwrap_or_default(), &mut body) {
            let _ = self.cmd(ep, now, Command::ReachOut { session: s.id, body: body.get(..len).unwrap_or_default() });
        }
        if let Some(f) = self.found(&s.node) {
            for a in f.addrs() {
                let _ = self.cmd(ep, now, Command::Punch { session: s.id, addr: a });
            }
        }
    }

    // ---- relay paths ----

    /// A datagram the endpoint transmitted to `remote`. Returns true if `remote` is a relay path and the datagram was
    /// handled here (sent on a carrier, by the hub tunnel, or held); false means it is an ordinary UDP datagram.
    pub fn route<E: Port>(&mut self, now: u64, ep: &E, remote: SocketAddr, packet: &[u8]) -> bool {
        self.clock = self.clock.max(now);
        let Some((relay, peer)) = self.path_parts(&remote) else { return is_relay_addr(&remote) };
        let session = self.sess.iter().flatten().find(|s| s.node == peer).map(|s| s.id);
        let st = session.and_then(|id| ep.stats(id));
        let rides = st.map(|st| Rides {
            pto_count: st.pto_count,
            handshaking: !st.established,
            hs_tries: u32::try_from(st.transport.handshake_retransmits).unwrap_or(0).saturating_add(1),
            thin: self.node_rtt >= super::dial::TG_SLOW,
        });
        let open = self.carrier_state(relay) == super::link::State::Open;
        let silent = now.saturating_sub(self.last_heard(relay));
        let tunnel_to = self.tunnel_target(now, ep, relay);
        let mut via = tunnel::decide(open, silent, rides, tunnel_to.is_some());
        if via != Via::Tunnel
            && let (Some(st), Some(_)) = (st, tunnel_to)
        {
            let thin = ThinSplice {
                thin: self.node_rtt >= super::dial::TG_SLOW,
                established: st.established,
                splice_age: self.splices.age(now, u8::try_from(relay).unwrap_or(0), &peer),
                rtt: self.node_rtt,
                carrier_fresh: open && silent < tunnel::THIN_SPLICE_FRESH,
                tunnel_took: true,
                pto_count: st.pto_count,
            };
            if tunnel::thin_splice(&thin) {
                via = Via::Tunnel;
            }
        }
        let relay_id = self.relay_cfg(relay).map(|c| c.id);
        if via != Via::Carrier
            && let Some(to) = tunnel_to
        {
            let d = Datagram::Spu { dst: peer, flag: 0, packet };
            if packet.len() <= crate::relay::datagram::MAX_TUNNEL_DATAGRAM - 35
                && self.enqueue_udp_pub(to, &d)
                && via == Via::Tunnel
            {
                // Not queued for the carrier; the dial goes on.
                self.dial_if_down(now, relay);
                return true;
            }
        }
        let _ = relay_id;
        self.send_packet(now, relay, &peer, packet);
        true
    }

    fn dial_if_down(&mut self, now: u64, relay: usize) {
        let ctx = self.ctx(relay);
        let act = self.rly.get_mut(relay).and_then(|r| r.link.want_dial(now, &mut self.shared, &ctx));
        if let Some(a) = act {
            self.act_pub(now, relay, a);
        }
    }

    pub(super) fn last_heard(&self, relay: usize) -> u64 {
        self.rly.get(relay).map_or(0, |r| r.link.last_heard())
    }

    /// The UDP address of a validated hub session that can carry a tunnel packet for `relay`: the relay's own hub
    /// session, else the home relay's (which forwards), else a hub session the relay spliced to us lately.
    fn tunnel_target<E: Port>(&self, now: u64, ep: &E, relay: usize) -> Option<SocketAddr> {
        let home = self.home();
        let order = [Some(relay), home.filter(|h| *h != relay)];
        let hub_ok = |r: usize| -> Option<(HubSession, SocketAddr)> {
            let id = self.sess.iter().flatten().find(|s| s.hub == Some(r) && !s.handshaking)?.id;
            let st = ep.stats(id)?;
            let (_, remote) = st.route?;
            let hs = HubSession { validated_direct: st.path_validated && !is_relay_addr(&remote), heard: st.heard, remote };
            Some((hs, remote))
        };
        for r in order.into_iter().flatten() {
            if let Some((hs, remote)) = hub_ok(r)
                && tunnel::hub_ok(&hs, now)
            {
                return self.rly.get(r).and_then(|x| x.cfg).and_then(|c| c.udp).filter(|_| true).or(Some(remote)).map(|_| remote);
            }
        }
        // SPLICE_LIVE: a hub that spliced down to us lately has a working UDP session; the same validated path
        // carries our tunnel packets even when our own receive stamp on it is old.
        for r in order.into_iter().flatten() {
            if let Some((hs, remote)) = hub_ok(r)
                && hs.validated_direct
                && self.splices.live(now, u8::try_from(r).unwrap_or(0), self.node_rtt) == Some(remote)
            {
                return Some(remote);
            }
        }
        None
    }

    /// The next packet relays carried for the endpoint: hand it to the endpoint with `deliver`, which receives the
    /// synthetic source address and the bytes.
    pub fn deliver_inbound(&mut self, mut deliver: impl FnMut(SocketAddr, &mut [u8])) {
        let mut buf = [0u8; MAX_PACKET_LEN];
        while let Some((from, n)) = self.poll_inbound(&mut buf) {
            if let Some(d) = buf.get_mut(..n) {
                deliver(from, d);
            }
        }
    }

    // ---- suspension ----

    /// The node suspends: sessions sleep, relays get a signed notice, carriers close.
    pub fn suspend_all<E: Port>(&mut self, now: u64, ep: &mut E, wall_ms: u64) {
        self.suspend(now, wall_ms);
        let _ = self.cmd(ep, now, Command::Suspend);
    }

    /// The node resumes: sessions wake (or redial), carriers come back.
    pub fn resume_all<E: Port>(&mut self, now: u64, ep: &mut E, moved: bool) {
        let _ = self.cmd(ep, now, Command::Resume { moved });
        self.resume(now);
        self.arm_punches(now);
    }

    /// Every followed session punches again a tenth of a second from `now` (the node's address changed).
    pub(super) fn arm_punches(&mut self, now: u64) {
        for s in self.sess.iter_mut().flatten() {
            s.punch.arm(now.saturating_add(punch::LINK_PUNCH));
        }
    }

    // ---- local discovery ----

    fn beacon(&mut self, now: u64, wall_ms: Option<u64>) {
        if self.beacons_on && wall_ms.is_some() && self.duty.poll(now) {
            self.sign.want_beacon();
        }
        self.start_jobs(now);
    }

    /// A beacon arrived on the local group. A verified one makes its addresses candidate paths for dials to its
    /// node. Returns the node when it did.
    pub fn handle_beacon(&mut self, now: u64, bytes: &[u8]) -> Option<NodeId> {
        let b = Beacon::parse_verified(bytes).ok()?;
        if b.node == self.me {
            return None;
        }
        let mut addrs = [None; local::MAX_ADDRS];
        for (d, a) in addrs.iter_mut().zip(b.addrs()) {
            *d = Some(a);
        }
        let entry = LocalPeer { node: b.node, addrs, at: now };
        let slot = self
            .beacons
            .iter()
            .position(|x| x.is_some_and(|x| x.node == b.node))
            .or_else(|| self.beacons.iter().position(Option::is_none))
            .unwrap_or_else(|| (0..LOCAL_PEERS).min_by_key(|i| self.beacons.get(*i).copied().flatten().map_or(0, |x| x.at)).unwrap_or(0));
        if let Some(s) = self.beacons.get_mut(slot) {
            *s = Some(entry);
        }
        Some(b.node)
    }

    /// A mailbox serves this node: local beacons stay off after the opening burst.
    pub const fn set_mailbox(&mut self, serves: bool) {
        self.duty.set_mailbox(serves);
    }
}
