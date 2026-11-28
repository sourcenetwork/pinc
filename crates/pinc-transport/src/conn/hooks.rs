//! Hooks for the endpoint layer: what `pinc-core` needs from a connection and the connection alone can give.
//!
//! The endpoint recycles a connection's memory ([`Connection::into_resources`]), answers key requests it was told
//! about ([`Connection::pending_key_request`]), feeds the node-wide round trips back ([`Connection::set_node_rtt`]),
//! moves the first resend of a dial ([`Connection::set_first_retransmit`]), allows short Initials in its resends
//! ([`Connection::set_short_until`]) and reports a prekey reject ([`Connection::take_prekey_rejected`]), defers the
//! first path MTU probe ([`Connection::defer_mtu_probe`]), sends the handshake flight on several candidate paths
//! ([`Connection::set_flight_fanout`], and [`Connection::set_flight_skip_primary`] to leave the active path out),
//! starts a sub-session ([`Connection::sub_session`]) and starts one whose parent is still in its handshake
//! ([`Connection::sub_pending`], opened by [`Connection::activate_sub`]).
//!
//! Invariants: a sub-session is born established with keys derived from its parent's, so it needs no handshake
//! message and no round trip; the flight fan-out only repeats bytes the handshake already queued, one path after the
//! other, never changes what the primary path sends, and ends when a dialing side is established.

use pinc_crypto::Provider;
use pinc_security::{
    Alpn, AlpnList, ConnId, CreditRecord, Env, Established, Failure, KeyRequest, LocalIdentity, Responder,
    ResponderConfig, TicketBatch, sub_session_secret,
};

use super::config::{Config, PathId, PathInfo};
use super::handshake::Machine;
use super::params::peer_limits;
use super::{Connection, Phase, Resources, Tables};
use crate::recovery::RttEstimator;
use crate::stream::StreamSource;

/// What the application may queue on a pending sub-session before the peer's record is known: one window unit
/// (16 KiB) ...
pub(super) const PENDING_WINDOW: u64 = 16 * 1024;
/// ... and this many streams.
const PENDING_STREAMS: u16 = 4;
use pinc_security::Event as SecEvent;

/// What a sub-session is opened from: the parent session, the protocol and the two connection ids.
#[derive(Debug, Clone, Copy)]
pub struct SubOpen<'p> {
    /// Whether this side opened the sub-session (the dialer) or accepts it.
    pub client: bool,
    /// The established parent session; its secrets seed the sub-session's keys.
    pub parent: &'p Established,
    /// The application protocol of the sub-session.
    pub alpn: Alpn,
    /// The dialer's connection id for the sub-session.
    pub cc: ConnId,
    /// The accepting side's connection id for the sub-session.
    pub cs: ConnId,
    /// This node's identity (the shell handshake machine needs one; it signs nothing).
    pub identity: LocalIdentity,
    /// The path the sub-session starts on: the parent's active path.
    pub path: PathId,
    /// What the endpoint knows about that path.
    pub path_info: PathInfo,
}

/// What a dialed sub-session whose parent is still in its handshake is opened from.
#[derive(Debug, Clone, Copy)]
pub struct SubWait {
    /// The application protocol of the sub-session.
    pub alpn: Alpn,
    /// The dialer's connection id for the sub-session.
    pub cc: ConnId,
    /// The accepting side's connection id for the sub-session.
    pub cs: ConnId,
    /// This node's identity (the shell handshake machine needs one; it signs nothing).
    pub identity: LocalIdentity,
    /// The path the sub-session starts on: the parent's dial path.
    pub path: PathId,
    /// What the endpoint knows about that path.
    pub path_info: PathInfo,
}

conn_impl! {
    /// Give back the memory this connection used, for the next one. The pool is not reset here; the spill slots its
    /// streams hold go back to the endpoint's arena, however the connection ended.
    pub fn into_resources(mut self, lent: &mut super::Lent<'_, 'a>) -> Resources<'a, S, N, C, F> {
        self.with_lent(lent, |c| c.streams.release_spills(&mut c.pool));
        Resources {
            pool: self.pool,
            streams: self.streams,
            loss: self.loss,
            tables: Tables {
                sent: self.rec.into_ring(),
                events: self.events.into_table(),
                machines: self.hs.machines().clone(),
            },
        }
    }

    /// The key operation the handshake waits for, if any, after an [`Event::KeyRequest`](super::Event::KeyRequest).
    pub fn pending_key_request(&self) -> Option<KeyRequest<'_>> {
        self.hs.request.as_ref().map(super::handshake::OwnedRequest::as_request)
    }

    /// A number that changes whenever the set of connection ids [`local_cids`](Self::local_cids) yields changes.
    pub fn cid_epoch(&self) -> u64 {
        self.cids.epoch()
    }

    /// Until when the session counts as carrying application data: the endpoint's last application activity on it,
    /// sent or received (the transport sees only what this side writes), plus the 20 s after which the reference
    /// model takes a session to be idle. An idle end on a relay does not look for a direct path (`challenge_back`).
    pub const fn set_app_until(&mut self, at: u64) {
        self.life.app_until = at;
    }

    /// Feed the node-wide round trips back: the largest recent round trip (the probe timeout of a connection with
    /// no sample starts from it), the average handshake round trip, and whether the node is on a constrained link.
    /// A zero value leaves that input as it was.
    pub fn set_node_rtt(&mut self, peak: u64, handshake: u64, thin: bool) {
        if peak > 0 {
            self.rec.set_node_rtt(peak.max(self.rec.peak_rtt()));
            self.cfg.node_peak_rtt = Some(peak);
        }
        if handshake > 0 {
            self.rec.set_handshake_rtt(handshake);
            self.cfg.node_rtt = Some(handshake);
        }
        self.cfg.thin = thin;
        self.hs.set_node_timing(thin, self.cfg.node_rtt, self.cfg.node_peak_rtt);
    }

    /// A responder that has sent its flight, so it holds its handshake at least [`super::RESPONDER_HOLD`].
    pub fn answered(&self) -> bool {
        self.hs.answered()
    }

    /// Allow the short prekey Initial in the resends of a dialing handshake while the clock is below `until`: the node
    /// heard a validated UDP path lately. A connection never told has the allowance its dial began with.
    pub fn set_short_until(&mut self, until: u64) {
        self.hs.set_short_until(until);
    }

    /// Whether a dialing handshake took a prekey reject since the last call: the peer does not hold the prekey the
    /// short Initial named, so the node should forget that it does.
    pub fn take_prekey_rejected(&mut self) -> bool {
        self.hs.take_prekey_rejected()
    }

    /// When the relay carrier of the active path last heard anything, or `None` when that carrier is not open. A
    /// session on a relay path whose probes keep timing out while its carrier answers is closed: its peer no longer
    /// holds it (see [`handle_timeout`](Self::handle_timeout)).
    pub fn set_carrier_heard(&mut self, heard: Option<u64>) {
        self.life.carrier_heard = heard;
    }

    /// Move the pending first resend of a dialing handshake to the absolute time `at`. Ignored once the first
    /// flight is answered.
    pub fn set_first_retransmit(&mut self, at: u64) {
        self.hs.set_retransmit_at(at);
    }

    /// Hold the resends of the flight of a dialing handshake (the peer's address is still being looked up), or let
    /// them go on. While held the timer fires every 500 ms and sends nothing.
    pub fn hold_first_flight(&mut self, hold: bool) {
        self.hs.set_held(hold);
    }

    /// End a dialing handshake with [`CloseReason::Unanswered`](super::CloseReason::Unanswered) when its resend timer
    /// fires after 4 first flights went out with nothing heard (at the 500 ms first delay: 7.5 s for a full handshake,
    /// 3 s for a resume, whose fallback restarts the schedule) instead of at its 30 s limit. Held resends do not count,
    /// a message from the peer (a rejected ticket too) starts the count again, and a thin node keeps its 60 s.
    pub const fn end_unanswered(&mut self) {
        self.hs.end_unanswered();
    }

    /// No path MTU probe is sent before `until`.
    pub fn defer_mtu_probe(&mut self, until: u64) {
        self.life.qr_until = self.life.qr_until.max(until);
    }

    /// Acknowledge every `every`-th ack-eliciting packet instead of the default policy (`None`), as
    /// [`Config::ack_every`]: 4 for a dialed session to a hub.
    pub fn set_ack_every(&mut self, every: Option<u32>) {
        self.cfg.ack_every = every;
        self.rx.set_every(every);
    }

    /// Send every handshake flight, and each resend of it, on the given paths as well as the active one. The flight
    /// leaves on the active path first, then on each listed path in turn; paths the connection does not track are
    /// ignored. An empty list turns the fan-out off. A dialing side turns it off itself when its session is
    /// established (the reply came back on one path, and the Finish and its resends go there only), and a later call
    /// is ignored. A responder keeps every path its first message completed on, and adds the listed ones.
    pub fn set_flight_fanout(&mut self, ids: &[PathId]) {
        let ids: &[PathId] = if self.client && self.phase != Phase::Handshaking { &[] } else { ids };
        let named = ids
            .iter()
            .filter_map(|id| self.paths.find(*id))
            .filter(|i| *i != self.paths.active && *i < 16)
            .fold(0u16, |m, i| m | (1 << i));
        // A responder's owed paths are the ones its first message completed on, not the host's to take back.
        self.fan_set = if self.client { named } else { self.fan_set | named };
        self.fan_mask = if self.hs.has_tx() { self.fan_set } else { 0 };
        if self.fan_set == 0 {
            self.fan_target = None;
        }
    }

    /// While the handshake runs, send its flight only on the fan-out paths and never on the active one (one path
    /// per try, chosen by the layer above). With no fan-out path the flight is not sent at all in that try. Ignored
    /// once the handshake is done.
    pub fn set_flight_skip_primary(&mut self, skip: bool) {
        self.fan_skip = skip;
    }

    /// Whether the flight leaves only on the fan-out paths right now.
    ///
    /// A responder owes its flight to the paths its first message completed on (`fan_set`, the active path's bit
    /// included when it is owed): when the active path is not one of them, the flight skips it.
    pub(super) fn flight_skips_primary(&self) -> bool {
        self.phase == Phase::Handshaking
            && (self.fan_skip || (!self.client && self.fan_set != 0 && self.fan_set & (1 << self.paths.active) == 0))
    }

    /// The handshake flight is done being owed to any path (the session is confirmed, or its dialer is validated).
    pub(super) fn end_fan(&mut self) {
        self.fan_set = 0;
        self.fan_mask = 0;
        self.fan_target = None;
    }

    /// A keepalive that is not a transport PING stood for this connection's (an authenticated carrier answered for
    /// it): count it as traffic received, and as traffic sent when `sent`, so neither the idle timeout nor the next
    /// keepalive fires meanwhile. An answer that arrived (`sent` false) is also a datagram heard on the active path, and
    /// the peer heard: the give-up and the closing of a relay session behind a live carrier read the silence from it.
    pub fn pulse(&mut self, now: u64, sent: bool) {
        self.life.last_activity = now;
        if sent {
            self.life.last_sent = now;
        } else {
            self.rec.note_peer_activity(now);
            if let Some(p) = self.paths.get_mut(self.paths.active) {
                p.last_rx = now;
            }
        }
    }

    /// Replay the flight on the next fan-out path once the current one is fully out. A responder's target whose
    /// budget cannot carry even the smallest datagram is skipped this round, so it cannot hold the flight back from
    /// the paths that can take it; the next retransmission tries it again. The only target is never skipped: the flight
    /// waits there for budget and goes on from where it stopped.
    pub(super) fn fan_step(&mut self) {
        let owed = !self.client && self.fan_set != 0;
        if self.hs.has_tx()
            && let Some(t) = self.fan_target.or((owed || self.flight_skips_primary()).then_some(self.paths.active))
            && self.amp_room(t) < self.control_min(t, 4)
            && (owed || self.fan_target.is_some())
            && self.fan_mask & !(1u16 << self.paths.active) != 0
        {
            self.hs.stop_flight();
        }
        if self.hs.has_tx() && !(self.flight_skips_primary() && self.fan_target.is_none() && self.fan_mask != 0) {
            return;
        }
        self.fan_target = None;
        while self.fan_mask != 0 {
            let i = self.fan_mask.trailing_zeros() as usize;
            self.fan_mask &= !(1u16 << i);
            if i != self.paths.active && self.paths.get(i).is_some() && self.hs.replay() {
                self.fan_target = Some(i);
                return;
            }
        }
    }

    /// Start a sub-session: a connection born established, with keys from the parent session's secrets, the
    /// connection ids `cc` and `cs`, and the parent's active path. [`Event::Connected`](super::Event::Connected) is
    /// ready at once and data can be written before any packet is exchanged.
    ///
    /// # Errors
    /// A [`Failure`] if the protocol cannot be listed or the pool has no chunk.
    pub fn sub_session(
        cfg: Config,
        open: SubOpen<'_>,
        res: Resources<'a, S, N, C, F>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let SubOpen { client, parent, alpn, cc, cs, identity, path, path_info } = open;
        let mut c = Self::sub_shell(client, cfg, alpn, cc, cs, &identity, path, path_info, res, env)?;
        c.establish_sub(env, parent, alpn);
        Ok(c)
    }

    /// Start a dialed sub-session whose parent is still in its handshake: the connection exists, takes writes and has
    /// its ids, but holds no keys until [`Connection::activate_sub`] gives it the parent's secrets.
    ///
    /// # Errors
    /// A [`Failure`] if the protocol cannot be listed or the pool has no chunk.
    pub fn sub_pending(
        cfg: Config,
        open: SubWait,
        res: Resources<'a, S, N, C, F>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let SubWait { alpn, cc, cs, identity, path, path_info } = open;
        let mut c = Self::sub_shell(true, cfg, alpn, cc, cs, &identity, path, path_info, res, env)?;
        // The peer's record is not known yet; the application may still open a stream and queue its first bytes, which
        // wait for the keys. The parent's record replaces this when the sub-session opens.
        c.peer_credit = CreditRecord::new(PENDING_WINDOW, PENDING_STREAMS, 0);
        c.streams.set_peer_limits(&peer_limits(&c.peer_credit));
        Ok(c)
    }

    /// The round-trip estimate of this connection.
    pub const fn rtt_estimate(&self) -> RttEstimator {
        *self.rec.rtt()
    }

    /// Start from `rtt` when this connection has measured nothing yet: a sub-session runs on its parent's paths.
    pub fn adopt_rtt(&mut self, rtt: RttEstimator) {
        self.rec.adopt_rtt(rtt);
    }

    /// The paths this connection tracks: the id, what the endpoint said of it, and whether it is validated.
    pub fn path_list(&self) -> impl Iterator<Item = (PathId, PathInfo, bool)> + '_ {
        self.paths.iter().map(|(_, p)| (p.id, p.info, p.validated))
    }

    /// The ids of the paths this connection can still name in a datagram or adopt: every tracked path, the active one
    /// also when its address is gone, and a handshake reply's path not yet followed. The set the endpoint's table of
    /// address pairs counts the session as holding.
    pub fn path_ids(&self) -> [Option<PathId>; NP] {
        let mut ids = self.paths.slots.map(|s| s.map(|p| p.id));
        // A reply that finds no free slot cannot be adopted (`learn_path` refuses at a full table), so needs no pair.
        if let Some((id, ..)) = self.reply_from
            && !ids.contains(&Some(id))
            && let Some(free) = ids.iter_mut().find(|s| s.is_none())
        {
            *free = Some(id);
        }
        for id in self.hold_ids.into_iter().flatten() {
            if !ids.contains(&Some(id))
                && let Some(free) = ids.iter_mut().find(|s| s.is_none())
            {
                *free = Some(id);
            }
        }
        ids
    }

    /// Run where the parent session runs: take its paths with their validation, and its active path. A path of this
    /// connection the parent does not hold validated is no longer validated here. A sub-session born while its parent
    /// was in its handshake took the path the parent dialed first, which the handshake may have left for another.
    pub fn adopt_paths(&mut self, env: &mut Env<'_, P>, parent: &[(PathId, PathInfo, bool)], active: PathId) {
        for slot in self.paths.slots.iter_mut().flatten() {
            if !parent.iter().any(|(id, _, v)| *id == slot.id && *v) {
                slot.validated = false;
            }
        }
        for &(id, info, validated) in parent {
            let Some(i) = self.paths.find(id).or_else(|| self.new_path_slot(id, info, env.now)) else {
                continue;
            };
            if let Some(p) = self.paths.get_mut(i) {
                p.info = info;
                if validated {
                    p.validated = true;
                    p.amp.validate();
                }
            }
            self.sync_kind(i);
        }
        if let Some(i) = self.paths.find(active) {
            self.switch_active(i);
        }
    }

    /// The parent of a pending sub-session is established: derive the keys from its secrets and open for data.
    ///
    /// # Errors
    /// [`Failure::InvalidParameter`] if the connection is not a pending sub-session.
    pub fn activate_sub(&mut self, env: &mut Env<'_, P>, parent: &Established, alpn: Alpn) -> Result<(), Failure> {
        if !self.client || self.phase != Phase::Handshaking || self.cids.first_remote().is_none() {
            return Err(Failure::InvalidParameter);
        }
        self.establish_sub(env, parent, alpn);
        Ok(())
    }

    #[allow(clippy::too_many_arguments, reason = "the parts of a sub-session shell")]
    fn sub_shell(
        client: bool,
        cfg: Config,
        alpn: Alpn,
        cc: ConnId,
        cs: ConnId,
        identity: &LocalIdentity,
        path: PathId,
        path_info: PathInfo,
        mut res: Resources<'a, S, N, C, F>,
        env: &mut Env<'_, P>,
    ) -> Result<Self, Failure> {
        let (first_local, first_remote) = if client { (cc, cs) } else { (cs, cc) };
        let local = Self::advertise(&cfg, &mut res.streams, &res.pool);
        let alpns = AlpnList::new(&[alpn.as_bytes()]).ok_or(Failure::InvalidParameter)?;
        let shell = Machine::Server(Responder::new(ResponderConfig::new(*identity, first_local, alpns)));
        let mut c = Self::base(client, cfg, res, shell, first_local, ConnId::default(), env.now, local)?;
        c.cids.set_first_remote(first_remote);
        c.new_path_slot(path, path_info, env.now);
        if let Some(p) = c.paths.active_mut() {
            p.validated = true;
            p.amp.validate();
        }
        c.sess_amp.validate();
        Ok(c)
    }

    /// Give the shell the keys of the sub-session derived from `parent`.
    fn establish_sub(&mut self, env: &mut Env<'_, P>, parent: &Established, alpn: Alpn) {
        let (cc, cs) = if self.client {
            (self.cids.first_local(), self.cids.first_remote().unwrap_or_default())
        } else {
            (self.cids.first_remote().unwrap_or_default(), self.cids.first_local())
        };
        let a = alpn.as_bytes();
        let est = Established {
            peer: parent.peer,
            alpn,
            traffic: parent.traffic.sub_session(a, cc.as_bytes(), cs.as_bytes()),
            resume: sub_session_secret(&parent.resume, a, cc.as_bytes(), cs.as_bytes()),
            tickets: TicketBatch::new(),
            resumed: false,
            peer_credit: parent.peer_credit,
            local_credit: self.local_credit,
            remembered_credit: CreditRecord::NONE,
            cid_secret: sub_session_secret(&parent.cid_secret, a, cc.as_bytes(), cs.as_bytes()),
        };
        self.hs.on_event(&mut self.pool, &SecEvent::Established(est.clone()));
        self.hs.retire_machine();
        self.on_hs_event(env, SecEvent::Established(est));
        self.confirmed = true;
        self.end_fan();
        self.hs.confirm(&mut self.pool);
    }
}
