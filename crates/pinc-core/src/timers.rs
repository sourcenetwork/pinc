//! Timers and the per-session bookkeeping that follows every input.
//!
//! After any call that touches a session the endpoint settles it: it reads the session's events, hands it the node
//! round trips if they changed, applies the keepalive plan, registers new connection ids, forgets that a peer which
//! rejected a short Initial holds the node's prekey, brings the session's entry in the table of sessions by address in
//! line with its path, and recomputes the one deadline the session contributes to the heap. The deadline is the
//! earliest of the connection's own timer, the keepalive review, the next ping of a standby path, the end of an
//! unauthenticated session's life (30 s, 60 s on a thin node, and 60 s once it answered as a responder: as long as its
//! handshake may last), and the moment a cached access answer has 5 s left.
//! [`Endpoint::poll_timeout`](crate::Endpoint::poll_timeout) is a peek at the heap;
//! [`Endpoint::handle_timeout`](crate::Endpoint::handle_timeout) pops the sessions that are due, each at most once per
//! call.
//!
//! Before a session's timer runs, the endpoint also tells it how long its re-join challenges must wait for those the
//! node's other thin sessions sent to the same address: one per address per `max(1 s, node peak round trip)`, the last
//! 200 addresses remembered, and until when a dial's resend may carry the short Initial (a validated UDP path heard
//! within 90 s of the timer, not of the dial).
//!
//! Invariants: a session has at most one entry in the heap; a settled session that has ended is freed; a deadline
//! after a timer is strictly later than the time of the call (none at the clock's last instant), so a timer cannot
//! spin; a closing session at the clock's last instant is therefore not freed.

use pinc_transport::conn::{Config, PathId, RJ_THIN_GAP};
use pinc_transport::recovery::deadline_after;

use crate::endpoint::{CLOSE_GRACE, env, ep_impl, lent};
#[cfg(feature = "trace")]
use crate::keepalive::Role;
use crate::keepalive::{ACTIVE_KEEP, Inputs, standby_due};
use crate::trace::trace;

/// The most settle records the endpoint keeps unread (cargo feature `trace`).
#[cfg(feature = "trace")]
pub const SETTLE_CAPACITY: usize = 128;

/// What one settle of a connected session that is not closing read and decided (cargo feature `trace`).
#[cfg(feature = "trace")]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SettleRecord {
    /// The time of the settle.
    pub now: u64,
    /// The session, as `SessionId` names it.
    pub session: u64,
    /// The session's role.
    pub role: Role,
    /// This side dialed.
    pub dialer: bool,
    /// The active path is not through a relay.
    pub direct: bool,
    /// The last send, as handed to the plan.
    pub last_tx: u64,
    /// The last receive, as handed to the plan.
    pub last_rx: u64,
    /// The last application data, as handed to the plan.
    pub last_app: u64,
    /// The end of the quiet period.
    pub quiet_until: u64,
    /// Whether a packet is in flight, as handed to the plan.
    pub in_flight: bool,
    /// The keepalive is handed to the layer above.
    pub pulse: bool,
    /// The plan's ping.
    pub ping_at: Option<u64>,
    /// The plan's review moment.
    pub review_at: Option<u64>,
    /// The plan differed from the one the session held.
    pub changed: bool,
    /// The interval handed to the connection at every settle; `None` when the plan has no ping or the keepalive is the
    /// layer above's.
    pub interval: Option<u64>,
    /// The connection's own deadline, as the session's deadline used it.
    pub own: u64,
    /// The least next ping of a standby path.
    pub standby: Option<u64>,
    /// The access recheck.
    pub acp: Option<u64>,
    /// The end of the session's life, while it is unauthenticated.
    pub end: Option<u64>,
    /// A ping at or before now is reported due, after it is set.
    pub pulse_due: bool,
    /// The deadline set in the heap.
    pub deadline: Option<u64>,
}

/// The bounded ring of settle records, as `TraceLog` keeps trace records.
#[cfg(feature = "trace")]
#[derive(Debug)]
pub(crate) struct SettleLog {
    ring: [Option<SettleRecord>; SETTLE_CAPACITY],
    head: usize,
    len: usize,
    dropped: u64,
}

#[cfg(feature = "trace")]
impl SettleLog {
    pub(crate) const fn new() -> Self {
        Self {
            ring: [None; SETTLE_CAPACITY],
            head: 0,
            len: 0,
            dropped: 0,
        }
    }

    pub(crate) fn push(&mut self, r: SettleRecord) {
        if self.len == SETTLE_CAPACITY {
            self.head = (self.head + 1) % SETTLE_CAPACITY;
            self.len -= 1;
            self.dropped += 1;
        }
        let at = (self.head + self.len) % SETTLE_CAPACITY;
        if let Some(s) = self.ring.get_mut(at) {
            *s = Some(r);
            self.len += 1;
        }
    }

    pub(crate) fn pop(&mut self) -> Option<SettleRecord> {
        if self.len == 0 {
            return None;
        }
        let r = self.ring.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % SETTLE_CAPACITY;
        self.len -= 1;
        r
    }

    pub(crate) const fn dropped(&self) -> u64 {
        self.dropped
    }
}

ep_impl! {
    /// The configuration of a new connection: the base configuration with the node round trips filled in. For a
    /// dial, `peer` selects the remembered round trip.
    pub(crate) fn conn_config(&self, peer: Option<&pinc_crypto::NodeId>) -> Config {
        let mut c = self.cfg.conn;
        c.thin = self.rtt.thin_node();
        c.node_rtt = Some(self.rtt.lrtt()).filter(|r| *r > 0);
        c.node_peak_rtt = Some(self.rtt.tgr()).filter(|r| *r > 0);
        c.remembered_rtt = peer.and_then(|p| self.rtt.remembered_for(p));
        c
    }

    /// Bring session `i` up to date after an input, recompute its deadline and queue it for sending.
    pub(crate) fn settle(&mut self, i: usize, now: u64) {
        self.settle_core(i, now, true);
    }

    /// As [`settle`](Self::settle); `queue` says whether to put the session on the send queue.
    pub(crate) fn settle_core(&mut self, i: usize, now: u64, queue: bool) {
        self.drain(i, now);
        // A dial is probing this session's peer and a packet came back (QUIET_PROBE): the dial rides at once
        // instead of waiting out its window. The scan is gated on the mark only a probe sets, so it costs one
        // compare for a session no dial is waiting on. Every resolution ends its probe, so the loop ends.
        if self.slots.get(i).is_some_and(|s| {
            s.m.in_use && s.m.probed_until > now && now.saturating_sub(s.m.last_rx) < crate::sub::PARENT_RX
        }) {
            let g = self.slots.get(i).map_or(0, |s| s.m.generation);
            self.trace_probe(now, 1, usize::MAX, (i, g), 0);
            self.ride_probes(i, now);
        }
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        // A quiet-parent probe holds no connection: its only deadline is its end (QUIET_PROBE).
        if slot.conn.is_none() {
            if slot.m.probing {
                self.heap.set(i, Some(slot.m.probe_until));
            }
            return;
        }
        let Some(conn) = slot.conn.as_mut() else { return };
        // A peer that rejected the short Initial does not hold our prekey: the next dial starts with the full one.
        if conn.take_prekey_rejected()
            && let Some(peer) = slot.m.peer
        {
            self.ekk.remove(&peer);
        }
        // The keepalive is handed over before the connection's deadline is read below, since its PING timer is part of
        // that deadline, and at every settle, since the interval counts from the last send, which moves while the plan
        // may not.
        #[cfg(feature = "trace")]
        let mut rec: Option<SettleRecord> = None;
        let mut probe_ping = false;
        let plan = if !conn.is_closed() && conn.is_connected() {
            let direct = !conn.active_is_relay();
            let in_flight = conn.recovery().packets_in_flight() > 0;
            let mut plan = Inputs {
                role: slot.m.role,
                dialer: slot.m.client,
                direct,
                now,
                last_tx: slot.m.last_tx,
                last_rx: slot.m.last_rx,
                last_app: slot.m.last_app,
                quiet_until: self.quiet_until,
                in_flight,
            }
            .plan();
            // A dial is probing this session's peer (QUIET_PROBE): one ping goes out for the probe, at once. A
            // pulse session's keepalive is the layer above's: the plan reports one due now and the carrier
            // carries it (`Command::Pulse` marks it sent). For the rest the timer sends the session's own ping
            // (run_timer), so the connection's keepalive stands down until the marker says the ping went.
            if slot.m.probed_until > now && slot.m.probed_ping_for != slot.m.probed_until {
                if slot.m.pulse {
                    plan.ping_at = Some(now);
                } else {
                    plan.ping_at = None;
                    probe_ping = true;
                }
            }
            let interval = if slot.m.pulse { None } else { plan.ping_at.map(|p| p.saturating_sub(slot.m.last_tx)) };
            conn.set_keepalive(interval);
            #[cfg(feature = "trace")]
            {
                rec = Some(SettleRecord {
                    now,
                    session: crate::SessionId::new(i, slot.m.generation).0,
                    role: slot.m.role,
                    dialer: slot.m.client,
                    direct,
                    last_tx: slot.m.last_tx,
                    last_rx: slot.m.last_rx,
                    last_app: slot.m.last_app,
                    quiet_until: self.quiet_until,
                    in_flight,
                    pulse: slot.m.pulse,
                    ping_at: plan.ping_at,
                    review_at: plan.review_at,
                    changed: plan != slot.m.plan,
                    interval,
                    own: 0,
                    standby: None,
                    acp: None,
                    end: None,
                    pulse_due: false,
                    deadline: None,
                });
            }
            Some(plan)
        } else {
            None
        };
        // The connection's own deadline, asked once: nothing below changes it but the node's round trips.
        let Some(mut own) = conn.poll_timeout() else {
            self.free_slot(i, now);
            return;
        };
        let closing = conn.is_closed();
        let peak = conn.recovery().peak_rtt();
        if peak != slot.m.seen_peak {
            slot.m.seen_peak = peak;
            self.rtt.note_peak(peak);
            self.node_ver += 1;
            trace!(self, now, Rtt {
                lrtt: self.rtt.lrtt(),
                tgr: self.rtt.tgr(),
                hs_floor: self.rtt.hs_floor(),
            });
        }
        // The connection sees only what this side writes: tell it until when the session carries application data.
        conn.set_app_until(slot.m.last_app.saturating_add(ACTIVE_KEEP));
        if slot.m.node_ver != self.node_ver {
            slot.m.node_ver = self.node_ver;
            conn.set_node_rtt(self.rtt.tgr(), self.rtt.lrtt(), self.rtt.thin_node());
            // The node's round trips move a handshake's timers: ask again (the phase did not change, so there is one).
            own = conn.poll_timeout().unwrap_or(own);
        }
        let mut deadline = if closing { deadline_after(now, CLOSE_GRACE) } else { Some(own) };
        let mut note = |d: Option<u64>| {
            if let Some(d) = d {
                deadline = Some(deadline.map_or(d, |c| c.min(d)));
            }
        };
        #[cfg(feature = "trace")]
        let mut standby: Option<u64> = None;
        if let Some(plan) = plan {
            if probe_ping {
                note(Some(now));
            }
            if plan != slot.m.plan {
                slot.m.plan = plan;
                trace!(self, now, Keepalive {
                    slot: i as u64,
                    ping_at: plan.ping_at.unwrap_or(u64::MAX),
                    review_at: plan.review_at.unwrap_or(u64::MAX),
                });
            }
            note(plan.review_at);
            slot.m.pulse_due = slot.m.pulse && plan.ping_at.is_some_and(|p| p <= now);
            if slot.m.pulse {
                // A keepalive already due waits for the layer above; only a later one is a deadline.
                note(plan.ping_at.filter(|p| *p > now));
            }
            // Every valid standby path the connection tracks, as in the reference model: one added to the session and
            // never sent on is due at once.
            let active = conn.active_path();
            for (id, _, valid) in conn.path_list() {
                if Some(id) != active && valid {
                    let due = standby_due(now, slot.m.path_tx(id), slot.m.last_app);
                    note(due);
                    #[cfg(feature = "trace")]
                    {
                        standby = due.into_iter().chain(standby).min();
                    }
                }
            }
            note(slot.m.acp_recheck);
            #[cfg(feature = "trace")]
            if let Some(r) = rec.as_mut() {
                r.own = own;
                r.standby = standby;
                r.acp = slot.m.acp_recheck;
                r.pulse_due = slot.m.pulse_due;
            }
        }
        #[cfg(feature = "trace")]
        let mut end = None;
        if slot.m.unauth {
            let e = slot.half_open_end(self.rtt.thin_node());
            note(Some(e));
            #[cfg(feature = "trace")]
            {
                end = Some(e);
            }
        }
        self.heap.set(i, deadline);
        #[cfg(feature = "trace")]
        if let Some(mut r) = rec {
            r.end = end;
            r.deadline = deadline;
            self.trace.settles.push(r);
        }
        self.sync_cids(i, false);
        self.sync_route(i);
        if queue {
            self.mark_dirty(i, now);
        }
    }

    /// The next time [`handle_timeout`](Self::handle_timeout) must run, or `None` when no session has a timer.
    /// While the event queue is near full no timer is due: read events with `poll_event` first.
    pub fn poll_timeout(&self) -> Option<u64> {
        self.heap.peek().map(|(t, _)| t).filter(|_| !self.events.stalled())
    }

    /// Run every timer that is due at `now`.
    pub fn handle_timeout(&mut self, now: u64) {
        self.last_now = now;
        self.orphans.expire(now);
        for _ in 0..K {
            if self.events.stalled() {
                return;
            }
            let Some((t, i)) = self.heap.peek() else { return };
            if t > now {
                return;
            }
            self.heap.set(i, None);
            self.run_timer(i, now);
            if self.heap.deadline(i).is_some_and(|d| d <= now) {
                self.heap.set(i, deadline_after(now, 1));
            }
        }
    }

    fn run_timer(&mut self, i: usize, now: u64) {
        let thin = self.rtt.thin_node();
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        if slot.m.unauth && now >= slot.half_open_end(thin) {
            trace!(self, now, HalfOpenExpired { slot: i as u64 });
            self.free_slot(i, now);
            return;
        }
        if slot.m.acp_recheck.is_some_and(|t| t <= now) {
            slot.m.acp_recheck = None;
            self.ask_acp(i, now, true);
        }
        // A quiet-parent probe holds no connection: at its end it rides the probed session or makes its own
        // handshake (QUIET_PROBE).
        if let Some((pidx, pgen)) = self.slots.get(i).filter(|s| s.m.probing).map(|s| (s.m.probe_parent as usize, s.m.probe_of_gen)) {
            if now >= self.slots.get(i).map_or(0, |s| s.m.probe_until) {
                self.resolve_probe(i, now);
                // A mark of 0 means a nested `ride_probes` already resolved every probe of the parent.
                if self.slots.get(pidx).is_some_and(|s| s.m.in_use && s.m.generation == pgen && s.m.probed_until != 0) {
                    self.recompute_probed(pidx, now);
                }
            }
            return;
        }
        // Only a session with a re-join running has floors to take and challenges to report: the timer of every
        // other session (a bulk transfer's fires for each paced burst) does none of that work.
        let rejoining = self
            .slots
            .get(i)
            .and_then(|s| s.conn.as_ref())
            .is_some_and(pinc_transport::conn::Connection::rejoin_running);
        let floors = if rejoining { self.rejoin_floors(i) } else { [None; NP] };
        let short_until = self.short_until();
        let Some(slot) = self.slots.get_mut(i) else { return };
        let Some(conn) = slot.conn.as_mut() else { return };
        // A dial is probing this session's peer (QUIET_PROBE): the session pings its peer at once so the probe
        // learns whether the peer lives. Pulse sessions ping through the carrier via the plan; the rest ping here,
        // once per probe: the marker goes even when the path is gone, so the session returns to its own plan
        // instead of waking for a ping it has nowhere to send.
        if slot.m.probed_until > now
            && !slot.m.pulse
            && slot.m.probed_ping_for != slot.m.probed_until
        {
            if let Some(active) = conn.active_path() {
                let _ = conn.ping_path(active);
            }
            slot.m.probed_ping_for = slot.m.probed_until;
        }
        // A standby path that carried nothing for 5 s while data moves is pinged to keep its mapping open.
        let active = conn.active_path();
        let mut probe: [Option<pinc_transport::conn::PathId>; NP] = [None; NP];
        let mut n = 0;
        for (id, _, valid) in conn.path_list() {
            if Some(id) != active
                && valid
                && standby_due(now, slot.m.path_tx(id), slot.m.last_app).is_some_and(|d| d <= now)
                && let Some(s) = probe.get_mut(n)
            {
                *s = Some(id);
                n += 1;
            }
        }
        let mut env = env!(self, now);
        for id in probe.iter().flatten() {
            let _ = conn.ping_path(*id);
            if let Some(p) = slot.m.stamp(*id) {
                p.tx = now;
            }
        }
        for (id, at) in floors.into_iter().flatten() {
            conn.set_rejoin_floor(id, at);
        }
        // A resend of a dial reads whether UDP was heard lately now, not as of the dial.
        conn.set_short_until(short_until);
        conn.handle_timeout(&mut env, &mut lent!(self));
        let mut fired: [Option<PathId>; NP] = [None; NP];
        if rejoining {
            for f in &mut fired {
                *f = conn.take_rejoin_fired();
            }
        }
        let remotes = fired.map(|f| f.and_then(|id| self.path_addrs(id)).map(|(_, remote)| remote));
        for remote in remotes.into_iter().flatten() {
            // The newest goes to the end of the order, so a full table forgets the oldest address.
            self.rejoin_sent.remove(&remote);
            self.rejoin_sent.insert(remote, now);
        }
        self.settle(i, now);
    }

    /// For each path of session `i` still being re-challenged on a thin session, when the spacing to the last re-join
    /// challenge of this node to the same address ends (0 when there was none).
    fn rejoin_floors(&self, i: usize) -> [Option<(PathId, u64)>; NP] {
        let mut out = [None; NP];
        let Some(conn) = self.slots.get(i).and_then(|s| s.conn.as_ref()) else { return out };
        let gap = RJ_THIN_GAP.max(self.rtt.tgr());
        for (d, id) in out.iter_mut().zip(conn.rejoin_paths()) {
            let last = self.path_addrs(id).and_then(|(_, remote)| self.rejoin_sent.get(&remote).copied());
            *d = Some((id, last.map_or(0, |t| t.saturating_add(gap))));
        }
        out
    }
}

#[cfg(feature = "trace")]
ep_impl! {
    /// The oldest settle record not read yet (cargo feature `trace`).
    pub fn poll_settle(&mut self) -> Option<SettleRecord> {
        self.trace.settles.pop()
    }

    /// How many settle records were dropped because nobody read them (cargo feature `trace`).
    #[must_use]
    pub const fn settle_dropped(&self) -> u64 {
        self.trace.settles.dropped()
    }
}
