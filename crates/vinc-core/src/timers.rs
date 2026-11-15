//! Timers and the per-session bookkeeping that follows every input.
//!
//! After any call that touches a session the endpoint settles it: it reads the session's events, hands it the node
//! round trips if they changed, applies the keepalive plan, registers new connection ids, forgets that a peer which
//! rejected a short Initial holds the node's prekey, brings the session's entry in the table of sessions by address in
//! line with its path, and recomputes the one deadline the session contributes to the heap. The deadline is the
//! earliest of the connection's own timer, the keepalive review, the next ping of a standby path, the end of an
//! unauthenticated session's life (30 s, 60 s on a thin node: as long as its handshake may last), and the moment a
//! cached access answer has 5 s left.
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
//! after a timer is strictly later than the time of the call, so a timer cannot spin.

use vinc_transport::conn::{Config, PathId, RJ_THIN_GAP, connect_limit};

use crate::endpoint::{CLOSE_GRACE, env, ep_impl};
use crate::keepalive::{ACTIVE_KEEP, Inputs, standby_due};
use crate::trace::trace;

ep_impl! {
    /// The configuration of a new connection: the base configuration with the node round trips filled in. For a
    /// dial, `peer` selects the remembered round trip.
    pub(crate) fn conn_config(&self, peer: Option<&vinc_crypto::NodeId>) -> Config {
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
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        let Some(conn) = slot.conn.as_mut() else { return };
        // A peer that rejected the short Initial does not hold our prekey: the next dial starts with the full one.
        if conn.take_prekey_rejected()
            && let Some(peer) = slot.m.peer
        {
            self.ekk.remove(&peer);
        }
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
        let mut deadline = Some(if closing { now.saturating_add(CLOSE_GRACE) } else { own });
        let mut note = |d: Option<u64>| {
            if let Some(d) = d {
                deadline = Some(deadline.map_or(d, |c| c.min(d)));
            }
        };
        if !closing && conn.is_connected() {
            let plan = Inputs {
                role: slot.m.role,
                dialer: slot.m.client,
                direct: !conn.active_is_relay(),
                now,
                last_tx: slot.m.last_tx,
                last_rx: slot.m.last_rx,
                last_app: slot.m.last_app,
                quiet_until: self.quiet_until,
                in_flight: conn.recovery().packets_in_flight() > 0,
            }
            .plan();
            if plan != slot.m.plan {
                slot.m.plan = plan;
                let interval = plan.ping_at.map(|p| p.saturating_sub(slot.m.last_tx));
                conn.set_keepalive(if slot.m.pulse { None } else { interval });
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
                    note(standby_due(now, slot.m.path_tx(id), slot.m.last_app));
                }
            }
            note(slot.m.acp_recheck);
        }
        if slot.m.unauth {
            note(Some(slot.m.created.saturating_add(connect_limit(self.rtt.thin_node()))));
        }
        self.heap.set(i, deadline);
        self.sync_cids(i, false);
        self.sync_route(i);
        if queue {
            self.mark_dirty(i);
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
                self.heap.set(i, Some(now.saturating_add(1)));
            }
        }
    }

    fn run_timer(&mut self, i: usize, now: u64) {
        let life = connect_limit(self.rtt.thin_node());
        let Some(slot) = self.slots.get_mut(i) else { return };
        if !slot.m.in_use {
            return;
        }
        if slot.m.unauth && now >= slot.m.created.saturating_add(life) {
            trace!(self, now, HalfOpenExpired { slot: i as u64 });
            self.free_slot(i, now);
            return;
        }
        if slot.m.acp_recheck.is_some_and(|t| t <= now) {
            slot.m.acp_recheck = None;
            self.ask_acp(i, now, true);
        }
        // Only a session with a re-join running has floors to take and challenges to report: the timer of every
        // other session (a bulk transfer's fires for each paced burst) does none of that work.
        let rejoining = self
            .slots
            .get(i)
            .and_then(|s| s.conn.as_ref())
            .is_some_and(vinc_transport::conn::Connection::rejoin_running);
        let floors = if rejoining { self.rejoin_floors(i) } else { [None; NP] };
        let short_until = self.short_until();
        let Some(slot) = self.slots.get_mut(i) else { return };
        let Some(conn) = slot.conn.as_mut() else { return };
        // A standby path that carried nothing for 5 s while data moves is pinged to keep its mapping open.
        let active = conn.active_path();
        let mut probe: [Option<vinc_transport::conn::PathId>; NP] = [None; NP];
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
        conn.handle_timeout(&mut env);
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
