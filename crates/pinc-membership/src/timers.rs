//! Timers: renewal, the tick, the slow tick, and the quiet-window rechecks.
//!
//! The host asks [`Membership::poll_timeout`] for the next deadline and calls [`Membership::on_timeout`] when it
//! passes (or sooner; every call is safe at any time). A member ticks every 0.5 s and does session management every
//! 5 s; a hub does everything every 1 s.
//!
//! Invariants: a tick that arrives later than [`WAKE_GAP`] after it was due (the first is due at the start) is a
//! suspension: the node renews every hub at once with a snapshot request and opens a quiet window, so removals
//! queued while it slept are re-checked, not believed (a heal leaves removals already waiting at their own instant);
//! a window re-checks removals after [`QUIET`] and again after [`RECHECK_GAP`]. An omission clock that runs out is
//! swept at the tick that finds it due, not at the next slow tick.

use crate::codec::NodeId;
use crate::consts::{ACK_WAIT, HS_GRACE, HUB_STALE, HUB_TICK, NODE_TICK, PULSE_FRESH, RTT_QUIET, SLOW_TICK, WAKE_GAP};
use crate::event::{QuietCause, Trace};
use crate::node::{Membership, next_key};
use crate::session::{CloseReason, Host, Nanos};

impl Membership {
    /// When the first tick, or the next one, is due: the first is due at the start.
    fn tick_due(&self) -> Nanos {
        self.next_tick.unwrap_or(self.born)
    }

    /// When the host should next call [`Membership::on_timeout`].
    pub fn poll_timeout(&self) -> Nanos {
        let t = self.next_renew.min(self.tick_due());
        self.next_conf.map_or(t, |c| t.min(c))
    }

    /// Run whatever is due at `now`.
    ///
    /// Host contract: before a call that serves a due timer, the host hands over the input it already holds (frames,
    /// session events, transport evidence). A hub confirms a member down on the call that finds the deadline due, so
    /// an answer the host holds but has not handed over does not count.
    pub fn on_timeout<H: Host>(&mut self, h: &mut H, now: Nanos) {
        if self.leaving {
            return;
        }
        self.pulse_refresh(h, now);
        self.refresh_local(h, now);
        if now >= self.next_renew {
            self.renew(h, now, false, true);
        }
        if self.next_conf.is_some_and(|c| now >= c) {
            self.next_conf = None;
            if self.is_hub {
                let mut cur: Option<NodeId> = None;
                while let Some(m) = next_key(&self.susp, cur.as_ref()) {
                    cur = Some(m);
                    self.carrier_watch(h, now, &m);
                }
            }
        }
        if now >= self.next_tick.unwrap_or(0) {
            if !self.is_hub && now.saturating_sub(self.tick_due()) > WAKE_GAP {
                self.begin_quiet(now, QuietCause::LateTimer);
                self.renew(h, now, true, false);
            }
            self.next_tick = Some(now.saturating_add(if self.is_hub { HUB_TICK } else { NODE_TICK }));
            self.tick(h, now);
        }
    }

    fn tick<H: Host>(&mut self, h: &mut H, now: Nanos) {
        self.recheck_due(h, now);
        if self.next_absent.is_some_and(|t| now >= t) {
            self.sweep_absent(h, now);
        }
        if self.sent != Some((self.ver, self.th)) {
            self.renew(h, now, false, false);
        }
        if self.is_hub || now >= self.next_slow {
            if !self.is_hub {
                self.next_slow = now.saturating_add(SLOW_TICK);
            }
            self.slow_tick(h, now);
        }
        if self.is_hub {
            self.hub_tick(h, now);
        }
    }

    fn slow_tick<H: Host>(&mut self, h: &mut H, now: Nanos) {
        // A HELLO unanswered for ACK_WAIT means the hub session is dead (a handover, a rebind): close it.
        let mut cur: Option<NodeId> = None;
        while let Some(hub) = next_key(&self.hello_at, cur.as_ref()) {
            cur = Some(hub);
            let Some(t0) = self.hello_at.get(&hub).copied().flatten() else {
                continue;
            };
            let opened = self.up.get(&hub).copied().unwrap_or(now);
            if now.saturating_sub(t0) > ACK_WAIT && now.saturating_sub(opened) > HS_GRACE {
                if let Some(ev) = h.evidence(&hub) {
                    // The watchdog waits four round trips on slow paths and spares a session that still receives.
                    let wt = ACK_WAIT.max(ev.srtt.saturating_mul(4));
                    if now.saturating_sub(t0) <= wt || now.saturating_sub(ev.last_rx) < wt / 2 {
                        continue;
                    }
                }
                self.hello_at.insert(hub, None);
                if self.up.contains_key(&hub) {
                    h.close(&hub, CloseReason::NoAck);
                    self.drop_peer(h, now, &hub);
                }
            }
        }
        if !self.is_hub {
            self.sample_session_rtts(h, now);
        }
        self.drop_stale_hubs(h, now);
        self.sweep_absent(h, now);
        let primary_down = match self.primary {
            None => true,
            Some(p) => !self.hub_up(now, &p),
        };
        if primary_down {
            self.reselect(h, now);
        }
    }

    /// The hub sessions' transport round trips feed the nearest-hub choice, with no HELLO round trip needed.
    fn sample_session_rtts<H: Host>(&mut self, h: &mut H, now: Nanos) {
        for i in 0..self.boot.len() {
            let Some(hub) = self.boot.get(i).copied() else {
                continue;
            };
            if hub == self.me {
                continue;
            }
            if let Some(ev) = h.evidence(&hub)
                && self.up.contains_key(&hub)
                && ev.srtt > 0
                && now.saturating_sub(ev.last_rx) < PULSE_FRESH
                && ev.inflight <= RTT_QUIET
            {
                self.rtt_sample(&hub, ev.srtt);
            }
        }
        let cur = self.primary.and_then(|p| self.hrtt.get(&p).copied());
        let better = self.boot.iter().any(|x| {
            *x != self.me
                && self.primary != Some(*x)
                && self.hub_up(now, x)
                && self
                    .hrtt
                    .get(x)
                    .is_some_and(|r| cur.is_none_or(|c| r.saturating_add(crate::consts::HYST_ABS) < c * 2 / 3))
        });
        if better {
            self.reselect(h, now);
        }
    }

    /// A stale hub's copy is dropped while another hub is fresh, and its session is closed so a fresh one is made.
    /// While removals are held (a member with no confirmed home) the copies are kept: a stale copy feeds nothing, but
    /// the members only it lists stay listed, so the confirmed home's snapshot ages them (`mark_view_absent`) instead
    /// of removing at once members no hub reported down.
    fn drop_stale_hubs<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let stale = self.hv.keys().filter(|k| !self.hub_up(now, k)).count();
        if stale == 0 || stale >= self.hv.len() || self.source(now).hold {
            return;
        }
        let mut changed = false;
        let mut cur: Option<NodeId> = None;
        while let Some(hub) = next_key(&self.hv, cur.as_ref()) {
            cur = Some(hub);
            if self.hub_up(now, &hub) {
                continue;
            }
            let Some(copy) = self.hv.remove(&hub) else {
                continue;
            };
            self.trace(Trace::HubStale { hub });
            if self.up.contains_key(&hub) && now.saturating_sub(self.heard.get(&hub).copied().unwrap_or(0)) >= HUB_STALE
            {
                h.close(&hub, CloseReason::Stale);
            }
            for m in copy.entries.keys() {
                changed |= self.recompute_one(h, now, m);
            }
        }
        if changed {
            self.bump();
        }
    }
}
