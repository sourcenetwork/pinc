//! The member view.
//!
//! A node keeps one copy of each hub's roster (`hv`) and derives its view (`members`) from them: while the home
//! hub's snapshot is confirmed the view follows it alone; otherwise it is the union of the fresh hubs' copies, the
//! highest incarnation winning, with removals held.
//!
//! A snapshot never removes a member on its own. A complete snapshot that omits a member starts that member's lease
//! clock; the member stays in the view and is suspected, and leaves it only when the hub reports it down (a delta or
//! a DOWN of the same or a newer incarnation), or when a full lease passes without any hub listing it again. Removals
//! found while a quiet window is open (after a late timer or a partition heal) are re-checked at its end.
//!
//! Invariants: the view epoch only increases and increases once per batch of changes; the view never lists the node
//! itself; a revoked node is never listed; every removal goes through [`Membership::recompute_one`], the one place
//! that decides it.

use crate::codec::{Alive, Entry, Hello, NodeId, Record, Snap};
use crate::consts::{HYST_ABS, LEASE, PULSE_FRESH, RENEW};
use crate::event::{Event, Removal, Trace};
use crate::node::{CopyEntry, HubCopy, Membership, ViewEntry, next_key};
use crate::session::{Host, Nanos, Route};
use alloc::collections::BTreeSet;

use crate::codec::Frame;
use crate::consts::MAX_TABLE;

const RTT_UNKNOWN: Nanos = 1 << 40;

/// Which hub copies feed the view right now.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Source {
    /// Only this hub's copy counts (the home hub, confirmed).
    only: Option<NodeId>,
    /// Removals are held (no confirmed home view).
    hold: bool,
    /// At least one hub is fresh; otherwise every copy counts.
    any_fresh: bool,
}

impl Membership {
    pub(crate) fn refresh_local<H: Host>(&mut self, h: &H, now: Nanos) {
        self.ver = h.version();
        self.th = self.tag.tag(now, h);
    }

    pub(crate) fn hello_to<H: Host>(&mut self, h: &mut H, _now: Nanos, peer: &NodeId, snap: bool) {
        let homed = !self.is_hub && self.primary.as_ref() == Some(peer);
        let f = Frame::Hello(Hello {
            rec: Record {
                inc: self.inc.word(),
                ver: self.ver,
                thash: self.th,
            },
            snap,
            homed,
        });
        self.tx(h, peer, Route::Session, &f);
    }

    fn bump_record<H: Host>(&mut self, h: &mut H) {
        if let Ok(w) = self.inc.next_record(h) {
            self.trace(Trace::Incarnation { inc: w });
        } else {
            self.seal_failed = true;
            self.trace(Trace::SealFailed);
        }
    }

    /// Whether the session with `hub` is demonstrably alive on transport evidence alone.
    fn pulse_fresh<H: Host>(h: &H, now: Nanos, hub: &NodeId) -> bool {
        h.evidence(hub)
            .is_some_and(|e| e.pto == 0 && now.saturating_sub(e.last_rx) < PULSE_FRESH)
    }

    /// Renew the lease on every hub with a session. `periodic` renewals are skipped where the transport already
    /// proves the session alive.
    pub(crate) fn renew<H: Host>(&mut self, h: &mut H, now: Nanos, force_snap: bool, mut periodic: bool) {
        if self.sent.is_some_and(|s| s != (self.ver, self.th)) {
            self.bump_record(h);
        }
        if self.sent != Some((self.ver, self.th)) {
            periodic = false;
        }
        self.sent = Some((self.ver, self.th));
        let cur = Record {
            inc: self.inc.word(),
            ver: self.ver,
            thash: self.th,
        };
        if self.is_hub && self.own != cur {
            self.own = cur;
            let me = self.me;
            self.push_delta(h, now, &me, cur, Alive::Alive);
        }
        for i in 0..self.boot.len() {
            let Some(hub) = self.boot.get(i).copied() else {
                continue;
            };
            if hub == self.me || !self.up.contains_key(&hub) {
                continue;
            }
            let snap = force_snap || !self.hv.contains_key(&hub);
            if periodic
                && !snap
                && (self.primary != Some(hub) || self.home_ok == Some(hub))
                && Self::pulse_fresh(h, now, &hub)
            {
                self.trace(Trace::HelloSuppressed { hub });
                continue;
            }
            self.hello_at.entry(hub).or_insert(now);
            self.hsent.insert(hub, now);
            self.hello_to(h, now, &hub, snap);
        }
        self.next_renew = now.saturating_add(RENEW);
    }

    /// Pick the primary hub: the lowest round trip, keeping the current one unless the new one beats it by 20 ms and
    /// a quarter.
    pub(crate) fn reselect<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let p = if self.is_hub {
            Some(self.me)
        } else {
            let mut best: Option<((Nanos, usize), NodeId)> = None;
            for (i, hub) in self.boot.iter().filter(|x| **x != self.me).enumerate() {
                if self.hub_up(now, hub) {
                    let k = (self.hrtt.get(hub).copied().unwrap_or(RTT_UNKNOWN), i);
                    if best.is_none_or(|(bk, _)| k < bk) {
                        best = Some((k, *hub));
                    }
                }
            }
            let mut p = best.map(|(_, x)| x);
            if let (Some(np), Some(cur)) = (p, self.primary)
                && np != cur
                && self.hub_up(now, &cur)
            {
                let rc = self.hrtt.get(&cur).copied().unwrap_or(RTT_UNKNOWN);
                let rn = self.hrtt.get(&np).copied().unwrap_or(RTT_UNKNOWN);
                if rn.saturating_add(HYST_ABS) >= rc.saturating_mul(3) / 4 {
                    p = Some(cur);
                }
            }
            p
        };
        let Some(p) = p else { return };
        if self.primary == Some(p) {
            return;
        }
        let old = self.primary;
        self.primary = Some(p);
        self.trace(Trace::Primary { hub: p });
        if !self.is_hub {
            // The new home sends its combined view as a snapshot and our deltas from now on.
            self.home_ok = None;
            self.hello_to(h, now, &p, true);
            if let Some(o) = old
                && self.up.contains_key(&o)
            {
                self.hello_to(h, now, &o, false);
            }
        }
        h.primary_changed(old.as_ref(), &p);
    }

    /// Fold a transport round trip sample into the hub's smoothed round trip.
    pub(crate) fn rtt_sample(&mut self, hub: &NodeId, r: Nanos) {
        let v = self.hrtt.get(hub).map_or(r, |old| r.min((3 * old + r) / 4));
        self.hrtt.insert(*hub, v);
    }

    pub(crate) fn bump(&mut self) {
        self.epoch += 1;
        let members = u32::try_from(self.members.len()).unwrap_or(u32::MAX);
        self.emit(Event::ViewChanged {
            epoch: self.epoch,
            members,
        });
    }

    fn source(&self, now: Nanos) -> Source {
        let home = self
            .primary
            .filter(|p| !self.is_hub && self.home_ok == Some(*p) && self.hv.contains_key(p) && self.hub_up(now, p));
        match home {
            Some(p) => Source {
                only: Some(p),
                hold: false,
                any_fresh: true,
            },
            None => Source {
                only: None,
                hold: !self.is_hub,
                any_fresh: self.hv.keys().any(|k| self.hub_up(now, k)),
            },
        }
    }

    /// A hub told us about ourselves, or the incarnation it holds for us is above ours.
    fn on_self_entry<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId, rec: Record, alive: Alive) {
        if *hub == self.me {
            return;
        }
        self.trace(Trace::SelfDelta { hub: *hub });
        if alive == Alive::Alive && rec.inc > self.inc.word() {
            // Reincarnated behind our back (a clock that went back, a lost store): move above it.
            match self.inc.observe(h, rec.inc) {
                Ok(true) => {
                    self.trace(Trace::Incarnation { inc: self.inc.word() });
                    self.renew(h, now, false, false);
                }
                Ok(false) => {}
                Err(_) => {
                    self.seal_failed = true;
                    self.trace(Trace::SealFailed);
                }
            }
        } else if alive != Alive::Alive || rec.inc < self.inc.word() {
            // A hub dropped us, or holds an older record: attach again at once.
            self.hello_to(h, now, hub, false);
        } else {
            // The hub restored us (a returning carrier): subscribe again, so nothing was silently lost.
            h.resubscribe(hub);
        }
    }

    /// One roster change from `hub` (also this hub's own, with `hub == self.me`).
    pub(crate) fn apply_delta<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId, e: &Entry<'_>) {
        if *e.member == self.me {
            self.on_self_entry(h, now, hub, e.rec, e.alive);
            return;
        }
        if self.revoked.contains(e.member) {
            return;
        }
        if !self.hv.contains_key(hub) {
            if self.hv.len() >= crate::consts::MAX_HUBS {
                return;
            }
            self.hv.insert(*hub, HubCopy::default());
        }
        if let Some(c) = self.hv.get_mut(hub) {
            match e.alive {
                Alive::Alive => {
                    if c.entries.len() < MAX_TABLE || c.entries.contains_key(e.member) {
                        let round = c.round;
                        c.entries.insert(
                            *e.member,
                            CopyEntry {
                                rec: e.rec,
                                round,
                                absent_since: None,
                            },
                        );
                        self.left.remove(e.member);
                    }
                }
                Alive::Down | Alive::Left => {
                    // Down at the same or a newer incarnation than the copy holds.
                    if c.entries
                        .get(e.member)
                        .is_some_and(|x| x.rec.inc >> 16 <= e.rec.inc >> 16)
                    {
                        c.entries.remove(e.member);
                        if e.alive == Alive::Left && self.left.len() < MAX_TABLE {
                            self.left.insert(*e.member);
                        }
                    }
                }
            }
        }
        if self.recompute_one(h, now, e.member) {
            self.bump();
        }
    }

    /// A hub reported `member` down with proof.
    pub(crate) fn apply_down<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId, member: &NodeId, inc: u64) {
        let rec = Record {
            inc,
            ver: 0,
            thash: [0; 8],
        };
        let e = Entry {
            member,
            rec,
            alive: Alive::Down,
        };
        self.apply_delta(h, now, hub, &e);
    }

    /// A snapshot frame from `hub`.
    pub(crate) fn apply_snap<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId, s: &Snap<'_>) {
        if !self.hv.contains_key(hub) {
            if self.hv.len() >= crate::consts::MAX_HUBS {
                return;
            }
            self.hv.insert(*hub, HubCopy::default());
        }
        let mut round = 0;
        if let Some(c) = self.hv.get_mut(hub) {
            if !c.open {
                c.round = c.round.wrapping_add(1);
                c.open = true;
            }
            round = c.round;
        }
        if !self.is_hub && self.primary.as_ref() == Some(hub) {
            self.home_ok = Some(*hub);
            self.home_seen = true;
        }
        let mut changed = false;
        let mut n = 0u32;
        for e in s.entries() {
            n += 1;
            if *e.member == self.me {
                self.on_self_entry(h, now, hub, e.rec, e.alive);
                continue;
            }
            if self.revoked.contains(e.member) {
                continue;
            }
            if let Some(c) = self.hv.get_mut(hub) {
                if c.entries.len() >= MAX_TABLE && !c.entries.contains_key(e.member) {
                    continue;
                }
                c.entries.insert(
                    *e.member,
                    CopyEntry {
                        rec: e.rec,
                        round,
                        absent_since: None,
                    },
                );
            }
            self.left.remove(e.member);
            changed |= self.recompute_one(h, now, e.member);
        }
        self.trace(Trace::SnapApplied {
            hub: *hub,
            entries: n,
            more: s.more,
        });
        if !s.more {
            if let Some(c) = self.hv.get_mut(hub) {
                c.open = false;
            }
            if !s.partial {
                changed |= self.mark_absent(h, now, hub, round);
            }
            if self.primary.as_ref() == Some(hub) {
                // A snapshot means a fresh attachment: the hub forgot our subscriptions with the old session.
                h.resubscribe(hub);
            }
        }
        if changed {
            self.bump();
        }
    }

    /// A complete snapshot of `hub` listed round `round`: everything else in its copy is omitted, which starts that
    /// member's lease clock without removing it.
    fn mark_absent<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId, round: u32) -> bool {
        let mut changed = false;
        let mut cur: Option<NodeId> = None;
        loop {
            let next = self.hv.get(hub).and_then(|c| next_key(&c.entries, cur.as_ref()));
            let Some(m) = next else { break };
            cur = Some(m);
            let mut marked = false;
            if let Some(ce) = self.hv.get_mut(hub).and_then(|c| c.entries.get_mut(&m))
                && ce.round != round
                && ce.absent_since.is_none()
            {
                ce.absent_since = Some(now);
                marked = true;
            }
            if marked {
                self.trace(Trace::Absent { member: m });
                changed |= self.recompute_one(h, now, &m);
            }
        }
        changed
    }

    /// Drop copy entries whose omission has lasted a full lease, and recompute those members.
    pub(crate) fn sweep_absent<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let mut changed = false;
        let mut hcur: Option<NodeId> = None;
        while let Some(hub) = next_key(&self.hv, hcur.as_ref()) {
            hcur = Some(hub);
            let mut cur: Option<NodeId> = None;
            loop {
                let next = self.hv.get(&hub).and_then(|c| next_key(&c.entries, cur.as_ref()));
                let Some(m) = next else { break };
                cur = Some(m);
                let expired = self
                    .hv
                    .get(&hub)
                    .and_then(|c| c.entries.get(&m))
                    .and_then(|e| e.absent_since)
                    .is_some_and(|t| now.saturating_sub(t) >= LEASE);
                if expired {
                    // Kept until recomputed: the removal reason is "lease expired".
                    changed |= self.recompute_one(h, now, &m);
                    if let Some(c) = self.hv.get_mut(&hub) {
                        c.entries.remove(&m);
                    }
                }
            }
        }
        if changed {
            self.bump();
        }
    }

    /// Decide `m`'s place in the view from the hub copies. Returns whether the view changed.
    pub(crate) fn recompute_one<H: Host>(&mut self, h: &mut H, now: Nanos, m: &NodeId) -> bool {
        let src = self.source(now);
        let mut best: Option<(Record, bool)> = None;
        let mut expired = false;
        for (hub, copy) in &self.hv {
            let eligible = src
                .only
                .map_or_else(|| !src.any_fresh || self.hub_up(now, hub), |o| o == *hub);
            if !eligible {
                continue;
            }
            let Some(ce) = copy.entries.get(m) else { continue };
            let absent = ce.absent_since.is_some();
            if ce.absent_since.is_some_and(|t| now.saturating_sub(t) >= LEASE) {
                expired = true;
                continue;
            }
            if best.is_none_or(|(b, babs)| ce.rec.inc > b.inc || (ce.rec.inc == b.inc && babs && !absent)) {
                best = Some((ce.rec, absent));
            }
        }
        let cur = self.members.get(m).copied();
        let Some((best, absent)) = best else {
            return self.remove_from_view(h, now, m, cur, &src, expired);
        };
        let mut changed = false;
        if self.is_hub && cur.is_none_or(|c| c.rec != best) {
            self.home_delta(h, now, m, best, Alive::Alive);
        }
        match cur {
            Some(c) if (best.inc >> 16) <= (c.rec.inc >> 16) => {
                if (best.inc >> 16) == (c.rec.inc >> 16)
                    && best.inc >= c.rec.inc
                    && let Some(e) = self.members.get_mut(m)
                {
                    e.rec.inc = best.inc;
                    if best.ver != c.rec.ver {
                        e.rec.ver = best.ver;
                        self.emit(Event::StackChanged {
                            member: *m,
                            version: best.ver,
                        });
                        changed = true;
                    }
                    if best.thash != c.rec.thash {
                        if let Some(e) = self.members.get_mut(m) {
                            e.rec.thash = best.thash;
                        }
                        self.emit(Event::AddressChanged { member: *m });
                        changed = true;
                    }
                }
            }
            _ => {
                if cur.is_none() && self.members.len() >= MAX_TABLE {
                    return false;
                }
                self.members.insert(
                    *m,
                    ViewEntry {
                        rec: best,
                        suspected: false,
                    },
                );
                self.emit(Event::MemberJoined { member: *m });
                let old = cur
                    .map(|c| (c.rec.ver, c.rec.thash))
                    .or_else(|| self.gone_ver.get(m).copied());
                self.gone_ver.remove(m);
                if let Some((ver, th)) = old {
                    if ver != best.ver {
                        self.emit(Event::StackChanged {
                            member: *m,
                            version: best.ver,
                        });
                    }
                    if cur.is_none() && th != best.thash {
                        self.emit(Event::AddressChanged { member: *m });
                    }
                }
                changed = true;
            }
        }
        if let Some(e) = self.members.get_mut(m)
            && e.suspected != absent
        {
            e.suspected = absent;
            if absent {
                self.emit(Event::MemberSuspected { member: *m });
            }
        }
        changed
    }

    fn remove_from_view<H: Host>(
        &mut self,
        h: &mut H,
        now: Nanos,
        m: &NodeId,
        cur: Option<ViewEntry>,
        src: &Source,
        expired: bool,
    ) -> bool {
        let Some(c) = cur else { return false };
        if src.hold {
            return false;
        }
        if now < self.quiet_until && self.recheck.len() < MAX_TABLE {
            self.recheck.insert(*m);
            self.trace(Trace::Deferred { member: *m });
            return false;
        }
        self.members.remove(m);
        if self.gone_ver.len() < MAX_TABLE || self.gone_ver.contains_key(m) {
            self.gone_ver.insert(*m, (c.rec.ver, c.rec.thash));
        }
        let left = self.left.remove(m);
        let (why, alive) = if left {
            (Removal::Left, Alive::Left)
        } else if expired {
            (Removal::LeaseExpired, Alive::Down)
        } else {
            (Removal::Reported, Alive::Down)
        };
        self.trace(Trace::Removed { member: *m, why });
        self.emit(if left {
            Event::MemberLeft { member: *m }
        } else {
            Event::MemberConfirmedDown { member: *m }
        });
        if self.is_hub {
            self.home_delta(h, now, m, c.rec, alive);
        }
        true
    }

    /// Recompute the members whose removal a quiet window deferred.
    pub(crate) fn recheck_now<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let set: BTreeSet<NodeId> = core::mem::take(&mut self.recheck);
        let mut changed = false;
        for m in &set {
            changed |= self.recompute_one(h, now, m);
        }
        if changed {
            self.bump();
        }
    }

    /// A hub's combined view changed for `m`: tell the members whose home this hub is.
    pub(crate) fn home_delta<H: Host>(&mut self, h: &mut H, _now: Nanos, m: &NodeId, rec: Record, alive: Alive) {
        let mut cur: Option<NodeId> = None;
        while let Some(p) = crate::node::next_in(&self.homed, cur.as_ref()) {
            cur = Some(p);
            if p != *m {
                self.delta_to(h, &p, m, rec, alive);
            }
        }
    }
}
