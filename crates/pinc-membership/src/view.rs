//! The member view.
//!
//! A node keeps one copy of each hub's roster (`hv`) and derives its view (`members`) from them: while the home
//! hub's snapshot is confirmed the view follows it alone; otherwise it is the union of the fresh hubs' copies, the
//! highest incarnation winning, with removals held.
//!
//! A snapshot never removes a member on its own. A complete snapshot that omits a member starts that member's lease
//! clock (the complete snapshot of the confirmed home does so for every member of the view it omits, whichever hub's
//! copy the member came from); the member stays in the view, with no event, and leaves it only when the hub reports
//! it down (a delta or a DOWN of the same or a newer incarnation), or when a full lease passes without any hub
//! listing it again. Removals found while a quiet window is open (after a late timer or a partition heal) are
//! re-checked at its end; a heal never defers a removal an earlier window already deferred, a late timer defers
//! every removal waiting.
//!
//! Invariants: the view epoch only increases and increases once per batch of changes; the view never lists the node
//! itself; a revoked node is never listed; every removal goes through [`Membership::recompute_one`], the one place
//! that decides it.

use crate::codec::{Alive, Entry, Hello, NodeId, Record, Snap};
use crate::consts::{HYST_ABS, LEASE, PULSE_FRESH, RECHECK_GAP, RENEW};
use crate::event::{Event, Removal, Trace};
use crate::node::{CopyEntry, HubCopy, Membership, Recheck, ViewEntry, next_key};
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
        if self.leaving {
            return;
        }
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
            let at = self.hello_at.entry(hub).or_insert(None);
            if at.is_none() {
                *at = Some(now);
            }
            self.hsent.insert(hub, Some(now));
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
            let home = !self.is_hub && self.primary.as_ref() == Some(hub);
            if home {
                // The last frame confirms the home, before the omissions are aged: from here the home's copy is the
                // only source, and mark_view_absent gives it an entry for every view member it lacks.
                self.home_ok = Some(*hub);
                self.home_seen = true;
            }
            // Every completed snapshot ages what it omits, partial or not: a hub younger than a lease learns its
            // live members within the lease the omission clock gives them, and a delta that lists one clears it.
            self.drop_gone(hub, round);
            changed |= self.mark_absent(h, now, hub, round);
            if home {
                changed |= self.mark_view_absent(h, now, hub, round);
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

    /// A complete snapshot of `hub` listed round `round`: an earlier entry of a member the view does not list is
    /// dropped from the copy, as a snapshot that replaces the copy drops it. The omission lease below keeps a member
    /// the view lists; it must not bring back one the view let go. The copy of a hub that was not this node's home
    /// got no deltas, so its entries are stale: when that hub becomes the home, its first snapshot would otherwise
    /// mark a long-gone member omitted and list it again for a lease.
    fn drop_gone(&mut self, hub: &NodeId, round: u32) {
        let members = &self.members;
        if let Some(c) = self.hv.get_mut(hub) {
            c.entries.retain(|m, ce| ce.round == round || members.contains_key(m));
        }
    }

    /// A complete snapshot of `hub` listed round `round`: everything else in its copy is omitted, which starts that
    /// member's lease clock without removing it. A member whose removal a window deferred, and that the copy of a
    /// newly confirmed home still lists, is aged here like any other: one lease at most, where skipping would leave
    /// a listed entry that nothing ends.
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
                self.note_absent(now);
                self.trace(Trace::Absent { member: m });
                changed |= self.recompute_one(h, now, &m);
            }
        }
        changed
    }

    /// A complete snapshot of the confirmed home listed round `round`: it is the whole view, and the frames were
    /// applied under the union of the copies, so every view member is recomputed under the home alone. A member the
    /// home's copy never held gets an entry in it, carrying the view's record, that only the omission clock gives life
    /// to; `sweep_absent` ends it. With the copy full there is no room for the clock and the member is recomputed at
    /// once. A member whose removal already waits is given no entry when a window deferred it (its own instant ends
    /// it, not another lease) or when it was held and no copy lists it; a held member that some other copy still
    /// lists gets the entry, as that copy is stale until aged.
    fn mark_view_absent<H: Host>(&mut self, h: &mut H, now: Nanos, hub: &NodeId, round: u32) -> bool {
        let mut changed = false;
        let mut cur: Option<NodeId> = None;
        while let Some(m) = next_key(&self.members, cur.as_ref()) {
            cur = Some(m);
            let Some(rec) = self.members.get(&m).map(|e| e.rec) else {
                continue;
            };
            let Some(c) = self.hv.get(hub) else { break };
            let listed = c.entries.contains_key(&m);
            let full = c.entries.len() >= MAX_TABLE;
            let skip = self
                .recheck
                .get(&m)
                .is_some_and(|r| !r.held || !self.hv.values().any(|x| x.entries.contains_key(&m)));
            if listed || full || skip {
                changed |= self.recompute_one(h, now, &m);
                continue;
            }
            if let Some(c) = self.hv.get_mut(hub) {
                c.entries.insert(
                    m,
                    CopyEntry {
                        rec,
                        round: round.wrapping_sub(1),
                        absent_since: Some(now),
                    },
                );
            }
            self.note_absent(now);
            self.trace(Trace::Absent { member: m });
            changed |= self.recompute_one(h, now, &m);
        }
        changed
    }

    /// An omission clock started at `since`: the sweep is due a lease later.
    fn note_absent(&mut self, since: Nanos) {
        let due = since.saturating_add(LEASE);
        self.next_absent = Some(self.next_absent.map_or(due, |t| t.min(due)));
    }

    /// Drop copy entries whose omission has lasted a full lease, and recompute those members. Leaves `next_absent`
    /// at the earliest expiry that remains.
    pub(crate) fn sweep_absent<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let mut changed = false;
        self.next_absent = None;
        let mut hcur: Option<NodeId> = None;
        while let Some(hub) = next_key(&self.hv, hcur.as_ref()) {
            hcur = Some(hub);
            let mut cur: Option<NodeId> = None;
            loop {
                let next = self.hv.get(&hub).and_then(|c| next_key(&c.entries, cur.as_ref()));
                let Some(m) = next else { break };
                cur = Some(m);
                let since = self
                    .hv
                    .get(&hub)
                    .and_then(|c| c.entries.get(&m))
                    .and_then(|e| e.absent_since);
                let expired = since.is_some_and(|t| now.saturating_sub(t) >= LEASE);
                if let Some(t) = since.filter(|_| !expired) {
                    self.note_absent(t);
                }
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
        let Some((best, _)) = best else {
            return self.remove_from_view(h, now, m, cur, &src, expired);
        };
        let mut changed = false;
        if self.is_hub && cur.is_none_or(|c| c.rec != best) {
            self.home_delta(h, now, m, best, Alive::Alive);
        }
        match cur {
            // The view keeps its record within one epoch (a higher sequence of the same life stays); another epoch,
            // newer or older, is the best eligible copy's: a copy that no longer holds the later life takes it away.
            Some(c) if (best.inc >> 16) == (c.rec.inc >> 16) => {
                if best.inc >= c.rec.inc
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
                self.members.insert(*m, ViewEntry { rec: best });
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
            // Held until a home view is confirmed: look again then, no hub copy lists the member to bring it back.
            if self.recheck.len() < MAX_TABLE {
                self.recheck.entry(*m).or_insert(Recheck {
                    due: self.quiet_until,
                    grace: self.regrace,
                    held: true,
                });
            }
            return false;
        }
        if now < self.quiet_until && self.recheck.len() < MAX_TABLE {
            self.recheck.entry(*m).or_insert(Recheck {
                due: self.quiet_until,
                grace: self.regrace,
                held: false,
            });
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

    /// Recompute the members whose deferral is due. A member gets one more look at the end of its window (it may
    /// have woken a moment ago and its HELLO is on the way), then is recomputed without a further deferral.
    pub(crate) fn recheck_due<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let mut ready = BTreeSet::new();
        let mut regrace = false;
        for (m, e) in &mut self.recheck {
            if e.due > now {
                continue;
            }
            if e.grace {
                ready.insert(*m);
            } else {
                e.due = now.saturating_add(RECHECK_GAP);
                e.grace = true;
                regrace = true;
            }
        }
        if regrace {
            self.regrace = true;
            self.quiet_until = self.quiet_until.max(now.saturating_add(RECHECK_GAP));
        }
        if ready.is_empty() {
            return;
        }
        self.regrace = false;
        for m in &ready {
            self.recheck.remove(m);
        }
        // A removal a window already deferred is believed now, whatever window a heal has opened since.
        let open = core::mem::take(&mut self.quiet_until);
        let mut changed = false;
        for m in &ready {
            changed |= self.recompute_one(h, now, m);
        }
        self.quiet_until = open;
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
