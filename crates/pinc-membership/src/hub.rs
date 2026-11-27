//! The hub roster: leases, attachment, carrier-drop confirmation, DOWN, return and leave.
//!
//! A hub holds `roster[member] = (record, last renewal)`. Any frame from a member renews its lease; a hub also
//! refreshes a lease that is [`RENEW`] stale from the transport's `last_rx`; the lease ends [`LEASE`] after the last
//! renewal. A new attachment gets the replay floor (opaque, from the broadcast layer) and a snapshot; any other
//! HELLO gets an ACK.
//!
//! When a member's relay carrier closes and the member stays silent, the hub probes it. The hub confirms the member
//! down only when the confirm deadline has passed, nothing has been heard since the drop (no frame, no transport
//! packet), and a second probe on an independent path also went unanswered. The first probe takes the session, on
//! whatever path the transport runs it; the second never takes that path: it goes through another hub's relay, the
//! first live hub whose relay the host took it for. A probe the host refused is not a sent probe. With no second
//! probe sent the hub waits for the lease. A confirmed member is pushed as a down delta, reported to the other hubs
//! as a DOWN with proof, held (its subscriptions are kept for the lease) and remembered in `downed`.
//!
//! A hub accepts another hub's DOWN only when the proof lists two paths, the member holds no carrier to this hub,
//! and this hub's own lease is stale: not renewed, by frame or by transport evidence, within the longer of the
//! proof's probes and [`RENEW`].
//!
//! A member that leaves is dropped as left, and pushed as a left delta to every attached hub like any roster change. A
//! hub that is told by such a delta that a member it holds left drops it as left at once, as long as the member holds
//! no carrier to this hub and the delta is about the same life of the member. The leave itself is a close code of the
//! member's own session, which another hub cannot verify; the notice is as trusted as the hub that sends it, and a
//! member that was dropped wrongly attaches again with its next HELLO.
//!
//! A HELLO that announces an older incarnation than the roster holds does not regress the roster; the hub answers
//! with a delta about the node itself, and the node moves above it.
//!
//! Invariants: a lease only ends by expiry, a confirmation, an accepted DOWN, a leave or a revocation; a member that
//! returns within the lease gets its entry, its subscriptions and a delta about itself back.

use crate::codec::{Alive, Down, Hello, MAX_PROBES, NodeId, Other, Path, Probe, Proof, Record, SNAP_CHUNK, ty};
use crate::codec::{ENTRY_LEN, Frame, Snap, entry_bytes};
use crate::consts::{CONFIRM, FLOOR_MAX, LEASE, MAX_TABLE, PROBE_WAIT_MIN, RENEW, SLEEP_WIN};
use crate::event::{Refusal, Trace};
use crate::node::{Lease, Membership, Susp, next_in, next_key};
use crate::session::{Carrier, Host, Nanos, Route};

/// Why a hub drops a member from its roster.
#[derive(Clone, Copy)]
pub(crate) enum Cause {
    /// This hub confirmed it down, with proof for the other hubs.
    Confirmed(Proof),
    /// Another hub's DOWN was accepted.
    Remote,
    /// The member said goodbye.
    Left,
}

/// How long the second probe waits: the first's wait, and three round trips of the hub whose relay carries it. The
/// relay's leg to the member is assumed no slower than the member's own session: the hub has no measure of it.
fn wait_b(wait: Nanos, relay_srtt: Nanos) -> Nanos {
    wait.saturating_add(relay_srtt.saturating_mul(3))
}

fn ms(d: Nanos) -> u32 {
    u32::try_from(d / 1_000_000).unwrap_or(u32::MAX)
}

impl Membership {
    /// One roster change at this hub: tell the attached hubs (and the homed members, for the hub's own record), and
    /// fold it into this hub's own copy.
    pub(crate) fn push_delta<H: Host>(&mut self, h: &mut H, now: Nanos, m: &NodeId, rec: Record, alive: Alive) {
        let mut cur: Option<NodeId> = None;
        while let Some(p) = next_in(&self.attached, cur.as_ref()) {
            cur = Some(p);
            if p != *m && (self.is_boot(&p) || (*m == self.me && self.homed.contains(&p))) {
                self.delta_to(h, &p, m, rec, alive);
            }
        }
        let me = self.me;
        let e = crate::codec::Entry { member: m, rec, alive };
        self.apply_delta(h, now, &me, &e);
    }

    /// Send `peer` this hub's snapshot: the combined view for a member, the roster for a hub, plus this hub itself.
    fn send_snapshot<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId) {
        let partial = now.saturating_sub(self.born) < LEASE;
        let to_hub = self.is_boot(peer);
        let mut chunk = [0u8; SNAP_CHUNK * ENTRY_LEN];
        let mut n = 0usize;
        let mut cur: Option<NodeId> = None;
        let mut own_done = false;
        loop {
            let (m, rec) = if to_hub {
                match next_key(&self.roster, cur.as_ref()) {
                    Some(k) => (k, self.roster.get(&k).map(|l| l.rec)),
                    None => (self.me, None),
                }
            } else {
                match next_key(&self.members, cur.as_ref()) {
                    Some(k) => (k, self.members.get(&k).map(|e| e.rec)),
                    None => (self.me, None),
                }
            };
            let (m, rec) = match rec {
                Some(r) => {
                    cur = Some(m);
                    (m, r)
                }
                None if !own_done => {
                    own_done = true;
                    (self.me, self.own)
                }
                None => break,
            };
            if m == *peer {
                continue;
            }
            if n == SNAP_CHUNK {
                self.send_snap_chunk(h, peer, partial, true, &chunk, n);
                n = 0;
            }
            if let Some(dst) = chunk.get_mut(n * ENTRY_LEN..(n + 1) * ENTRY_LEN) {
                dst.copy_from_slice(&entry_bytes(&m, &rec, Alive::Alive));
            }
            n += 1;
        }
        self.send_snap_chunk(h, peer, partial, false, &chunk, n);
    }

    /// A hub sends `peer` its snapshot again without a new attachment: the host adopted another session of an
    /// attached member, and what went out on the closed session may be lost.
    pub fn snapshot_to<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId) {
        if self.is_hub && self.attached.contains(peer) {
            self.send_snapshot(h, now, peer);
        }
    }

    fn send_snap_chunk<H: Host>(
        &mut self,
        h: &mut H,
        peer: &NodeId,
        partial: bool,
        more: bool,
        chunk: &[u8],
        n: usize,
    ) {
        let Some(entries) = chunk.get(..n * ENTRY_LEN) else {
            return;
        };
        let Ok(snap) = Snap::new(partial, more, entries) else {
            return;
        };
        let mut buf = [0u8; 4 + 3 + SNAP_CHUNK * ENTRY_LEN];
        self.tx_buf(h, peer, Route::Reply, &Frame::Snap(snap), &mut buf);
    }

    /// `FLOOR_PUSH`: a hub that has just accepted a session of a member sends its replay floor at once, with its first
    /// flight, instead of waiting for the member's HELLO, so a restarted member's floor gathering completes a round
    /// trip earlier per hub. The HELLO that follows sends it again for a new attachment; the member keeps the later.
    pub fn push_floor<H: Host>(&mut self, h: &mut H, peer: &NodeId) {
        if self.is_hub && !self.is_boot(peer) {
            self.send_floor(h, peer);
        }
    }

    fn send_floor<H: Host>(&mut self, h: &mut H, peer: &NodeId) {
        let mut body = [0u8; FLOOR_MAX];
        let n = h.floor(peer, &mut body).min(FLOOR_MAX);
        let Some(rest) = body.get(..n).filter(|r| !r.is_empty()) else {
            return;
        };
        let mut buf = [0u8; FLOOR_MAX + 8];
        let f = Frame::Other(Other {
            ty: ty::FLOOR,
            topic: &[],
            rest,
        });
        self.tx_buf(h, peer, Route::Reply, &f, &mut buf);
    }

    /// A HELLO from `peer`.
    pub(crate) fn on_hello<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId, hello: &Hello) {
        if hello.homed && !self.is_boot(peer) {
            if self.homed.len() < MAX_TABLE {
                self.homed.insert(*peer);
            }
        } else {
            self.homed.remove(peer);
        }
        if self.downed.remove(peer).is_some() {
            h.restore(peer);
        }
        let new_attach = !self.attached.contains(peer);
        if new_attach && self.attached.len() < MAX_TABLE {
            self.attached.insert(*peer);
        }
        if new_attach {
            self.trace(Trace::Attached { member: *peer });
            self.send_floor(h, peer);
        }
        if hello.snap || new_attach {
            self.send_snapshot(h, now, peer);
        } else {
            self.tx(h, peer, Route::Reply, &Frame::Ack);
        }
        if let Some(held) = self.roster.get(peer).copied()
            && hello.rec.inc < held.rec.inc
        {
            // The node announces an older incarnation than the one we hold (a clock that went back, a lost store).
            // Keep ours so the roster never regresses, and tell the node, which moves above it.
            if let Some(l) = self.roster.get_mut(peer) {
                l.renewed = now;
            }
            self.delta_to(h, peer, peer, held.rec, Alive::Alive);
            return;
        }
        if let Some(seen) = self.members.get(peer).map(|e| e.rec)
            && hello.rec.inc >> 16 < seen.inc >> 16
        {
            // The view holds a later life of the node than it announces and no roster here does (its clock went back
            // while the hub that held its last life went away): tell it, as above, and wait for its HELLO from above.
            if let Some(l) = self.roster.get_mut(peer) {
                l.renewed = now;
            }
            self.delta_to(h, peer, peer, seen, Alive::Alive);
            return;
        }
        let unchanged = self.roster.get(peer).is_some_and(|l| l.rec == hello.rec);
        if unchanged {
            if let Some(l) = self.roster.get_mut(peer) {
                l.renewed = now;
            }
            return;
        }
        if !self.roster.contains_key(peer) && self.roster.len() >= MAX_TABLE {
            return;
        }
        self.roster.insert(
            *peer,
            Lease {
                rec: hello.rec,
                renewed: now,
            },
        );
        self.push_delta(h, now, peer, hello.rec, Alive::Alive);
    }

    /// Drop `m`'s lease now.
    pub(crate) fn hub_down<H: Host>(&mut self, h: &mut H, now: Nanos, member: &NodeId, cause: Cause) {
        let Some(lease) = self.roster.remove(member) else {
            return;
        };
        self.susp.remove(member);
        self.attached.remove(member);
        let left = matches!(cause, Cause::Left);
        if left {
            h.release(member);
        } else {
            h.hold(member);
        }
        self.push_delta(h, now, member, lease.rec, if left { Alive::Left } else { Alive::Down });
        if !left && (self.downed.len() < MAX_TABLE || self.downed.contains_key(member)) {
            self.downed.insert(*member, (lease, now));
        }
        if let Cause::Confirmed(proof) = cause {
            let mut paths = proof.probes().iter().map(|p| p.path);
            self.trace(Trace::Confirmed {
                member: *member,
                first: paths.next().unwrap_or(Path::Session),
                second: paths.next(),
            });
            for idx in 0..self.boot.len() {
                let Some(hub) = self.boot.get(idx).copied() else {
                    continue;
                };
                if hub != self.me {
                    let f = Frame::Down(Down {
                        member,
                        inc: lease.rec.inc,
                        proof,
                    });
                    if self.tx(h, &hub, Route::Reply, &f) {
                        self.trace(Trace::DownSent { member: *member });
                    }
                }
            }
        }
    }

    /// Another hub's DOWN. Accepted only on a stale lease of our own.
    pub(crate) fn on_down<H: Host>(&mut self, h: &mut H, now: Nanos, d: &Down<'_>) {
        let m = *d.member;
        let refuse = |s: &mut Self, why| s.trace(Trace::DownRefused { member: m, why });
        if self.is_boot(&m) {
            return refuse(self, Refusal::NotApplicable);
        }
        let Some(l) = self.roster.get(&m).copied() else {
            return refuse(self, Refusal::Unknown);
        };
        if l.rec.inc >> 16 != d.inc >> 16 {
            return refuse(self, Refusal::Unknown);
        }
        let oldest = d.proof.probes().iter().map(|p| p.age_ms).max().unwrap_or(0);
        if !d.proof.independent() {
            return refuse(self, Refusal::NotIndependent);
        }
        if d.proof.silence_ms < oldest {
            return refuse(self, Refusal::BadProof);
        }
        if h.carrier(&m) == Carrier::Open {
            return refuse(self, Refusal::CarrierOpen);
        }
        let renewed = h.evidence(&m).map_or(l.renewed, |e| l.renewed.max(e.last_rx));
        if let Some(x) = self.roster.get_mut(&m) {
            x.renewed = renewed;
        }
        let window = (u64::from(oldest) * 1_000_000).max(RENEW);
        if now.saturating_sub(renewed) <= window {
            return refuse(self, Refusal::LeaseFresh);
        }
        self.trace(Trace::DownAccepted { member: m });
        self.hub_down(h, now, &m, Cause::Remote);
    }

    /// Another hub's delta says `e.member` left. A member held for the same life that has no carrier to this hub is
    /// dropped as left at once, as the member's own close would have dropped it.
    pub(crate) fn on_left<H: Host>(&mut self, h: &mut H, now: Nanos, e: &crate::codec::Entry<'_>) {
        let m = *e.member;
        if self.is_boot(&m) || h.carrier(&m) == Carrier::Open {
            return;
        }
        if self.roster.get(&m).is_none_or(|l| l.rec.inc >> 16 != e.rec.inc >> 16) {
            return;
        }
        self.trace(Trace::LeaveSeen { member: m });
        self.hub_down(h, now, &m, Cause::Left);
    }

    /// The once-a-tick hub work: expire leases, refresh them from transport evidence, watch dropped carriers,
    /// restore returned carriers.
    pub(crate) fn hub_tick<H: Host>(&mut self, h: &mut H, now: Nanos) {
        let mut cur: Option<NodeId> = None;
        while let Some(m) = next_key(&self.roster, cur.as_ref()) {
            cur = Some(m);
            let Some(mut l) = self.roster.get(&m).copied() else {
                continue;
            };
            if now.saturating_sub(l.renewed) > RENEW
                && let Some(ev) = h.evidence(&m)
                && ev.last_rx > l.renewed
            {
                l.renewed = ev.last_rx;
                if let Some(x) = self.roster.get_mut(&m) {
                    x.renewed = l.renewed;
                }
                self.trace(Trace::Pulse { member: m });
            }
            if now.saturating_sub(l.renewed) > LEASE {
                self.roster.remove(&m);
                self.susp.remove(&m);
                self.trace(Trace::LeaseExpired { member: m });
                self.push_delta(h, now, &m, l.rec, Alive::Down);
                h.release(&m);
            } else if !self.is_boot(&m) {
                self.carrier_watch(h, now, &m);
            }
        }
        let mut cur: Option<NodeId> = None;
        while let Some(m) = next_key(&self.downed, cur.as_ref()) {
            cur = Some(m);
            let Some((_, t0)) = self.downed.get(&m).copied() else {
                continue;
            };
            if now.saturating_sub(t0) > LEASE || self.roster.contains_key(&m) || self.revoked.contains(&m) {
                self.downed.remove(&m);
                h.release(&m);
            } else if h.carrier(&m) == Carrier::Open {
                self.carrier_return(h, now, &m);
            }
        }
    }

    /// `member`'s carrier is open again. If the hub confirmed it down within the lease, restore its entry and its
    /// subscriptions, tell the other hubs, and tell the member about itself.
    pub fn carrier_return<H: Host>(&mut self, h: &mut H, now: Nanos, member: &NodeId) {
        let Some((mut l, _)) = self.downed.remove(member) else {
            self.trace(Trace::CarrierReturned {
                member: *member,
                restored: false,
            });
            return;
        };
        if self.roster.contains_key(member) || self.revoked.contains(member) {
            return;
        }
        if self.roster.len() >= MAX_TABLE {
            // The roster filled up while the member was held: a full table refuses, it never grows past its bound.
            h.release(member);
            self.trace(Trace::CarrierReturned {
                member: *member,
                restored: false,
            });
            return;
        }
        l.renewed = now;
        self.roster.insert(*member, l);
        if self.up.contains_key(member) && self.attached.len() < MAX_TABLE {
            self.attached.insert(*member);
        }
        h.restore(member);
        self.push_delta(h, now, member, l.rec, Alive::Alive);
        self.delta_to(h, member, member, l.rec, Alive::Alive);
        self.trace(Trace::CarrierReturned {
            member: *member,
            restored: true,
        });
    }

    /// `member`'s relay carrier to this hub closed at `since`. Start confirming it now rather than at the next tick.
    pub fn carrier_gone<H: Host>(&mut self, h: &mut H, now: Nanos, member: &NodeId) {
        if self.is_hub && !self.is_boot(member) {
            self.trace(Trace::CarrierGone { member: *member });
            self.carrier_watch(h, now, member);
        }
    }

    /// Send the second probe of a suspicion through the relay of the first live hub (not this one, not the member)
    /// whose relay the host took it for. Returns the path it took and the smoothed round trip to that hub (0 when the
    /// host has none), or `None` when no probe left.
    fn probe_second<H: Host>(&mut self, h: &mut H, now: Nanos, m: &NodeId) -> Option<(Path, Nanos)> {
        for i in 0..self.boot.len() {
            let Some(x) = self.boot.get(i).copied() else {
                continue;
            };
            if x != self.me && x != *m && self.hub_up(now, &x) && self.tx(h, m, Route::Via(x), &Frame::Probe) {
                self.trace(Trace::ProbeSent {
                    member: *m,
                    path: Path::Relay,
                });
                return Some((Path::Relay, h.evidence(&x).map_or(0, |e| e.srtt)));
            }
        }
        None
    }

    fn schedule_confirm(&mut self, now: Nanos, at: Nanos) {
        let at = at.max(now + 1);
        self.next_conf = Some(self.next_conf.map_or(at, |c| c.min(at)));
    }

    /// Confirm or clear a dropped carrier. See the module docs for the rule. The second probe waits three round
    /// trips of the hub whose relay carries it on top of the first probe's wait; the relay's leg to the member is
    /// assumed no slower than the member's own session, as the hub has no measure of it.
    pub(crate) fn carrier_watch<H: Host>(&mut self, h: &mut H, now: Nanos, m: &NodeId) {
        let Some(l) = self.roster.get(m).copied() else {
            self.susp.remove(m);
            return;
        };
        let Carrier::Gone { since, sleep } = h.carrier(m) else {
            self.susp.remove(m);
            return;
        };
        let ev = h.evidence(m);
        let heard = ev.is_some_and(|e| e.last_rx >= since);
        if l.renewed >= since || heard || sleep.is_some_and(|s| s.saturating_add(SLEEP_WIN) >= since) {
            if heard && let (Some(e), Some(x)) = (ev, self.roster.get_mut(m)) {
                x.renewed = x.renewed.max(e.last_rx);
            }
            self.susp.remove(m);
            return;
        }
        match self.susp.get(m).copied() {
            Some(mut sp) if sp.since == since => {
                // The watch runs again when the first probe's wait ends: an independent route may be up by then. A
                // suspicion is not reported: only the confirmation is an event.
                let at = sp.probe_a.saturating_add(sp.wait);
                if now < at {
                    self.schedule_confirm(now, at);
                }
                if sp.probe_b.is_none()
                    && let Some((path, srtt)) = self.probe_second(h, now, m)
                {
                    sp.probe_b = Some((now, path, srtt));
                    self.susp.insert(*m, sp);
                }
                if let Some((tb, _, srtt)) = sp.probe_b {
                    let dl = (sp.since + CONFIRM)
                        .max(sp.probe_a + sp.wait)
                        .max(tb + wait_b(sp.wait, srtt));
                    if now >= dl {
                        self.confirm(h, now, m, sp, l);
                    } else {
                        self.schedule_confirm(now, dl);
                    }
                }
            }
            _ => {
                if self.susp.len() >= MAX_TABLE {
                    return;
                }
                let wait = PROBE_WAIT_MIN.max(ev.map_or(0, |e| e.srtt.saturating_mul(3)));
                self.tx(h, m, Route::Reply, &Frame::Probe);
                self.trace(Trace::ProbeSent {
                    member: *m,
                    path: Path::Session,
                });
                let probe_b = self.probe_second(h, now, m).map(|(path, srtt)| (now, path, srtt));
                let sp = Susp {
                    since,
                    probe_a: now,
                    probe_b,
                    wait,
                };
                self.susp.insert(*m, sp);
                self.schedule_confirm(now, now.saturating_add(wait));
                if let Some((tb, _, srtt)) = probe_b {
                    let dl = (since + CONFIRM).max(now + wait).max(tb + wait_b(wait, srtt));
                    self.schedule_confirm(now, dl);
                } else {
                    self.trace(Trace::NoIndependentPath { member: *m });
                }
            }
        }
    }

    fn confirm<H: Host>(&mut self, h: &mut H, now: Nanos, m: &NodeId, sp: Susp, l: Lease) {
        let mut probes = [Probe {
            age_ms: 0,
            path: Path::Session,
        }; MAX_PROBES];
        let mut n = 0;
        if let Some(p) = probes.first_mut() {
            *p = Probe {
                age_ms: ms(now.saturating_sub(sp.probe_a)),
                path: Path::Session,
            };
        }
        n += 1;
        if let Some((tb, path, _)) = sp.probe_b
            && let Some(p) = probes.get_mut(n)
        {
            *p = Probe {
                age_ms: ms(now.saturating_sub(tb)),
                path,
            };
            n += 1;
        }
        let Some(proof) = Proof::new(ms(now.saturating_sub(l.renewed)), probes.get(..n).unwrap_or_default()) else {
            return;
        };
        self.hub_down(h, now, m, Cause::Confirmed(proof));
    }
}
