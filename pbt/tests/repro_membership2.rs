//! Reproductions of membership bugs found by the network properties in `membership_world.rs` and
//! `membership_timers.rs`, each a plain test that fails on the unmodified code.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

use std::collections::{BTreeMap, BTreeSet};

use pinc_membership::consts::{AWARENESS_BOUND, LEASE};
use pinc_membership::session::StoreError;
use pinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Event, Evidence, Local, Membership, NodeId, Route, Session,
};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000 * MS;
const T0: u64 = 1_000 * SEC;

fn id(i: usize) -> NodeId {
    [u8::try_from(i + 1).unwrap(); 32]
}

#[derive(Default)]
struct Host {
    sessions: BTreeSet<NodeId>,
    ev: BTreeMap<NodeId, Evidence>,
    out: Vec<(NodeId, Vec<u8>)>,
    persistent: bool,
    sealed: Option<u64>,
}

impl Session for Host {
    fn send(&mut self, peer: &NodeId, _route: Route, frame: &[u8]) -> bool {
        if !self.sessions.contains(peer) {
            return false;
        }
        self.out.push((*peer, frame.to_vec()));
        true
    }
    fn evidence(&self, peer: &NodeId) -> Option<Evidence> {
        self.ev.get(peer).copied()
    }
    fn carrier(&self, _member: &NodeId) -> Carrier {
        Carrier::Unknown
    }
    fn close(&mut self, _peer: &NodeId, _reason: CloseReason) {}
}

impl Broadcast for Host {
    fn floor(&mut self, _member: &NodeId, _out: &mut [u8]) -> usize {
        0
    }
    fn frame(&mut self, _from: &NodeId, _ty: u8, _topic: &[u8], _rest: &[u8]) {}
    fn hold(&mut self, _member: &NodeId) {}
    fn restore(&mut self, _member: &NodeId) {}
    fn release(&mut self, _member: &NodeId) {}
    fn resubscribe(&mut self, _hub: &NodeId) {}
    fn primary_changed(&mut self, _old: Option<&NodeId>, _new: &NodeId) {}
}

impl Local for Host {
    fn version(&self) -> u16 {
        7
    }
    fn reflexive_known(&self) -> bool {
        true
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [moves, 0, 0, 0, 0, 0, 0, 7]
    }
    fn persistent(&self) -> bool {
        self.persistent
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        Ok(self.sealed)
    }
    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        self.sealed = Some(epoch);
        Ok(())
    }
}

/// A tiny network with zero latency: node 0 is the one hub, the others members. Frames cross at once; the
/// transport hears every session at every step, as its keepalives would.
struct Net {
    m: Vec<Membership>,
    h: Vec<Host>,
    alive: Vec<bool>,
    now: u64,
}

impl Net {
    fn start(i: usize, h: &mut Host, now: u64) -> Membership {
        let hubs = [id(0)];
        let cfg = Config { me: id(i), is_hub: i == 0, hubs: &hubs, trace: true };
        Membership::start(&cfg, h, now, 1_700_000_000_000 + now / MS, 0).unwrap()
    }

    fn new(nodes: usize) -> Self {
        let mut h: Vec<Host> = (0..nodes).map(|i| Host { persistent: i == 0, ..Host::default() }).collect();
        let m = (0..nodes).map(|i| Self::start(i, &mut h[i], T0)).collect();
        Self { m, h, alive: vec![true; nodes], now: T0 }
    }

    /// A session between member `a` (the dialer) and the hub.
    fn connect(&mut self, a: usize) {
        for (x, y, incoming) in [(0, a, true), (a, 0, false)] {
            self.h[x].sessions.insert(id(y));
            self.h[x].ev.insert(id(y), Evidence { last_rx: self.now, srtt: 2 * MS, pto: 0, inflight: 0, direct: true });
            let (m, h) = (&mut self.m[x], &mut self.h[x]);
            m.session_up(h, self.now, &id(y), incoming);
        }
        self.pump();
    }

    fn pump(&mut self) {
        for _ in 0..64 {
            let mut moved = false;
            for i in 0..self.m.len() {
                for (peer, bytes) in std::mem::take(&mut self.h[i].out) {
                    let j = usize::from(peer[0]) - 1;
                    if self.alive[j] && self.h[j].sessions.contains(&id(i)) {
                        let (m, h) = (&mut self.m[j], &mut self.h[j]);
                        assert_eq!(m.on_bytes(h, self.now, &id(i), &bytes), Ok(bytes.len()));
                        moved = true;
                    }
                }
            }
            if !moved {
                return;
            }
        }
    }

    fn run(&mut self, dur: u64) {
        let end = self.now + dur;
        while self.now < end {
            self.now += 100 * MS;
            for i in 0..self.m.len() {
                if !self.alive[i] {
                    continue;
                }
                let now = self.now;
                let live: Vec<NodeId> =
                    self.h[i].sessions.iter().copied().filter(|p| self.alive[usize::from(p[0]) - 1]).collect();
                for p in live {
                    if let Some(e) = self.h[i].ev.get_mut(&p) {
                        e.last_rx = now;
                    }
                }
                if self.m[i].poll_timeout() <= now {
                    let (m, h) = (&mut self.m[i], &mut self.h[i]);
                    m.on_timeout(h, now);
                }
            }
            self.pump();
        }
    }
}

/// properties.md, membership, completeness: "a failed member leaves every live view within the awareness bound"
/// (`consts::AWARENESS_BOUND`, 145 s: "The longest a change of the group (a join, a leave or a crash) takes to reach
/// every live member").
///
/// Actual: one hub H and members X and B, the hub a lease old so its snapshots are complete. H restarts (a new
/// process, the same store) at the moment X crashes. B's session to the old H dies; B dials the new H, which is
/// younger than a lease and so sends a partial snapshot without X. X stays in B's view for good: 400 s after the
/// crash it is still listed, while the hub's own view does not list it. Found by `views_converge_after_the_heal`
/// (shrunk input `[Restart(0), Crash(1)]`, one hub, two members, EPHYRA_REPLAY=9079131089087898006:12).
///
/// Suspected fault: a partial snapshot neither drops the copy's old entries (`drop_gone`) nor starts their omission
/// clock (`mark_absent`, `mark_view_absent`), view.rs:356-362, and nothing asks the hub for another snapshot once it
/// is a lease old: a member asks for one only when it dials, changes primary or wakes late (`renew`, view.rs:98,
/// `snap = force_snap || !self.hv.contains_key(&hub)`). The new hub never held X, so no lease of it ends and no delta
/// or DOWN about it is ever sent: the stale entry of the old hub life is the only source, and it never ages. With
/// more hubs the same holds for a member whose home is the restarted hub, and for a hub whose copy of a restarted
/// hub is stale, which then serves the ghost to its own members. Who can trigger it: no one in particular; a hub
/// restart (the relay binary restarted with the same identity) that coincides with, or follows, a member crash
/// before the old hub life's lease on it ended.
#[test]
fn a_member_that_crashed_while_its_only_hub_restarted_stays_in_views_for_good() {
    // The second shape of the fault, `a_leave_missed_while_the_hub_is_young_is_never_learned`, needs no restart.
    let (hub, x, b) = (0, 1, 2);
    let mut n = Net::new(3);
    n.run(LEASE + 5 * SEC);
    // The members start now, against a hub a lease old.
    for i in [x, b] {
        n.m[i] = Net::start(i, &mut n.h[i], n.now);
        n.connect(i);
    }
    n.run(10 * SEC);
    assert!(n.m[b].in_view(&id(x)), "B lists X");
    // The hub restarts at the moment X crashes: every session of both is gone, unseen by B.
    n.alive[x] = false;
    n.h[hub] = Host { persistent: true, sealed: n.h[hub].sealed, ..Host::default() };
    n.m[hub] = Net::start(hub, &mut n.h[hub], n.now);
    let crash = n.now;
    // B's transport gives the dead session up after a minute and dials the new hub.
    n.h[b].ev.get_mut(&id(hub)).unwrap().last_rx = crash;
    n.alive[hub] = false;
    n.run(60 * SEC);
    n.alive[hub] = true;
    n.h[b].sessions.remove(&id(hub));
    let (m, h) = (&mut n.m[b], &mut n.h[b]);
    m.session_down(h, n.now, &id(hub), 0);
    n.connect(b);
    n.run(AWARENESS_BOUND + 200 * SEC);
    let events: Vec<Event> = std::iter::from_fn(|| n.m[b].poll_event()).collect();
    assert!(!n.m[hub].in_view(&id(x)), "the hub does not list X");
    assert!(
        !n.m[b].in_view(&id(x)),
        "X crashed {} s ago and B still lists it; B's events: {events:?}",
        (n.now - crash) / SEC
    );
}

/// The same fault with no restart, on a network younger than a lease. properties.md, membership: "leave reported as
/// a leave"; completeness: "a failed member leaves every live view within the awareness bound" (a leave is one of the
/// changes `AWARENESS_BOUND` covers).
///
/// Actual: one hub, 10 s old, and members X and B. B's session to the hub closes; X leaves (its close carries the
/// leave code, the hub drops it as left and pushes the left delta to its homed members, but B is not attached); B
/// dials again a moment later and gets the hub's snapshot, partial because the hub is younger than a lease. X stays in
/// B's view for good, with no event, while the hub no longer lists it. Found by `views_converge_after_the_heal`
/// (shrunk input `[Close(1, 0), Leave(47)]`, one hub, two members, EPHYRA_REPLAY=5655694454216781121:226).
///
/// Suspected fault: as above, view.rs:356-362 (a partial snapshot ages nothing) with no later complete snapshot
/// (view.rs:98). Who can trigger it: no one in particular: any member that misses a delta while its home hub is
/// younger than a lease (the first 80 s of a network, or of a hub's life) keeps the stale entry.
#[test]
fn a_leave_missed_while_the_hub_is_young_is_never_learned() {
    let (hub, x, b) = (0, 1, 2);
    let mut n = Net::new(3);
    n.connect(x);
    n.connect(b);
    n.run(10 * SEC);
    assert!(n.m[b].in_view(&id(x)), "B lists X");
    // B's session to the hub closes (a rebind, a handover); both ends see it.
    for (i, p) in [(b, hub), (hub, b)] {
        n.h[i].sessions.remove(&id(p));
        let (m, h) = (&mut n.m[i], &mut n.h[i]);
        m.session_down(h, n.now, &id(p), 0);
    }
    // X leaves: its session closes with the leave code.
    let (m, h) = (&mut n.m[x], &mut n.h[x]);
    m.leave(h);
    n.alive[x] = false;
    n.h[hub].sessions.remove(&id(x));
    let (m, h) = (&mut n.m[hub], &mut n.h[hub]);
    m.session_down(h, n.now, &id(x), pinc_membership::session::LEAVE_CODE);
    let left = n.now;
    assert!(!n.m[hub].in_view(&id(x)), "the hub dropped X as left");
    n.run(2 * SEC);
    n.connect(b);
    n.run(AWARENESS_BOUND + 200 * SEC);
    let events: Vec<Event> = std::iter::from_fn(|| n.m[b].poll_event()).collect();
    assert!(
        !n.m[b].in_view(&id(x)),
        "X left {} s ago and B still lists it; B's events: {events:?}",
        (n.now - left) / SEC
    );
}
