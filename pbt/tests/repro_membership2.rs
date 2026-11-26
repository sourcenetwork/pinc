//! Reproductions of membership bugs found by the network properties in `membership_world.rs` and
//! `membership_timers.rs`, each a plain test that fails on the unmodified code.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

use std::collections::{BTreeMap, BTreeSet};

use pinc_membership::codec::{Alive, Snap, entry_bytes};
use pinc_membership::consts::{AWARENESS_BOUND, LEASE};
use pinc_membership::session::StoreError;
use pinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Event, Evidence, Frame, Local, Membership, NodeId, Record, Route, Session,
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

/// A tiny network with zero latency: nodes below `nh` are hubs (with a persistent store), the others members.
/// Frames cross at once; the transport hears every session at every step, as its keepalives would.
struct Net {
    m: Vec<Membership>,
    h: Vec<Host>,
    alive: Vec<bool>,
    nh: usize,
    now: u64,
}

impl Net {
    /// Start node `i` with its wall clock `back_ms` behind the true time.
    fn start_with(i: usize, nh: usize, h: &mut Host, now: u64, back_ms: u64) -> Membership {
        let hubs: Vec<NodeId> = (0..nh).map(id).collect();
        let cfg = Config { me: id(i), is_hub: i < nh, hubs: &hubs, trace: true };
        Membership::start(&cfg, h, now, 1_700_000_000_000 + now / MS - back_ms, 0).unwrap()
    }

    fn start(i: usize, h: &mut Host, now: u64) -> Membership {
        Self::start_with(i, 1, h, now, 0)
    }

    fn with_hubs(nodes: usize, nh: usize) -> Self {
        let mut h: Vec<Host> = (0..nodes).map(|i| Host { persistent: i < nh, ..Host::default() }).collect();
        let m = (0..nodes).map(|i| Self::start_with(i, nh, &mut h[i], T0, 0)).collect();
        Self { m, h, alive: vec![true; nodes], nh, now: T0 }
    }

    fn new(nodes: usize) -> Self {
        Self::with_hubs(nodes, 1)
    }

    /// A session between member `a` (the dialer) and hub 0.
    fn connect(&mut self, a: usize) {
        self.connect_to(a, 0);
    }

    /// A session between `a` (the dialer) and hub `hub`.
    fn connect_to(&mut self, a: usize, hub: usize) {
        for (x, y, incoming) in [(hub, a, true), (a, hub, false)] {
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
        assert_eq!(n.nh, 1);
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

/// Hubs H0 and H1, member X homed at H0 and member W homed at H1. X restarts with its wall clock `back_ms` behind
/// (its new incarnation is then below the last life's) at the moment H0 crashes, and X attaches to H1. Returns
/// whether, 300 s later, H1's and W's records of X carry X's incarnation, and whether W then hears of an address
/// change of X.
fn clock_back_while_the_home_dies(back_ms: u64) -> (bool, bool, String) {
    let (h0, h1, x, w) = (0, 1, 2, 3);
    let mut n = Net::with_hubs(4, 2);
    n.connect_to(h1, h0);
    n.connect_to(x, h0);
    n.connect_to(w, h1);
    n.run(10 * SEC);
    assert!(n.m[w].in_view(&id(x)), "W lists X");
    // X restarts (a new process: its sessions are gone) with its clock behind; H0 crashes at the same time.
    n.alive[h0] = false;
    n.h[x] = Host::default();
    n.m[x] = Net::start_with(x, 2, &mut n.h[x], n.now, back_ms);
    n.h[h1].sessions.remove(&id(h0));
    let (m, h) = (&mut n.m[h1], &mut n.h[h1]);
    m.session_down(h, n.now, &id(h0), 0);
    n.connect_to(x, h1);
    n.run(300 * SEC);
    let inc = n.m[x].incarnation();
    let rec_of = |m: &Membership| m.members().find(|(k, _)| **k == id(x)).map(|(_, r)| r.inc);
    let (at_h1, at_w) = (rec_of(&n.m[h1]), rec_of(&n.m[w]));
    let records_ok = at_h1 == Some(inc) && at_w == Some(inc);
    let _ = std::iter::from_fn(|| n.m[w].poll_event()).count();
    n.m[x].address_changed(n.now);
    n.run(30 * SEC);
    let heard = std::iter::from_fn(|| n.m[w].poll_event()).any(|e| e == Event::AddressChanged { member: id(x) });
    (records_ok, heard, format!("X runs at {inc:#x}; H1 holds {at_h1:x?}, W holds {at_w:x?}"))
}

/// properties.md, membership: incarnations "only go up through records and observed words", and convergence: "views
/// merge to the union of fresh hubs with the highest incarnation". hub.rs:195-196, for a node that announces an older
/// incarnation than the hub holds: "(a clock that went back, a lost store). Keep ours so the roster never regresses,
/// and tell the node, which moves above it"; view.rs:214: "Reincarnated behind our back (a clock that went back, a
/// lost store): move above it."
///
/// Actual: hubs H0 and H1, member X homed at H0, member W homed at H1. X restarts with its wall clock 10 s behind,
/// so its new incarnation is below its last life's, and H0 crashes at the same moment (one power cut at a site that
/// holds both); X attaches to H1. H1's view, and W's, keep X's last-life record for good (300 s later, after H0's copy
/// was dropped as stale), and X is never told, so it never moves above it. The visible effect: X's later records are
/// all ignored by those views, so W never hears `Event::AddressChanged` when X's address changes (nor
/// `StackChanged` on a version change), and a DOWN or delta for X's real incarnation does not match the record they
/// hold. The control run with no clock jump gets both right. Found by `views_converge_after_the_heal` (shrunk input
/// `[Restart(122, 10001), Crash(0)]`, two hubs, two members, EPHYRA_REPLAY=13:487).
///
/// Suspected fault: `recompute_one` (view.rs:505) keeps the view's record whenever the best fresh copy's epoch is not
/// above it, so a record that only a dropped copy held stays; and the hub tells a node to move above an older
/// incarnation only when its own roster holds the newer one (hub.rs:192-201, `self.roster.get(peer)`), never when
/// only its view does. Who can trigger it: no one in particular; a member whose clock went back across a restart (or
/// whose store was lost) while the only hub that held its last life went away.
#[test]
fn a_member_whose_clock_went_back_is_never_told_when_its_home_hub_died() {
    let (ok, heard, state) = clock_back_while_the_home_dies(0);
    assert!(ok && heard, "control run with no clock jump: records ok {ok}, address change heard {heard}; {state}");
    let (ok, heard, state) = clock_back_while_the_home_dies(10_001);
    assert!(ok, "after a clock jump back, the views keep X's last-life record: {state}; address change heard: {heard}");
    assert!(heard, "W never heard of X's address change; {state}");
}

/// A complete snapshot from `hub` listing `members`, all alive.
fn hub_snap(m: &mut Membership, h: &mut Host, now: u64, hub: NodeId, members: &[NodeId]) {
    let rec = Record { inc: 5 << 16, ver: 7, thash: [1; 8] };
    let entries: Vec<u8> = members.iter().flat_map(|x| entry_bytes(x, &rec, Alive::Alive)).collect();
    let mut out = vec![0u8; 4096];
    let f = Frame::Snap(Snap::new(false, false, &entries).unwrap());
    let b = f.encode(&mut out).unwrap().to_vec();
    assert_eq!(m.on_bytes(h, now, &hub, &b), Ok(b.len()));
}

/// One delta from `hub` about `x`.
fn hub_delta(m: &mut Membership, h: &mut Host, now: u64, hub: NodeId, x: &NodeId, alive: Alive) {
    let rec = Record { inc: 5 << 16, ver: 7, thash: [1; 8] };
    let mut out = vec![0u8; 256];
    let b = Frame::Delta(pinc_membership::codec::Entry { member: x, rec, alive }).encode(&mut out).unwrap().to_vec();
    assert_eq!(m.on_bytes(h, now, &hub, &b), Ok(b.len()));
}

/// A member with hub A starts at T0 and reads A's complete snapshot listing X. The host serves the first tick on
/// time when `first_tick_on_time`; then the node is suspended for 30 s (more than WAKE_GAP, less than the 60 s after
/// which a hub's silence counts as a partition). While it slept A sent two deltas: X down, then X alive again (X came
/// back at the same incarnation). At the wake the late tick runs first, then the two deltas are read. Returns
/// whether the application was told X is down, and whether X is in the view 30 s after the wake.
fn suspended_right_after_start(first_tick_on_time: bool) -> (bool, bool) {
    let (a, x) = (id(1), id(2));
    let hubs = [a];
    let cfg = Config { me: id(0), is_hub: false, hubs: &hubs, trace: true };
    let mut h = Host::default();
    let mut m = Membership::start(&cfg, &mut h, T0, 0, 0).unwrap();
    h.sessions.insert(a);
    m.session_up(&mut h, T0, &a, false);
    h.ev.insert(a, Evidence { last_rx: T0, srtt: 20 * MS, pto: 0, inflight: 0, direct: true });
    hub_snap(&mut m, &mut h, T0, a, &[x]);
    assert!(m.in_view(&x), "A's snapshot adds X");
    if first_tick_on_time {
        m.on_timeout(&mut h, T0);
    }
    let wake = T0 + 30 * SEC;
    h.ev.insert(a, Evidence { last_rx: wake, srtt: 20 * MS, pto: 0, inflight: 0, direct: true });
    m.on_timeout(&mut h, wake);
    hub_delta(&mut m, &mut h, wake + MS, a, &x, Alive::Down);
    hub_delta(&mut m, &mut h, wake + MS, a, &x, Alive::Alive);
    let mut now = wake + MS;
    for _ in 0..1_000 {
        now = m.poll_timeout().max(now + MS);
        if now > wake + 30 * SEC {
            break;
        }
        h.ev.insert(a, Evidence { last_rx: now, srtt: 20 * MS, pto: 0, inflight: 0, direct: true });
        m.on_timeout(&mut h, now);
    }
    let down = std::iter::from_fn(|| m.poll_event()).any(|e| e == Event::MemberConfirmedDown { member: x });
    (down, m.in_view(&x))
}

/// timers.rs, module invariant: "a tick that arrives later than WAKE_GAP after it was due is a suspension: the node
/// renews every hub at once with a snapshot request and opens a quiet window, so removals queued while it slept are
/// re-checked, not believed". The first tick is due at the start (`poll_timeout` returns `self.born` before any tick).
///
/// Actual: the same member, the same frames and the same 30 s suspension. When the host served the first tick on time,
/// the late tick opens a quiet window, the DOWN that A sent while the node slept is deferred, A's next delta lists X
/// again, and the application hears nothing. When the suspension came before the first tick, the late first tick
/// opens no window, X is removed at once and the application gets `Event::MemberConfirmedDown` for X, which is alive
/// and listed again a moment later. Found by `a_late_tick_opens_a_quiet_window` in `membership_timers.rs` (shrunk
/// input `(0, 2001)`: no tick before, a first tick 2001 ms late).
///
/// Suspected fault: `on_timeout` treats a tick as late only `if let Some(t) = self.next_tick` (timers.rs:46-48), so
/// the first tick, with `next_tick` still `None`, is never late, though `poll_timeout` gave `self.born` as its due
/// time. Who can trigger it: no one in particular; a node suspended (a laptop lid, a phone sent to the background)
/// after it read its hubs' first frames and before its host served the first timer.
#[test]
fn a_suspension_before_the_first_tick_reports_a_live_member_down() {
    let (down, kept) = suspended_right_after_start(true);
    assert!(!down && kept, "control: a late tick after an on-time one: reported down {down}, kept {kept}");
    let (down, kept) = suspended_right_after_start(false);
    assert!(!down, "a late first tick let a DOWN read at the wake remove X at once (in the view 30 s later: {kept})");
}
