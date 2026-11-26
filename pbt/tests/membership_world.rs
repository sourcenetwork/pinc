//! `pinc-membership` as a network: 1 to 3 hub machines and 2 to 5 member machines of the real
//! [`pinc_membership::Membership`], exchanging their real frames over sessions a generated script drives (sessions
//! closed, superseded and silently cut, carriers dropped, frames delayed, nodes suspended, crashed, restarted with a
//! new incarnation, leaving, revoked, moving to other hubs, timers served late), then a heal, then the agreement of
//! every view with the network.
//!
//! The host model follows the project's own world (`tests/membership_world.rs`): hub streams are reliable and in
//! order within one session (a cut delays, it never drops), a member's transport answers on whichever path works, a
//! relayed probe needs both relay legs, transport keepalives refresh the evidence, and a session silent past the
//! give-up bound (`Session::give_up`, 60 s) is closed by the transport. The host reports `session_down` only for its
//! current session to a peer, so a superseding session comes up with no down first (`pinc-node` `hub_closed`). A hub
//! with the role and nothing else ("the relay binary") has a persistent store and never leaves, moves or changes its
//! stack; a hub that is an ordinary node may do all three.
//!
//! Where the expected behaviour comes from:
//! - `docs/proofs/properties.md`, membership, completeness: "a failed member leaves every live view within the
//!   awareness bound"; convergence: "views merge to the union of fresh hubs with the highest incarnation";
//!   `consts::AWARENESS_BOUND`: "The longest a change of the group (a join, a leave or a crash) takes to reach every
//!   live member". After the heal every live view must equal the live attached nodes, records at their current
//!   incarnation (`views_converge_after_the_heal`, checked two awareness bounds after the heal).
//! - properties.md, membership, accuracy: "a live member is never confirmed down by a single lost probe, a slow
//!   member, a snapshot after a heal, or another hub's DOWN while this hub's lease is fresh"; crate docs: "one lost
//!   probe or a slow member never confirms a live node down". With the hubs and some members left alone by every
//!   fault, no node may report one of those members down or gone.
//! - `hub.rs`: "Invariants: a lease only ends by expiry, a confirmation, an accepted DOWN, a leave or a revocation";
//!   "the lease ends [`LEASE`] after the last renewal"; "The hub confirms the member down only when the confirm
//!   deadline has passed, nothing has been heard since the drop"; "A hub accepts another hub's DOWN only when ... this
//!   hub's own lease is stale: not renewed, by frame or by transport evidence, within the longer of the proof's probes
//!   and [`RENEW`]". Each roster drop is checked against its cause and the cause against the network.
//! - `view.rs`: "the view epoch only increases"; crate docs: "Incarnations only go up, across restarts" (checked
//!   across lives for the nodes with a persistent store); `node.rs`: "every table is bounded".
//! - properties.md, membership: "every timer call the host makes moves the deadline past now".
//!
//! The known bug of `repro_membership.rs` (a live member leaves the view at once when the home hub's snapshot is
//! multi-frame or partial) is excluded narrowly: a removal of a protected member made while the machine reads a
//! partial or multi-frame snapshot from its primary is counted, not failed. Most networks start their members a
//! lease after their hubs, so hubs send complete snapshots.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use ephyra::prelude::*;
use pinc_membership::consts::{AWARENESS_BOUND, CONFIRM, LEASE, MAX_TABLE, RENEW};
use pinc_membership::event::Removal;
use pinc_membership::session::{DENIED_CODE, LEAVE_CODE, StoreError};
use pinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Event, Evidence, Frame, Local, Membership, NodeId, Route, Session, Trace,
};

const MS: u64 = 1_000_000;
const SEC: u64 = 1_000 * MS;
const GIVE_UP: u64 = 60 * SEC;
const T0: u64 = 1_000 * SEC;
const WALL0: u64 = 1_700_000_000_000;

fn id(i: usize) -> NodeId {
    [u8::try_from(i + 1).expect("small world"); 32]
}

fn ix(n: &NodeId) -> usize {
    usize::from(n[0]) - 1
}

fn norm(a: usize, b: usize) -> (usize, usize) {
    (a.min(b), a.max(b))
}

// ---------------------------------------------------------------------------------------------------------------
// The host of one node.

#[derive(Debug, Default)]
struct Host {
    sessions: BTreeSet<NodeId>,
    ev: BTreeMap<NodeId, Evidence>,
    carriers: BTreeMap<NodeId, Carrier>,
    out: Vec<(NodeId, Route, Vec<u8>)>,
    closed: Vec<(NodeId, CloseReason)>,
    version: u16,
    persistent: bool,
    sealed: Option<u64>,
}

impl Session for Host {
    fn send(&mut self, peer: &NodeId, route: Route, frame: &[u8]) -> bool {
        if !self.sessions.contains(peer) {
            return false;
        }
        self.out.push((*peer, route, frame.to_vec()));
        true
    }
    fn evidence(&self, peer: &NodeId) -> Option<Evidence> {
        self.ev.get(peer).copied()
    }
    fn carrier(&self, member: &NodeId) -> Carrier {
        self.carriers.get(member).copied().unwrap_or_default()
    }
    fn close(&mut self, peer: &NodeId, reason: CloseReason) {
        self.closed.push((*peer, reason));
    }
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
        self.version
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

// ---------------------------------------------------------------------------------------------------------------
// The world.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Life {
    Alive,
    Crashed,
    Left,
    Revoked,
}

struct Nd {
    m: Membership,
    h: Host,
    hub: bool,
    dedicated: bool,
    steady: bool,
    off: u64,
    life: Life,
    lno: u32,
    asleep_until: u64,
    lag: u64,
    want: BTreeSet<usize>,
    /// The host's current session to each peer (the session id).
    link: BTreeMap<usize, u64>,
    /// Session downs that reached the node while it was suspended, reported at its wake.
    pending: Vec<(usize, u64, u64)>,
    /// The last frame from each peer this life read, on the node's clock.
    last_frame: BTreeMap<usize, u64>,
    epoch: u64,
    inc: u64,
    prev_lives_inc: u64,
    last_view_event: Option<u64>,
    /// The world time until which the node was last unreachable (suspended, crashed, restarted).
    unreach_end: u64,
}

struct Sess {
    sid: u64,
    a: usize,
    b: usize,
    gens: (u32, u32),
}

struct Stream {
    from: usize,
    to: usize,
    to_gen: u32,
    from_gen: u32,
    q: VecDeque<(u64, Vec<u8>)>,
    last_at: u64,
}

enum Sched {
    Up { sid: u64 },
    Down { to: usize, lno: u32, peer: usize, code: u64, sid: u64 },
    Via { to: usize, to_gen: u32, from: usize, hub: usize, bytes: Vec<u8> },
    Revoke { at: usize, lno: u32, x: usize },
    Uncut { pair: (usize, usize) },
    Wake { i: usize, timer_first: bool },
    Join { i: usize },
}

/// What a call into a machine was, for the checks that depend on it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Ctx {
    Other,
    /// Bytes from a peer; whether they held a partial or multi-frame snapshot.
    Bytes { peer: usize, odd_snap: bool },
    Revoke(usize),
}

struct World {
    now: u64,
    n: Vec<Nd>,
    nh: usize,
    lat: u64,
    calm: bool,
    sess: BTreeMap<(usize, usize), Sess>,
    sid_pair: BTreeMap<u64, (usize, usize)>,
    streams: BTreeMap<(u64, usize), Stream>,
    cut: BTreeMap<(usize, usize), u32>,
    cut_end: BTreeMap<(usize, usize), u64>,
    slow: BTreeMap<(usize, usize), u64>,
    sched: BTreeMap<(u64, u64), Sched>,
    seq: u64,
    next_sid: u64,
    keepalive: u64,
    next_ka: u64,
    redial: bool,
    next_house: u64,
    revoked: BTreeSet<usize>,
    /// When each hub's carrier of each member went down (world time).
    carrier_down: BTreeMap<(usize, usize), u64>,
    /// Members some hub confirmed down, with the life confirmed.
    confirmed: BTreeSet<(usize, u32)>,
    known_bug: u32,
    /// (hub, member) -> the hub whose relay carried the hub's last relayed probe of the member.
    probe_via: BTreeMap<(usize, usize), usize>,
    /// (receiver, hub) -> whether the last snapshot the receiver read from the hub was complete, with both lives.
    last_snap: BTreeMap<(usize, usize), (bool, u32, u32)>,
    steps: u64,
}

impl World {
    fn new(net: &Net) -> Self {
        let nh = usize::from(net.hubs);
        let total = nh + usize::from(net.members);
        let hubs: Vec<NodeId> = (0..nh).map(id).collect();
        let mut n = Vec::new();
        for i in 0..total {
            let hub = i < nh;
            let dedicated = hub && net.dedicated;
            let k = i.saturating_sub(nh);
            let mask = net.want.get(k).copied().unwrap_or(1) & ((1u8 << nh) - 1);
            let want: BTreeSet<usize> = if hub {
                (0..nh).filter(|&x| x != i).collect()
            } else if mask == 0 {
                BTreeSet::from([k % nh])
            } else {
                (0..nh).filter(|&x| mask & (1 << x) != 0).collect()
            };
            let mut h = Host { version: 7, persistent: dedicated, ..Host::default() };
            let off = u64::from(net.off_ms.get(i).copied().unwrap_or(0)) * MS;
            let cfg = Config { me: id(i), is_hub: hub, hubs: &hubs, trace: true };
            let m = Membership::start(&cfg, &mut h, T0 + off, WALL0 + (T0 + off) / MS, 0).expect("a valid start");
            let steady = !hub && (net.steady >> k) & 1 == 1;
            n.push(Nd {
                epoch: m.view_epoch(),
                inc: m.incarnation(),
                m,
                h,
                hub,
                dedicated,
                steady,
                off,
                life: Life::Alive,
                lno: 0,
                asleep_until: 0,
                lag: 0,
                want,
                link: BTreeMap::new(),
                pending: Vec::new(),
                last_frame: BTreeMap::new(),
                prev_lives_inc: 0,
                last_view_event: None,
                unreach_end: 0,
            });
        }
        if net.calm && !n.iter().any(|x| x.steady) {
            n[nh].steady = true;
        }
        let mut w = Self {
            now: T0,
            n,
            nh,
            lat: u64::from(net.lat_ms) * MS,
            calm: net.calm,
            sess: BTreeMap::new(),
            sid_pair: BTreeMap::new(),
            streams: BTreeMap::new(),
            cut: BTreeMap::new(),
            cut_end: BTreeMap::new(),
            slow: BTreeMap::new(),
            sched: BTreeMap::new(),
            seq: 0,
            next_sid: 1,
            keepalive: u64::from(net.keepalive_s) * SEC,
            next_ka: T0 + u64::from(net.keepalive_s) * SEC,
            redial: true,
            next_house: T0 + SEC,
            revoked: BTreeSet::new(),
            carrier_down: BTreeMap::new(),
            confirmed: BTreeSet::new(),
            known_bug: 0,
            probe_via: BTreeMap::new(),
            last_snap: BTreeMap::new(),
            steps: 0,
        };
        if net.late_members {
            // The members start a lease after their hubs, so the hubs' snapshots are complete.
            for i in nh..total {
                w.n[i].life = Life::Crashed;
                w.push(T0 + LEASE + 5 * SEC, Sched::Join { i });
            }
        }
        w
    }

    fn push(&mut self, at: u64, s: Sched) {
        self.seq += 1;
        self.sched.insert((at, self.seq), s);
    }

    fn now_of(&self, i: usize) -> u64 {
        self.now + self.n[i].off
    }

    fn alive(&self, i: usize) -> bool {
        self.n[i].life == Life::Alive
    }

    fn awake(&self, i: usize) -> bool {
        self.alive(i) && self.n[i].asleep_until <= self.now
    }

    fn is_cut(&self, a: usize, b: usize) -> bool {
        self.cut.get(&norm(a, b)).is_some_and(|c| *c > 0)
    }

    /// Whether packets from `a` reach `b` now: the pair is not cut, or `a` is a member whose transport takes a path
    /// through a hub it holds a session with and that reaches `b`.
    fn dir_ok(&self, a: usize, b: usize) -> bool {
        if !self.is_cut(a, b) {
            return true;
        }
        !self.n[a].hub
            && (0..self.nh).any(|y| {
                y != a && y != b && self.awake(y) && self.n[a].link.contains_key(&y) && !self.is_cut(a, y) && !self.is_cut(y, b)
            })
    }

    /// Whether both paths hub `i` probed member `x` on broke since `since`: the session (the pair cut) and the relay
    /// of the hub it chose (`x` holds no session with it, or a leg of it was cut). The hub takes the first relay the
    /// host accepts (properties.md, accuracy: "the first one the host takes it for"), which need not reach `x`.
    fn probed_paths_broken(&self, i: usize, x: usize, since: u64) -> bool {
        let broke = |a: usize, b: usize| self.is_cut(a, b) || self.cut_end.get(&norm(a, b)).is_some_and(|e| *e >= since);
        broke(i, x)
            && self.probe_via.get(&(i, x)).is_none_or(|&r| {
                // The hub waits CONFIRM or three session round trips (hub.rs `carrier_watch`) for either probe; a
                // relay leg slower than that cannot answer in time, and no doc promises a longer wait for it.
                let relay_rtt = 2 * (self.one_way(i, r) + self.one_way(r, x));
                let wait = CONFIRM.max(6 * self.one_way(i, x));
                !self.n[x].link.contains_key(&r)
                    || !self.n[r].link.contains_key(&x)
                    || broke(r, x)
                    || broke(i, r)
                    || relay_rtt >= wait
            })
    }

    fn one_way(&self, a: usize, b: usize) -> u64 {
        self.lat + self.slow.get(&norm(a, b)).copied().unwrap_or(0)
    }

    // ----------------------------------------------------------------------------------- calls into a machine

    fn sync(&mut self, i: usize) {
        let peers: BTreeSet<NodeId> = self.n[i].link.keys().map(|&p| id(p)).collect();
        // The transport's round-trip estimate follows the path (its keepalives sample it).
        let rtt: Vec<(NodeId, u64)> = self.n[i].link.keys().map(|&p| (id(p), 2 * self.one_way(i, p))).collect();
        let h = &mut self.n[i].h;
        h.ev.retain(|k, _| peers.contains(k));
        for (p, srtt) in rtt {
            if let Some(e) = h.ev.get_mut(&p) {
                e.srtt = srtt;
            }
        }
        h.sessions = peers;
    }

    fn call<R>(&mut self, i: usize, ctx: Ctx, f: impl FnOnce(&mut Membership, &mut Host, u64) -> R) -> R {
        self.sync(i);
        let now_i = self.now_of(i);
        let total = self.n.len();
        let roster_before: Vec<usize> =
            if self.n[i].hub { (0..total).filter(|&j| self.n[i].m.lease_of(&id(j)).is_some()).collect() } else { Vec::new() };
        let primary_before = self.n[i].m.primary().map(ix);
        let nd = &mut self.n[i];
        let r = f(&mut nd.m, &mut nd.h, now_i);
        self.after(i, now_i, ctx, &roster_before, primary_before);
        r
    }

    /// The checks of one call, then its sends and closes. The checks come first: a close reports back into the same
    /// machine, and that nested call must not take this call's traces.
    fn after(&mut self, i: usize, now_i: u64, ctx: Ctx, roster_before: &[usize], primary_before: Option<usize>) {
        let primary_after = self.n[i].m.primary().map(ix);
        let odd_primary_snap = match ctx {
            Ctx::Bytes { peer, odd_snap } => odd_snap && (primary_before == Some(peer) || primary_after == Some(peer)),
            _ => false,
        };
        let mut causes: BTreeSet<usize> = BTreeSet::new();
        let traces: Vec<Trace> = std::iter::from_fn(|| self.n[i].m.poll_trace()).collect();
        if std::env::var_os("WORLD_DEBUG").is_some() {
            for t in &traces {
                eprintln!("{:>9} ms N{i}: {t:?}", self.now / MS);
            }
            for (p, r, b) in &self.n[i].h.out {
                eprintln!("{:>9} ms N{i} -> {}: {r:?} {:?}", self.now / MS, ix(p), Frame::read(b).ok().flatten().map(|(f, _)| f));
            }
        }
        for t in &traces {
            self.check_trace(i, now_i, t, odd_primary_snap, &mut causes);
        }
        let events: Vec<Event> = std::iter::from_fn(|| self.n[i].m.poll_event()).collect();
        for e in &events {
            self.check_event(i, e, odd_primary_snap);
        }
        if let Ctx::Revoke(x) = ctx {
            causes.insert(x);
        }
        // hub.rs: "a lease only ends by expiry, a confirmation, an accepted DOWN, a leave or a revocation".
        for &j in roster_before {
            if self.n[i].m.lease_of(&id(j)).is_none() {
                assert!(causes.contains(&j), "hub {i} dropped the lease of {j} with no expiry, confirmation, DOWN, leave or revocation");
            }
        }
        let m = &self.n[i].m;
        assert!(m.view_epoch() >= self.n[i].epoch, "node {i}: the view epoch went down");
        assert!(m.incarnation() >= self.n[i].inc, "node {i}: the incarnation went down");
        assert!(m.member_count() <= MAX_TABLE && m.roster_len() <= MAX_TABLE, "node {i}: a table over its bound");
        assert!(!m.in_view(&id(i)), "node {i} lists itself");
        for r in &self.revoked {
            if self.n[i].life == Life::Alive && self.revoked_at(i, *r) {
                assert!(!m.in_view(&id(*r)), "node {i} lists the revoked node {r}");
            }
        }
        let (e, inc) = (m.view_epoch(), m.incarnation());
        self.n[i].epoch = e;
        self.n[i].inc = inc;
        let out = std::mem::take(&mut self.n[i].h.out);
        for (peer, route, bytes) in out {
            assert_ne!(peer, id(i), "node {i} sent to itself");
            if let Route::Via(r) = route {
                self.probe_via.insert((i, ix(&peer)), ix(&r));
            }
            self.route(i, ix(&peer), route, bytes);
        }
        let closed = std::mem::take(&mut self.n[i].h.closed);
        for (peer, reason) in closed {
            let code = match reason {
                CloseReason::Leave => LEAVE_CODE,
                CloseReason::Revoked => DENIED_CODE,
                _ => 0,
            };
            self.close_link(i, ix(&peer), code);
        }
    }

    /// Whether node `i`'s machine was told that `x` is revoked (the revocations reach each node at its own time).
    fn revoked_at(&self, i: usize, x: usize) -> bool {
        !self.sched.values().any(|s| matches!(s, Sched::Revoke { at, x: y, .. } if *at == i && *y == x))
    }

    fn check_trace(&mut self, i: usize, now_i: u64, t: &Trace, odd: bool, causes: &mut BTreeSet<usize>) {
        match *t {
            Trace::LeaseExpired { member } => {
                let x = ix(&member);
                causes.insert(x);
                // hub.rs: "the lease ends LEASE after the last renewal"; any frame renews it.
                let last = self.n[i].last_frame.get(&x).copied().unwrap_or(0);
                assert!(now_i.saturating_sub(last) > LEASE, "hub {i} expired the lease of {x} {} ms after a frame from it", (now_i - last) / MS);
                if let Some(ev) = self.n[i].h.ev.get(&member) {
                    assert!(now_i.saturating_sub(ev.last_rx) > LEASE, "hub {i} expired the lease of {x} with fresh transport evidence");
                }
            },
            Trace::Confirmed { member, .. } => {
                let x = ix(&member);
                causes.insert(x);
                self.confirmed.insert((x, self.n[x].lno));
                // hub.rs: confirmed down only when "nothing has been heard since the drop" and a probe on an
                // independent path went unanswered: the member was in fact unreachable from this hub since the drop.
                let since = self.carrier_down.get(&(i, x)).copied().unwrap_or(0);
                // A member that closed its session to this hub (a move) cannot answer either probe: both ride it
                // (pinc-node hosts.rs: "a relayed probe for a member with no session" is not sent).
                let gone = self.n[x].life != Life::Alive
                    || !self.n[x].link.contains_key(&i)
                    || self.n[x].unreach_end >= since
                    // The hub itself was suspended since the drop: the answers wait unread while its confirm deadline
                    // passes, and a hub opens no quiet window for a late tick (timers.rs, `!self.is_hub`). No doc
                    // promises more for a suspended hub; see the report.
                    || self.n[i].unreach_end >= since
                    || self.probed_paths_broken(i, x, since)
                    || !self.awake(x)
                    || !self.dir_ok(x, i)
                    || self.cut_end.get(&norm(i, x)).is_some_and(|e| *e >= since);
                assert!(gone, "hub {i} confirmed {x} down while it was reachable since its carrier dropped");
            },
            Trace::DownAccepted { member } => {
                let x = ix(&member);
                causes.insert(x);
                assert!(self.confirmed.iter().any(|(y, _)| *y == x), "hub {i} accepted a DOWN of {x} that no hub confirmed");
                let last = self.n[i].last_frame.get(&x).copied().unwrap_or(0);
                assert!(now_i.saturating_sub(last) > RENEW, "hub {i} accepted a DOWN of {x} {} ms after a frame from it", (now_i - last) / MS);
            },
            Trace::LeaveSeen { member } => {
                let x = ix(&member);
                causes.insert(x);
                assert_eq!(self.n[x].life, Life::Left, "hub {i} saw {x} leave, which it did not");
            },
            Trace::Removed { member, why } => {
                let x = ix(&member);
                match why {
                    Removal::Left => assert_eq!(self.n[x].life, Life::Left, "node {i} removed {x} as left"),
                    Removal::Revoked => assert!(self.revoked.contains(&x), "node {i} removed {x} as revoked"),
                    Removal::Reported | Removal::LeaseExpired => {
                        if self.protected(x) {
                            if odd {
                                self.known_bug += 1;
                            } else {
                                panic!("node {i} removed the live, attached member {x} ({why:?})");
                            }
                        }
                    },
                }
            },
            _ => {},
        }
    }

    fn check_event(&mut self, i: usize, e: &Event, odd: bool) {
        match *e {
            Event::MemberConfirmedDown { member } => {
                let x = ix(&member);
                if self.protected(x) && !odd {
                    panic!("node {i} reported the live, attached member {x} down");
                }
            },
            Event::MemberLeft { member } => {
                assert_eq!(self.n[ix(&member)].life, Life::Left, "node {i} reported {} left", ix(&member));
            },
            Event::ViewChanged { epoch, .. } => {
                let nd = &mut self.n[i];
                assert!(nd.last_view_event.is_none_or(|l| epoch > l), "node {i}: a view epoch event did not increase");
                assert!(epoch <= nd.m.view_epoch(), "node {i}: a view epoch event from the future");
                nd.last_view_event = Some(epoch);
            },
            _ => {},
        }
    }

    /// A member no fault touches, in a network whose hubs no fault touches: the accuracy oracle covers it.
    fn protected(&self, x: usize) -> bool {
        self.calm && self.n.get(x).is_some_and(|n| n.steady && n.life == Life::Alive)
    }

    // ----------------------------------------------------------------------------------- the network

    fn route(&mut self, from: usize, to: usize, route: Route, bytes: Vec<u8>) {
        match route {
            Route::Session | Route::Reply => {
                let Some(s) = self.sess.get(&norm(from, to)) else { return };
                let sid = s.sid;
                let at = self.now + self.one_way(from, to);
                if let Some(st) = self.streams.get_mut(&(sid, from)) {
                    let at = at.max(st.last_at);
                    st.last_at = at;
                    st.q.push_back((at, bytes));
                }
            },
            Route::Via(hub) => {
                let hub = ix(&hub);
                let at = self.now + self.one_way(from, hub) + self.one_way(hub, to);
                let to_gen = self.n[to].lno;
                self.push(at, Sched::Via { to, to_gen, from, hub, bytes });
            },
        }
    }

    fn dial(&mut self, a: usize, b: usize) {
        if a == b || !self.awake(a) || self.revoked.contains(&a) || self.revoked.contains(&b) {
            return;
        }
        let sid = self.next_sid;
        self.next_sid += 1;
        let gens = (self.n[a].lno, self.n[b].lno);
        if let Some(old) = self.sess.insert(norm(a, b), Sess { sid, a, b, gens }) {
            // The old session stays readable until it closes; nothing more is written to it.
            self.sid_pair.remove(&old.sid);
            let end = self.now + 2 * SEC;
            for k in [(old.sid, a), (old.sid, b)] {
                if let Some(st) = self.streams.get_mut(&k) {
                    st.q.retain(|(t, _)| *t <= end);
                }
            }
        }
        self.sid_pair.insert(sid, norm(a, b));
        for (x, y) in [(a, b), (b, a)] {
            self.streams.insert(
                (sid, x),
                Stream { from: x, to: y, to_gen: self.n[y].lno, from_gen: self.n[x].lno, q: VecDeque::new(), last_at: 0 },
            );
        }
        let at = self.now + self.one_way(a, b);
        self.push(at, Sched::Up { sid });
    }

    fn drop_session(&mut self, sid: u64) {
        if let Some(pair) = self.sid_pair.remove(&sid) {
            self.sess.remove(&pair);
        }
        self.streams.retain(|k, _| k.0 != sid);
    }

    /// Node `i` closes its session with `p` (a close the machine asked for, a move, a give-up): both ends report it.
    fn close_link(&mut self, i: usize, p: usize, code: u64) {
        let Some(sid) = self.n[i].link.get(&p).copied() else { return };
        let world = self.sess.get(&norm(i, p)).is_some_and(|s| s.sid == sid);
        if world {
            self.drop_session(sid);
            let at = self.now + self.one_way(i, p);
            let lno = self.n[p].lno;
            self.push(at, Sched::Down { to: p, lno, peer: i, code, sid });
        }
        self.report_down(i, p, 0, sid);
    }

    fn report_down(&mut self, to: usize, peer: usize, code: u64, sid: u64) {
        if self.n[to].link.get(&peer) != Some(&sid) || self.n[to].life != Life::Alive && self.n[to].life != Life::Left {
            return;
        }
        if !self.awake(to) && self.n[to].life == Life::Alive {
            self.n[to].pending.push((peer, code, sid));
            return;
        }
        self.n[to].link.remove(&peer);
        let pid = id(peer);
        self.call(to, Ctx::Other, |m, h, now| m.session_down(h, now, &pid, code));
        if self.n[to].hub && !self.n[peer].hub {
            self.carrier_gone(to, peer, None);
        }
    }

    fn carrier_gone(&mut self, hub: usize, member: usize, sleep: Option<u64>) {
        if !self.awake(hub) || self.n[hub].h.carriers.get(&id(member)).is_some_and(|c| matches!(c, Carrier::Gone { .. })) {
            return;
        }
        let since = self.now_of(hub);
        self.n[hub].h.carriers.insert(id(member), Carrier::Gone { since, sleep: sleep.map(|s| since.saturating_sub(s)) });
        self.carrier_down.insert((hub, member), self.now);
        let mid = id(member);
        self.call(hub, Ctx::Other, |m, h, now| m.carrier_gone(h, now, &mid));
    }

    fn carrier_open(&mut self, hub: usize, member: usize) {
        let was = self.n[hub].h.carriers.insert(id(member), Carrier::Open);
        if matches!(was, Some(Carrier::Gone { .. })) {
            let mid = id(member);
            self.call(hub, Ctx::Other, |m, h, now| m.carrier_return(h, now, &mid));
        }
    }

    fn session_up(&mut self, sid: u64) {
        let Some(pair) = self.sid_pair.get(&sid).copied() else { return };
        let Some(s) = self.sess.get(&pair) else { return };
        let (a, b, gens) = (s.a, s.b, s.gens);
        if !self.alive(a) || !self.alive(b) || gens != (self.n[a].lno, self.n[b].lno) {
            self.drop_session(sid);
            return;
        }
        if !self.awake(a) || !self.awake(b) || self.is_cut(a, b) {
            // The handshake waits for both ends and the path.
            let at = self.n[a].asleep_until.max(self.n[b].asleep_until).max(self.now) + 200 * MS;
            self.push(at, Sched::Up { sid });
            return;
        }
        for (x, y, incoming) in [(b, a, true), (a, b, false)] {
            // The first end may refuse the session (a revoked peer), which closes it.
            if !self.alive(x) || !self.alive(y) || !self.sid_pair.contains_key(&sid) {
                return;
            }
            self.n[x].link.insert(y, sid);
            let srtt = 2 * self.one_way(x, y);
            let now_x = self.now_of(x);
            self.n[x].h.ev.insert(id(y), Evidence { last_rx: now_x, srtt, pto: 0, inflight: 0, direct: true });
            let yid = id(y);
            self.call(x, Ctx::Other, |m, h, now| m.session_up(h, now, &yid, incoming));
        }
        for (hub, mem) in [(a, b), (b, a)] {
            if self.n[hub].hub && !self.n[mem].hub && self.n[hub].link.get(&mem) == Some(&sid) {
                self.carrier_open(hub, mem);
            }
        }
    }

    fn deliver(&mut self) {
        let keys: Vec<(u64, usize)> = self.streams.keys().copied().collect();
        for k in keys {
            let Some(st) = self.streams.get(&k) else { continue };
            let (from, to) = (st.from, st.to);
            if st.q.front().is_none_or(|(t, _)| *t > self.now) {
                continue;
            }
            if self.n[to].lno != st.to_gen || self.n[from].lno != st.from_gen || !self.alive(from) {
                self.streams.remove(&k);
                continue;
            }
            if !self.awake(to) || !self.dir_ok(from, to) || !self.n[to].link.contains_key(&from) {
                continue;
            }
            let mut bytes = Vec::new();
            if let Some(st) = self.streams.get_mut(&k) {
                while st.q.front().is_some_and(|(t, _)| *t <= self.now) {
                    if let Some((_, b)) = st.q.pop_front() {
                        bytes.extend(b);
                    }
                }
            }
            self.receive(to, from, &bytes);
        }
    }

    fn receive(&mut self, to: usize, from: usize, bytes: &[u8]) {
        let now_to = self.now_of(to);
        if let Some(e) = self.n[to].h.ev.get_mut(&id(from)) {
            e.last_rx = now_to;
        }
        if self.awake(from) && self.dir_ok(to, from) {
            let now_from = self.now_of(from);
            if let Some(e) = self.n[from].h.ev.get_mut(&id(to)) {
                e.last_rx = now_from;
            }
        }
        let mut odd_snap = false;
        let mut at = 0;
        while let Ok(Some((f, n))) = Frame::read(&bytes[at..]) {
            if let Frame::Snap(s) = f {
                odd_snap |= s.partial || s.more;
                if !s.more && self.n[from].hub {
                    self.last_snap.insert((to, from), (!s.partial, self.n[from].lno, self.n[to].lno));
                }
            }
            at += n;
        }
        self.n[to].last_frame.insert(from, now_to);
        let pid = id(from);
        // A call parses at most MAX_FRAMES_PER_CALL frames; the host calls again with the rest.
        let mut at = 0;
        while at < bytes.len() && self.awake(to) {
            let rest = &bytes[at..];
            let used = self.call(to, Ctx::Bytes { peer: from, odd_snap }, |m, h, now| m.on_bytes(h, now, &pid, rest));
            assert!(used.is_ok_and(|u| u > 0), "node {to} did not read the frames from {from}: {used:?}");
            at += used.unwrap_or(bytes.len());
        }
    }

    fn keepalives(&mut self) {
        for e in 0..self.n.len() {
            if !self.awake(e) {
                continue;
            }
            let links: Vec<(usize, u64)> = self.n[e].link.iter().map(|(p, s)| (*p, *s)).collect();
            for (p, sid) in links {
                if self.sess.get(&norm(e, p)).is_some_and(|s| s.sid == sid) && self.awake(p) && self.dir_ok(p, e) {
                    let now_e = self.now_of(e);
                    if let Some(ev) = self.n[e].h.ev.get_mut(&id(p)) {
                        ev.last_rx = now_e;
                    }
                }
            }
        }
    }

    /// The transport gives up a session silent past its bound.
    fn give_ups(&mut self) {
        for e in 0..self.n.len() {
            if !self.awake(e) {
                continue;
            }
            let now_e = self.now_of(e);
            let silent: Vec<usize> = self.n[e]
                .link
                .keys()
                .copied()
                .filter(|p| self.n[e].h.ev.get(&id(*p)).is_none_or(|ev| now_e.saturating_sub(ev.last_rx) > GIVE_UP))
                .collect();
            for p in silent {
                self.close_link(e, p, 0);
            }
        }
    }

    fn redials(&mut self) {
        for a in 0..self.n.len() {
            if !self.awake(a) || self.revoked.contains(&a) {
                continue;
            }
            let want: Vec<usize> = self.n[a].want.iter().copied().collect();
            for b in want {
                // Between two hubs one side dials (the higher id), so a pair gets one session.
                if self.n[a].hub && b > a {
                    continue;
                }
                if !self.sess.contains_key(&norm(a, b)) && !self.n[a].link.contains_key(&b) && self.alive(b) && !self.is_cut(a, b) {
                    self.dial(a, b);
                }
            }
        }
    }

    fn timers(&mut self) {
        for i in 0..self.n.len() {
            if !self.awake(i) {
                continue;
            }
            let now_i = self.now_of(i);
            if self.serve_at(i) <= now_i {
                self.call(i, Ctx::Other, |m, h, now| m.on_timeout(h, now));
                let next = self.n[i].m.poll_timeout();
                assert!(next > now_i, "node {i}: a timer call left the deadline at or before now");
            }
        }
    }

    /// When the host serves node `i`'s next timer, on its own clock.
    fn serve_at(&self, i: usize) -> u64 {
        let due = self.n[i].m.poll_timeout();
        let lag = self.n[i].lag;
        if lag == 0 { due } else { due.div_ceil(lag).saturating_mul(lag) }
    }

    fn run_sched(&mut self, s: Sched) {
        match s {
            Sched::Up { sid } => self.session_up(sid),
            Sched::Down { to, lno, peer, code, sid } => {
                if self.n[to].lno == lno {
                    self.report_down(to, peer, code, sid);
                }
            },
            Sched::Via { to, to_gen, from, hub, bytes } => {
                let ok = self.awake(to)
                    && self.awake(hub)
                    && self.alive(from)
                    && self.n[to].lno == to_gen
                    && self.sess.contains_key(&norm(from, hub))
                    && self.sess.contains_key(&norm(hub, to))
                    && !self.is_cut(from, hub)
                    && !self.is_cut(hub, to);
                if ok {
                    self.receive(to, from, &bytes);
                }
            },
            Sched::Revoke { at, lno, x } => {
                if self.alive(at) && self.n[at].lno == lno {
                    if !self.awake(at) {
                        let when = self.n[at].asleep_until;
                        self.push(when, Sched::Revoke { at, lno, x });
                        return;
                    }
                    let xid = id(x);
                    let ok = self.call(at, Ctx::Revoke(x), |m, h, now| m.revoke(h, now, &xid).is_ok());
                    assert!(ok, "a revocation was refused in a small table");
                }
            },
            Sched::Uncut { pair } => {
                if let Some(c) = self.cut.get_mut(&pair) {
                    *c = c.saturating_sub(1);
                }
                self.cut_end.insert(pair, self.now);
            },
            Sched::Wake { i, timer_first } => {
                if !self.alive(i) || self.n[i].asleep_until > self.now {
                    return;
                }
                self.n[i].unreach_end = self.now;
                for (p, code, sid) in std::mem::take(&mut self.n[i].pending) {
                    self.report_down(i, p, code, sid);
                }
                if timer_first && self.serve_at(i) <= self.now_of(i) {
                    self.call(i, Ctx::Other, |m, h, now| m.on_timeout(h, now));
                }
                let hubs: Vec<usize> = (0..self.nh).filter(|&h| self.n[h].link.contains_key(&i)).collect();
                for h in hubs {
                    self.carrier_open(h, i);
                }
            },
            Sched::Join { i } => self.restart(i, 0),
        }
    }

    fn next_time(&self, end: u64) -> u64 {
        let mut t = end.min(self.next_house).min(self.next_ka);
        if let Some((k, _)) = self.sched.first_key_value() {
            t = t.min(k.0);
        }
        for st in self.streams.values() {
            if let Some((at, _)) = st.q.front()
                && self.awake(st.to)
                && self.dir_ok(st.from, st.to)
                && self.n[st.to].link.contains_key(&st.from)
            {
                t = t.min(*at);
            }
        }
        for i in 0..self.n.len() {
            if self.awake(i) {
                t = t.min(self.serve_at(i).saturating_sub(self.n[i].off));
            }
        }
        t.max(self.now)
    }

    fn run_to(&mut self, end: u64) {
        let mut same = 0u32;
        loop {
            let t = self.next_time(end);
            if t >= end && t > self.now {
                self.now = end;
                break;
            }
            same = if t == self.now { same + 1 } else { 0 };
            assert!(same < 10_000, "the world stopped making progress at {}", self.now);
            self.now = t;
            self.steps += 1;
            assert!(self.steps < 3_000_000, "the world ran too many steps");
            while let Some((&k, _)) = self.sched.first_key_value() {
                if k.0 > self.now {
                    break;
                }
                let s = self.sched.remove(&k).expect("the first key");
                self.run_sched(s);
            }
            self.deliver();
            if self.now >= self.next_ka {
                self.next_ka = self.now + self.keepalive;
                self.keepalives();
            }
            if self.now >= self.next_house {
                self.next_house = self.now + SEC;
                self.give_ups();
                if self.redial && (self.now / SEC) % 2 == 0 {
                    self.redials();
                }
            }
            self.timers();
            if t >= end {
                break;
            }
        }
    }

    // ----------------------------------------------------------------------------------- node lives

    /// A new process for node `i`, on the same store, at the current wall clock. The access-control layer applies the
    /// revocations it holds to the new machine at once.
    fn restart(&mut self, i: usize, back_ms: u64) {
        if self.revoked.contains(&i) {
            return;
        }
        self.kill(i, Life::Crashed);
        let hubs: Vec<NodeId> = (0..self.nh).map(id).collect();
        let now_i = self.now_of(i);
        let cfg = Config { me: id(i), is_hub: self.n[i].hub, hubs: &hubs, trace: true };
        let nd = &mut self.n[i];
        nd.h.ev.clear();
        nd.h.sessions.clear();
        nd.h.carriers.clear();
        nd.h.out.clear();
        nd.h.closed.clear();
        let m = Membership::start(&cfg, &mut nd.h, now_i, (WALL0 + now_i / MS).saturating_sub(back_ms), 0).expect("a restart");
        nd.prev_lives_inc = nd.prev_lives_inc.max(nd.inc);
        if nd.dedicated {
            // "Incarnations only go up, across restarts": a persistent store makes it so whatever the clock.
            assert!(m.incarnation() > nd.prev_lives_inc, "node {i}: a restart issued an incarnation not above the last life's");
        }
        nd.m = m;
        nd.lno += 1;
        nd.life = Life::Alive;
        nd.asleep_until = 0;
        nd.epoch = nd.m.view_epoch();
        nd.inc = nd.m.incarnation();
        nd.last_view_event = None;
        nd.last_frame.clear();
        nd.unreach_end = self.now;
        let _ = std::iter::from_fn(|| self.n[i].m.poll_trace()).count();
        let revoked: Vec<usize> = self.revoked.iter().copied().collect();
        for x in revoked {
            let xid = id(x);
            self.call(i, Ctx::Revoke(x), |m, h, now| m.revoke(h, now, &xid).is_ok());
        }
        let want: Vec<usize> = self.n[i].want.iter().copied().collect();
        for b in want {
            if self.alive(b) && !self.is_cut(i, b) {
                self.dial(i, b);
            }
        }
    }

    /// Node `i` stops: its sessions vanish without a close, the hubs' relays see its carriers close.
    fn kill(&mut self, i: usize, life: Life) {
        let sids: Vec<u64> = self.sess.values().filter(|s| s.a == i || s.b == i).map(|s| s.sid).collect();
        for sid in sids {
            self.drop_session(sid);
        }
        self.n[i].link.clear();
        self.n[i].pending.clear();
        self.n[i].life = life;
        self.n[i].unreach_end = self.now;
        if !self.n[i].hub {
            for hub in 0..self.nh {
                if self.n[hub].link.contains_key(&i) {
                    self.carrier_gone(hub, i, None);
                }
            }
        }
    }

    // ----------------------------------------------------------------------------------- the script

    /// The nodes a fault may touch: in a calm network, only the members no oracle protects.
    fn faultable(&self, k: u8, members_only: bool) -> Option<usize> {
        let c: Vec<usize> = (0..self.n.len())
            .filter(|&i| !(self.calm && (self.n[i].hub || self.n[i].steady)) && !(members_only && self.n[i].hub))
            .collect();
        (!c.is_empty()).then(|| c[usize::from(k) % c.len()])
    }

    /// A pair for a session fault: a faultable node and one of the hubs.
    fn pair(&self, a: u8, b: u8) -> Option<(usize, usize)> {
        let x = self.faultable(a, false)?;
        let mut hubs: Vec<usize> = (0..self.nh).filter(|&h| h != x).collect();
        if self.calm {
            hubs.retain(|_| !self.n[x].hub);
        }
        (!hubs.is_empty()).then(|| (x, hubs[usize::from(b) % hubs.len()]))
    }

    fn apply(&mut self, op: &WOp) {
        match *op {
            WOp::Run(ms) => self.run_to(self.now + u64::from(ms) * MS),
            WOp::Close(a, b) => {
                if let Some((x, y)) = self.pair(a, b)
                    && self.awake(x)
                {
                    self.close_link(x, y, 0);
                }
            },
            WOp::Cut(a, b, secs) => {
                if let Some((x, y)) = self.pair(a, b) {
                    *self.cut.entry(norm(x, y)).or_insert(0) += 1;
                    self.push(self.now + u64::from(secs) * SEC, Sched::Uncut { pair: norm(x, y) });
                }
            },
            WOp::CarrierDrop(a, b) => {
                if let Some((x, y)) = self.pair(a, b)
                    && !self.n[x].hub
                    && self.n[y].link.contains_key(&x)
                {
                    self.carrier_gone(y, x, None);
                }
            },
            WOp::CarrierBack(a, b) => {
                if let Some((x, y)) = self.pair(a, b)
                    && !self.n[x].hub
                    && self.n[y].link.contains_key(&x)
                    && self.awake(y)
                {
                    self.carrier_open(y, x);
                }
            },
            WOp::Slow(a, b, ms) => {
                if let Some((x, y)) = self.pair(a, b) {
                    self.slow.insert(norm(x, y), u64::from(ms) * MS);
                }
            },
            WOp::Sleep(k, ms, notice, timer_first) => {
                if let Some(i) = self.faultable(k, false)
                    && self.awake(i)
                {
                    let until = self.now + u64::from(ms) * MS;
                    self.n[i].asleep_until = until;
                    if notice && !self.n[i].hub {
                        for hub in (0..self.nh).filter(|&h| self.n[h].link.contains_key(&i)).collect::<Vec<_>>() {
                            self.carrier_gone(hub, i, Some(MS));
                        }
                    }
                    self.push(until, Sched::Wake { i, timer_first });
                }
            },
            WOp::Lag(k, ms) => {
                if let Some(i) = self.faultable(k, false) {
                    self.n[i].lag = u64::from(ms) * MS;
                }
            },
            WOp::Crash(k) => {
                if let Some(i) = self.faultable(k, false)
                    && self.alive(i)
                {
                    self.kill(i, Life::Crashed);
                }
            },
            WOp::Restart(k, back_ms) => {
                if let Some(i) = self.faultable(k, false)
                    && self.n[i].life != Life::Left
                {
                    self.restart(i, u64::from(back_ms));
                }
            },
            WOp::Leave(k) => {
                if let Some(i) = self.faultable(k, false)
                    && self.awake(i)
                    && !self.n[i].dedicated
                {
                    self.call(i, Ctx::Other, |m, h, _| m.leave(h));
                    self.n[i].life = Life::Left;
                    self.n[i].unreach_end = u64::MAX;
                }
            },
            WOp::Revoke(k, spread_ms) => {
                if let Some(x) = self.faultable(k, true)
                    && !self.revoked.contains(&x)
                    && self.n[x].life != Life::Left
                {
                    self.revoked.insert(x);
                    let total = self.n.len() as u64;
                    for at in 0..self.n.len() {
                        if at != x && self.alive(at) {
                            let when = self.now + u64::from(spread_ms) * MS * at as u64 / total;
                            let lno = self.n[at].lno;
                            self.push(when, Sched::Revoke { at, lno, x });
                        }
                    }
                    if self.alive(x) {
                        self.kill(x, Life::Revoked);
                    } else {
                        self.n[x].life = Life::Revoked;
                    }
                }
            },
            WOp::Move(k, mask) => {
                if let Some(i) = self.faultable(k, true)
                    && self.awake(i)
                {
                    let mask = mask & ((1u8 << self.nh) - 1);
                    let want: BTreeSet<usize> =
                        if mask == 0 { BTreeSet::from([usize::from(k) % self.nh]) } else { (0..self.nh).filter(|&x| mask & (1 << x) != 0).collect() };
                    let drop: Vec<usize> = self.n[i].link.keys().copied().filter(|p| !want.contains(p)).collect();
                    for p in drop {
                        self.close_link(i, p, 0);
                    }
                    for &b in &want {
                        if !self.sess.contains_key(&norm(i, b)) && self.alive(b) {
                            self.dial(i, b);
                        }
                    }
                    self.n[i].want = want;
                }
            },
            WOp::Supersede(a, b) => {
                if let Some((x, y)) = self.pair(a, b)
                    && self.sess.contains_key(&norm(x, y))
                    && self.awake(x)
                    && self.awake(y)
                {
                    let (d, o) = if self.n[x].hub && x < y { (x, y) } else if self.n[x].hub { (y, x) } else { (x, y) };
                    self.dial(d, o);
                }
            },
            WOp::Version(k) => {
                let i = usize::from(k) % self.n.len();
                if self.awake(i) && !self.n[i].dedicated {
                    self.n[i].h.version += 1;
                }
            },
            WOp::Moved(k) => {
                let i = usize::from(k) % self.n.len();
                if self.awake(i) && !self.n[i].dedicated {
                    self.call(i, Ctx::Other, |m, _, now| m.address_changed(now));
                }
            },
        }
    }

    /// Every fault ends: cuts and slow paths heal, sleepers wake, timers are served on time, every live node dials
    /// its hubs again (a member whose hubs are all gone dials a live one).
    fn heal(&mut self) {
        for c in self.cut.values_mut() {
            *c = 0;
        }
        let pairs: Vec<(usize, usize)> = self.cut.keys().copied().collect();
        for p in pairs {
            self.cut_end.insert(p, self.now);
        }
        self.slow.clear();
        self.redial = true;
        for i in 0..self.n.len() {
            self.n[i].lag = 0;
            if self.alive(i) && self.n[i].asleep_until > self.now {
                self.n[i].asleep_until = self.now;
                self.push(self.now, Sched::Wake { i, timer_first: false });
            }
        }
        let live_hubs: Vec<usize> = (0..self.nh).filter(|&h| self.alive(h)).collect();
        for i in self.nh..self.n.len() {
            if !self.n[i].want.iter().any(|&h| self.alive(h))
                && let Some(&h) = live_hubs.first()
            {
                self.n[i].want.insert(h);
            }
        }
    }

    /// Whether the last snapshot node `j` read from some live hub was partial (that hub was younger than a lease):
    /// a partial snapshot never ages the entries the copy already held, and no complete one is asked for later, so a
    /// node that left or crashed while `j` missed the delta stays listed (`repro_membership2.rs`). A member is also
    /// prone when any hub is, since a hub serves its view to its members.
    fn ghost_prone(&self, j: usize) -> bool {
        let stale_copy = |b: usize| {
            (0..self.nh).any(|p| {
                p != b
                    && self.alive(p)
                    && self.n[b].link.contains_key(&p)
                    && self.last_snap.get(&(b, p)) != Some(&(true, self.n[p].lno, self.n[b].lno))
            })
        };
        stale_copy(j) || (!self.n[j].hub && (0..self.nh).any(|b| self.alive(b) && stale_copy(b)))
    }

    /// Whether node `k` is part of the group as node `j` should see it: alive and attached to a live hub.
    fn expected_in(&self, k: usize) -> bool {
        self.alive(k) && (self.n[k].hub || self.n[k].want.iter().any(|&h| self.alive(h) && self.n[k].link.contains_key(&h)))
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Generators.

#[derive(Debug, Clone, ephyra::Arbitrary)]
struct Net {
    #[ephyra(gen = gens::int(1u8..=3))]
    hubs: u8,
    #[ephyra(gen = gens::int(2u8..=5))]
    members: u8,
    /// The hubs carry the role and nothing else (the relay binary) instead of being ordinary nodes with the role.
    dedicated: bool,
    /// No fault touches a hub or a steady member: the accuracy oracle is on.
    calm: bool,
    #[ephyra(gen = gens::bool_with(0.7))]
    late_members: bool,
    #[ephyra(gen = gens::vec(gens::int(0u8..=7)).len(5..=5))]
    want: Vec<u8>,
    #[ephyra(gen = gens::int(0u8..=31))]
    steady: u8,
    #[ephyra(gen = gens::int(5u8..=30))]
    keepalive_s: u8,
    #[ephyra(gen = gens::int(1u16..=60))]
    lat_ms: u16,
    #[ephyra(gen = gens::vec(gens::int(0u32..=5_000)).len(8..=8))]
    off_ms: Vec<u32>,
}

fn run_ms() -> BoxGen<u32> {
    gens::frequency(vec![
        (5, gens::int(100u32..=5_000).boxed()),
        (3, gens::int(5_000u32..=40_000).boxed()),
        (1, gens::int(40_000u32..=120_000).boxed()),
    ])
    .boxed()
}

fn sleep_ms() -> BoxGen<u32> {
    gens::frequency(vec![
        (3, gens::int(500u32..=3_000).boxed()),
        (3, gens::int(3_000u32..=30_000).boxed()),
        (2, gens::int(30_000u32..=200_000).boxed()),
    ])
    .boxed()
}

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum WOp {
    Run(#[ephyra(gen = run_ms())] u32),
    Close(u8, u8),
    Cut(u8, u8, #[ephyra(gen = gens::int(1u16..=150))] u16),
    CarrierDrop(u8, u8),
    CarrierBack(u8, u8),
    Slow(u8, u8, #[ephyra(gen = gens::int(0u16..=2_000))] u16),
    Sleep(u8, #[ephyra(gen = sleep_ms())] u32, bool, bool),
    Lag(u8, #[ephyra(gen = gens::int(0u16..=4_000))] u16),
    Crash(u8),
    /// A restart whose wall clock reads this many ms behind the last life's (a clock that went back).
    Restart(u8, #[ephyra(gen = clock_back_ms())] u32),
    Leave(u8),
    Revoke(u8, #[ephyra(gen = gens::int(0u16..=3_000))] u16),
    Move(u8, #[ephyra(gen = gens::int(0u8..=7))] u8),
    Supersede(u8, u8),
    Version(u8),
    Moved(u8),
}

fn clock_back_ms() -> BoxGen<u32> {
    gens::frequency(vec![(3, gens::constant(0u32).boxed()), (1, gens::int(1u32..=600_000).boxed())]).boxed()
}

fn world_cases() -> impl Gen<Value = (Net, Vec<WOp>)> {
    (ephyra::any::<Net>(), gens::vec(ephyra::any::<WOp>()).len(0..=30))
}

/// Run the script, heal, and run two awareness bounds; returns the world for the final checks.
fn run_world(net: &Net, ops: &[WOp]) -> World {
    let mut w = World::new(net);
    w.redials();
    let warm = if net.late_members { LEASE + 15 * SEC } else { 10 * SEC };
    w.run_to(T0 + warm);
    for op in ops {
        w.apply(op);
    }
    w.heal();
    let healed = w.now;
    w.run_to(healed + 2 * AWARENESS_BOUND);
    w
}

/// The network keeps every per-step invariant while the faults run, and after the heal and two awareness bounds
/// every live view lists exactly the live attached nodes, each at its current incarnation.
#[ephyra::test(gen = world_cases(), tests = 300)]
fn views_converge_after_the_heal(case: (Net, Vec<WOp>)) {
    let (net, ops) = case;
    let w = run_world(&net, &ops);
    for j in 0..w.n.len() {
        if !w.alive(j) || !w.expected_in(j) {
            continue;
        }
        let want: BTreeSet<usize> = (0..w.n.len()).filter(|&k| k != j && w.expected_in(k)).collect();
        let got: BTreeSet<usize> = w.n[j].m.members().map(|(k, _)| ix(k)).collect();
        let missing: Vec<usize> = want.difference(&got).copied().collect();
        // The ghost of `repro_membership2.rs`: a node gone while a hub restarted stays listed by every node whose copy
        // of that hub came only from partial snapshots since its restart. Excluded for those nodes, nowhere else.
        let ghost_ok = w.ghost_prone(j);
        let extra: Vec<usize> = got.difference(&want).copied().filter(|&k| !(ghost_ok && !w.alive(k))).collect();
        assert!(missing.is_empty(), "node {j} misses live attached nodes {missing:?} after the heal");
        assert!(extra.is_empty(), "node {j} still lists {extra:?}, which are gone, after the heal");
        for (k, r) in w.n[j].m.members() {
            let k = ix(k);
            // The same ghost, for a node whose clock went back on restart: the stale entry of its earlier life holds
            // the higher incarnation and so wins the merge; excluded under the same condition.
            // `a_member_whose_clock_went_back_is_never_told_when_its_home_hub_died`: a node that restarted below its
            // last life's incarnation may never be told; excluded only for such a node and a higher, stale record.
            let behind = w.n[k].prev_lives_inc > w.n[k].m.incarnation();
            if w.alive(k) && !((ghost_ok || behind) && r.inc > w.n[k].m.incarnation()) {
                assert_eq!(
                    r.inc,
                    w.n[k].m.incarnation(),
                    "node {j} holds an old record of {k} after the heal (links of {k}: {:?}, life of hubs: {:?})",
                    w.n[k].link.keys().collect::<Vec<_>>(),
                    (0..w.nh).map(|b| (w.n[b].life, w.n[b].lno)).collect::<Vec<_>>()
                );
            }
        }
    }
}
