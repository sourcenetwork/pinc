//! A small deterministic world for the membership tests: nodes, a network with latency, loss, cuts and dead
//! default paths, a host per node that records everything the machines ask of it, and a virtual clock.
//!
//! Included by the `membership_*` test targets with `#[path]`; not a test target itself.
#![allow(
    dead_code,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::collections::{BTreeMap, BTreeSet};

use vinc_membership::session::{LEAVE_CODE, StoreError};
use vinc_membership::{
    Broadcast, Carrier, CloseReason, Config, Event, Evidence, Frame, Local, Membership, NodeId, Route, Session, Trace,
};
use vinc_tests::SplitMix64;

pub const MS: u64 = 1_000_000;
pub const SEC: u64 = 1_000_000_000;

pub fn id(i: usize) -> NodeId {
    [u8::try_from(i + 1).unwrap(); 32]
}

/// What the machines asked of the broadcast layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bc {
    Frame(NodeId, u8, Vec<u8>, Vec<u8>),
    Hold(NodeId),
    Restore(NodeId),
    Release(NodeId),
    Resub(NodeId),
    Primary(Option<NodeId>, NodeId),
}

#[derive(Debug, Default)]
pub struct Host {
    pub me: NodeId,
    pub out: Vec<(NodeId, Route, Vec<u8>)>,
    pub sessions: BTreeSet<NodeId>,
    pub ev: BTreeMap<NodeId, Evidence>,
    pub carriers: BTreeMap<NodeId, Carrier>,
    pub bc: Vec<Bc>,
    pub closed: Vec<(NodeId, CloseReason)>,
    pub version: u16,
    pub ticket: u8,
    pub reflexive: bool,
    pub persistent: bool,
    pub sealed: Option<u64>,
    pub fail_seal: bool,
    pub fail_unseal: bool,
    /// Every `send` the machine made, with whether a session took it (for the proof traces).
    pub sent_log: Vec<(NodeId, Route, Vec<u8>, bool)>,
}

impl Session for Host {
    fn send(&mut self, peer: &NodeId, route: Route, frame: &[u8]) -> bool {
        let ok = self.sessions.contains(peer);
        self.sent_log.push((*peer, route, frame.to_vec(), ok));
        if !ok {
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
    fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize {
        out[..9].copy_from_slice(&[0xF1, member[0], 0, 0, 0, 0, 0, 0, 1]);
        9
    }
    fn frame(&mut self, from: &NodeId, ty: u8, topic: &[u8], rest: &[u8]) {
        self.bc.push(Bc::Frame(*from, ty, topic.to_vec(), rest.to_vec()));
    }
    fn hold(&mut self, member: &NodeId) {
        self.bc.push(Bc::Hold(*member));
    }
    fn restore(&mut self, member: &NodeId) {
        self.bc.push(Bc::Restore(*member));
    }
    fn release(&mut self, member: &NodeId) {
        self.bc.push(Bc::Release(*member));
    }
    fn resubscribe(&mut self, hub: &NodeId) {
        self.bc.push(Bc::Resub(*hub));
    }
    fn primary_changed(&mut self, old: Option<&NodeId>, new: &NodeId) {
        self.bc.push(Bc::Primary(old.copied(), *new));
    }
}

impl Local for Host {
    fn version(&self) -> u16 {
        self.version
    }
    fn reflexive_known(&self) -> bool {
        self.reflexive
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [self.ticket, moves, 0, 0, 0, 0, 0, 7]
    }
    fn persistent(&self) -> bool {
        self.persistent
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        if self.fail_unseal {
            return Err(StoreError);
        }
        Ok(self.sealed)
    }
    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        if self.fail_seal {
            return Err(StoreError);
        }
        self.sealed = Some(epoch);
        Ok(())
    }
}

pub struct Node {
    pub m: Membership,
    pub h: Host,
    pub up: bool,
    /// Application processing delay for arriving frames (a slow CPU); transport acknowledgements are not delayed.
    pub cpu: u64,
    pub is_hub: bool,
}

/// What the host looked like when a call into a machine was made (for the proof traces).
#[derive(Debug, Clone)]
pub struct EnvSnap {
    pub ev: Vec<(NodeId, Evidence)>,
    pub car: Vec<(NodeId, Carrier)>,
    pub acc: Vec<NodeId>,
    pub ver: u16,
    pub tk: u8,
    pub refl: bool,
    pub pers: bool,
    pub sealed: Option<u64>,
    pub failseal: bool,
    pub failunseal: bool,
}

/// One call into a machine.
#[derive(Debug, Clone)]
pub enum Op {
    Start {
        hub: bool,
        hubs: Vec<NodeId>,
        wall: u64,
        floor: u64,
        ret: &'static str,
    },
    Up {
        peer: NodeId,
        incoming: bool,
    },
    Down {
        peer: NodeId,
        code: u64,
    },
    Bytes {
        peer: NodeId,
        bytes: Vec<u8>,
        used: usize,
        bad: bool,
    },
    Timeout,
    CarrierGone {
        member: NodeId,
    },
    CarrierReturn {
        member: NodeId,
    },
    Leave,
    Revoke {
        member: NodeId,
        ok: bool,
    },
    Moved,
}

/// The public state of a machine after a call.
#[derive(Debug, Clone)]
pub struct StSnap {
    pub members: Vec<(NodeId, vinc_membership::Record)>,
    pub epoch: u64,
    pub primary: Option<NodeId>,
    pub inc: u64,
    pub roster: Vec<(NodeId, u64)>,
    pub seal_failed: bool,
}

/// A recorded call: its inputs, what the machine asked of the host and what it reported.
#[derive(Debug, Clone)]
pub struct Call {
    pub node: usize,
    pub now: u64,
    pub op: Op,
    pub env: EnvSnap,
    pub sent: Vec<(NodeId, Route, Vec<u8>, bool)>,
    pub bc: Vec<Bc>,
    pub closed: Vec<(NodeId, CloseReason)>,
    pub events: Vec<Event>,
    pub traces: Vec<Trace>,
    pub sealed_after: Option<u64>,
    pub st: StSnap,
}

/// Receives every call into a machine of a world, when installed with [`World::set_recorder`].
pub trait Recorder {
    fn record(&mut self, c: Call);
}

#[derive(Debug)]
enum Ev {
    Deliver { to: usize, from: usize, bytes: Vec<u8> },
    Process { to: usize, from: usize, bytes: Vec<u8> },
    Ack { to: usize, from: usize },
    SessionUp { a: usize, b: usize },
    SessionDown { to: usize, from: usize, code: u64 },
}

pub struct World {
    pub now: u64,
    pub nodes: Vec<Node>,
    pub hubs: usize,
    q: BTreeMap<(u64, u64), Ev>,
    seq: u64,
    pub lat: u64,
    pub loss_pct: u64,
    pub rng: SplitMix64,
    pub cut: BTreeSet<(usize, usize)>,
    pub dead_default: BTreeSet<(usize, usize)>,
    pub direct: BTreeSet<(usize, usize)>,
    pub sessions: BTreeSet<(usize, usize)>,
    pub events: Vec<Vec<(u64, Event)>>,
    pub traces: Vec<Vec<Trace>>,
    /// Frames matching this predicate (to, from, type, route) are dropped once each, then removed.
    pub drop_once: Vec<(usize, usize, u8)>,
    pub keepalive: u64,
    next_ka: u64,
    pub sent_types: Vec<(u64, usize, usize, u8, Route)>,
    pub frames: Vec<(u64, usize, usize, Vec<u8>)>,
    pub srtt: BTreeMap<(usize, usize), u64>,
    pub lat_pair: BTreeMap<(usize, usize), u64>,
    last_at: BTreeMap<(usize, usize), u64>,
    rec: Option<Box<dyn Recorder>>,
}

fn key(a: usize, b: usize) -> (usize, usize) {
    (a.min(b), a.max(b))
}

impl World {
    /// `hubs` hubs and `members` members, all started at time `start`.
    pub fn new(hubs: usize, members: usize, start: u64) -> Self {
        let hub_ids: Vec<NodeId> = (0..hubs).map(id).collect();
        let mut nodes = Vec::new();
        for i in 0..hubs + members {
            let mut h = Host {
                me: id(i),
                version: 1,
                ticket: u8::try_from(i).unwrap(),
                reflexive: true,
                ..Host::default()
            };
            let is_hub = i < hubs;
            let cfg = Config {
                me: id(i),
                is_hub,
                hubs: &hub_ids,
                trace: true,
            };
            let m = Membership::start(&cfg, &mut h, start, 1_000_000 + u64::try_from(i).unwrap(), 0).unwrap();
            nodes.push(Node {
                m,
                h,
                up: true,
                cpu: 0,
                is_hub,
            });
        }
        let n = nodes.len();
        Self {
            now: start,
            nodes,
            hubs,
            q: BTreeMap::new(),
            seq: 0,
            lat: 10 * MS,
            loss_pct: 0,
            rng: SplitMix64::new(7),
            cut: BTreeSet::new(),
            dead_default: BTreeSet::new(),
            direct: BTreeSet::new(),
            sessions: BTreeSet::new(),
            events: vec![Vec::new(); n],
            traces: vec![Vec::new(); n],
            drop_once: Vec::new(),
            keepalive: 30 * SEC,
            next_ka: start + 30 * SEC,
            sent_types: Vec::new(),
            frames: Vec::new(),
            srtt: BTreeMap::new(),
            lat_pair: BTreeMap::new(),
            last_at: BTreeMap::new(),
            rec: None,
        }
    }

    /// Set the round trip time between `a` and `b`: one-way latency and the transport's smoothed round trip.
    pub fn set_rtt(&mut self, a: usize, b: usize, rtt: u64) {
        for (x, y) in [(a, b), (b, a)] {
            self.lat_pair.insert((x, y), rtt / 2);
            self.srtt.insert((x, y), rtt);
        }
    }

    fn lat_of(&self, a: usize, b: usize) -> u64 {
        self.lat_pair.get(&(a, b)).copied().unwrap_or(self.lat)
    }

    fn push(&mut self, at: u64, ev: Ev) {
        self.seq += 1;
        self.q.insert((at, self.seq), ev);
    }

    fn idx(&self, id: &NodeId) -> usize {
        usize::from(id[0]) - 1
    }

    pub fn is_hub(&self, i: usize) -> bool {
        i < self.hubs
    }

    fn net_ok(&self, a: usize, b: usize) -> bool {
        self.nodes[a].up && self.nodes[b].up && !self.cut.contains(&key(a, b))
    }

    /// Whether a frame from `a` to `b` on `route` arrives.
    fn path_ok(&self, a: usize, b: usize, route: &Route) -> bool {
        let session = self.net_ok(a, b) && !self.dead_default.contains(&key(a, b));
        match route {
            Route::Session => {
                if self.is_hub(a) {
                    session
                } else {
                    // A member's transport answers on whichever path works.
                    session || self.any_alt(a, b)
                }
            }
            Route::Direct => self.direct.contains(&key(a, b)) && self.net_ok(a, b),
            Route::Via(x) => {
                let x = self.idx(x);
                self.net_ok(a, x) && self.net_ok(x, b)
            }
        }
    }

    fn any_alt(&self, a: usize, b: usize) -> bool {
        (self.direct.contains(&key(a, b)) && self.net_ok(a, b))
            || (0..self.hubs).any(|x| x != a && x != b && self.net_ok(a, x) && self.net_ok(x, b))
    }

    /// Open a session between `a` (dialer) and `b`, after one latency.
    pub fn connect(&mut self, a: usize, b: usize) {
        self.sessions.insert((a, b));
        let at = self.now + self.lat;
        self.push(at, Ev::SessionUp { a, b });
    }

    /// Every member dials every hub; hubs dial higher-numbered hubs.
    pub fn attach_all(&mut self) {
        for a in 0..self.nodes.len() {
            for b in 0..self.hubs {
                if a > b {
                    self.connect(a, b);
                }
            }
        }
    }

    /// End the session between `a` and `b` on both sides with `code` (as the dialer saw it), after one latency.
    pub fn close_session(&mut self, a: usize, b: usize, code: u64) {
        self.sessions.remove(&(a, b));
        self.sessions.remove(&(b, a));
        let at = self.now + self.lat;
        self.push(at, Ev::SessionDown { to: b, from: a, code });
        self.push(
            at,
            Ev::SessionDown {
                to: a,
                from: b,
                code: 0,
            },
        );
    }

    /// The process dies: no frame, no close.
    pub fn crash(&mut self, i: usize) {
        self.nodes[i].up = false;
    }

    pub fn set_carrier_gone(&mut self, hub: usize, member: usize) {
        let since = self.now;
        self.nodes[hub]
            .h
            .carriers
            .insert(id(member), Carrier::Gone { since, sleep: None });
        self.dead_default.insert(key(hub, member));
        let mid = id(member);
        self.call(
            hub,
            |m, h, now| m.carrier_gone(h, now, &mid),
            |()| Op::CarrierGone { member: mid },
        );
    }

    pub fn set_carrier_open(&mut self, hub: usize, member: usize) {
        self.nodes[hub].h.carriers.insert(id(member), Carrier::Open);
        self.dead_default.remove(&key(hub, member));
        let mid = id(member);
        self.call(
            hub,
            |m, h, now| m.carrier_return(h, now, &mid),
            |()| Op::CarrierReturn { member: mid },
        );
    }

    /// Refresh a node's host-side evidence table: session set, directness.
    fn sync(&mut self, i: usize) {
        let me = i;
        let peers: Vec<usize> = self
            .sessions
            .iter()
            .filter_map(|&(a, b)| {
                if a == me {
                    Some(b)
                } else if b == me {
                    Some(a)
                } else {
                    None
                }
            })
            .collect();
        let mut set = BTreeSet::new();
        for p in peers {
            set.insert(id(p));
            let direct = self.direct.contains(&key(i, p));
            let srtt = self.srtt.get(&(i, p)).copied().unwrap_or(2 * self.lat);
            self.nodes[i]
                .h
                .ev
                .entry(id(p))
                .and_modify(|e| {
                    e.direct = direct;
                    e.srtt = srtt;
                })
                .or_insert(Evidence {
                    last_rx: self.now,
                    srtt,
                    pto: 0,
                    inflight: 0,
                    direct,
                });
        }
        self.nodes[i].h.ev.retain(|k, _| set.contains(k));
        self.nodes[i].h.sessions = set;
    }

    /// Drain a node's outbox into the network and its events and traces into the logs.
    fn flush(&mut self, i: usize) {
        let out = std::mem::take(&mut self.nodes[i].h.out);
        for (peer, route, bytes) in out {
            let j = self.idx(&peer);
            let ty = bytes[4];
            self.sent_types.push((self.now, i, j, ty, route));
            self.frames.push((self.now, i, j, bytes.clone()));
            if let Some(p) = self.drop_once.iter().position(|&(f, t, y)| f == i && t == j && y == ty) {
                self.drop_once.remove(p);
                continue;
            }
            if !self.path_ok(i, j, &route) {
                continue;
            }
            // Hub streams are reliable: a lost packet is retransmitted, so loss shows up as delay, never as a lost frame.
            let mut extra = 0;
            while self.loss_pct > 0 && extra < 20 * self.lat && self.rng.next_u64() % 100 < self.loss_pct {
                extra += 3 * self.lat_of(i, j);
            }
            // A stream delivers in order: a retransmitted frame holds up the ones behind it.
            let at = (self.now + self.lat_of(i, j) + extra).max(self.last_at.get(&(i, j)).copied().unwrap_or(0));
            self.last_at.insert((i, j), at);
            self.push(at, Ev::Deliver { to: j, from: i, bytes });
        }
        while let Some(e) = self.nodes[i].m.poll_event() {
            self.events[i].push((self.now, e));
        }
        while let Some(t) = self.nodes[i].m.poll_trace() {
            self.traces[i].push(t);
        }
    }

    /// Install a recorder. The nodes already started are recorded as `Start` calls, with what they queued.
    pub fn set_recorder(&mut self, rec: Box<dyn Recorder>) {
        self.rec = Some(rec);
        for i in 0..self.nodes.len() {
            let env = self.snap_env(i);
            let (events, traces) = self.take_queues(i);
            let hub = self.nodes[i].is_hub;
            let hubs: Vec<NodeId> = (0..self.hubs).map(id).collect();
            let wall = 1_000_000 + u64::try_from(i).unwrap();
            let call = self.make_call(
                i,
                self.now,
                Op::Start {
                    hub,
                    hubs,
                    wall,
                    floor: 0,
                    ret: "ok",
                },
                env,
                (0, 0, 0),
                (events, traces),
            );
            if let Some(r) = self.rec.as_mut() {
                r.record(call);
            }
        }
    }

    pub fn take_recorder(&mut self) -> Option<Box<dyn Recorder>> {
        self.rec.take()
    }

    fn take_queues(&mut self, i: usize) -> (Vec<Event>, Vec<Trace>) {
        let mut events = Vec::new();
        let mut traces = Vec::new();
        while let Some(e) = self.nodes[i].m.poll_event() {
            events.push(e);
        }
        while let Some(t) = self.nodes[i].m.poll_trace() {
            traces.push(t);
        }
        (events, traces)
    }

    fn snap_env(&self, i: usize) -> EnvSnap {
        let h = &self.nodes[i].h;
        EnvSnap {
            ev: h.ev.iter().map(|(k, v)| (*k, *v)).collect(),
            car: h
                .carriers
                .iter()
                .filter(|(_, c)| **c != Carrier::Unknown)
                .map(|(k, v)| (*k, *v))
                .collect(),
            acc: h.sessions.iter().copied().collect(),
            ver: h.version,
            tk: h.ticket,
            refl: h.reflexive,
            pers: h.persistent,
            sealed: h.sealed,
            failseal: h.fail_seal,
            failunseal: h.fail_unseal,
        }
    }

    fn st_snap(&self, i: usize) -> StSnap {
        let m = &self.nodes[i].m;
        let roster = (0..self.nodes.len())
            .filter_map(|j| m.lease_of(&id(j)).map(|t| (id(j), t)))
            .collect();
        StSnap {
            members: m.members().map(|(k, r)| (*k, *r)).collect(),
            epoch: m.view_epoch(),
            primary: m.primary().copied(),
            inc: m.incarnation(),
            roster,
            seal_failed: m.seal_failed(),
        }
    }

    /// Build the record of a call: the tails of the logs since `marks` (sent, bc, closed), the queues drained.
    fn make_call(
        &mut self,
        i: usize,
        now: u64,
        op: Op,
        env: EnvSnap,
        marks: (usize, usize, usize),
        q: (Vec<Event>, Vec<Trace>),
    ) -> Call {
        let h = &self.nodes[i].h;
        Call {
            node: i,
            now,
            op,
            env,
            sent: h.sent_log[marks.0..].to_vec(),
            bc: h.bc[marks.1..].to_vec(),
            closed: h.closed[marks.2..].to_vec(),
            events: q.0,
            traces: q.1,
            sealed_after: h.sealed,
            st: self.st_snap(i),
        }
    }

    /// One call into node `i`'s machine, with its host synced and flushed afterwards; recorded when a recorder is on.
    /// `op` names the call after it ran (some calls know their result only then).
    fn call<R>(
        &mut self,
        i: usize,
        f: impl FnOnce(&mut Membership, &mut Host, u64) -> R,
        op: impl FnOnce(&R) -> Op,
    ) -> R {
        self.sync(i);
        let now = self.now;
        let recording = self.rec.is_some();
        let env = if recording { Some(self.snap_env(i)) } else { None };
        let marks = {
            let h = &self.nodes[i].h;
            (h.sent_log.len(), h.bc.len(), h.closed.len())
        };
        let (ne, nt) = (self.events[i].len(), self.traces[i].len());
        let Node { m, h, .. } = &mut self.nodes[i];
        let r = f(m, h, now);
        let opv = op(&r);
        self.flush(i);
        if let Some(env) = env {
            let events = self.events[i][ne..].iter().map(|(_, e)| *e).collect();
            let traces = self.traces[i][nt..].to_vec();
            let call = self.make_call(i, now, opv, env, marks, (events, traces));
            if let Some(rc) = self.rec.as_mut() {
                rc.record(call);
            }
        }
        r
    }

    /// Tell hub `hub` that `member`'s carrier closed, without touching the network (recorded).
    pub fn notice_gone(&mut self, hub: usize, member: usize) {
        let mid = id(member);
        self.call(
            hub,
            |m, h, now| m.carrier_gone(h, now, &mid),
            |()| Op::CarrierGone { member: mid },
        );
    }

    /// Revoke the wide id number `k` at node `i` (recorded): 30 zero bytes and `k` as a big-endian 16-bit number.
    pub fn revoke_raw(&mut self, i: usize, k: u16) -> bool {
        let mut mid = [0u8; 32];
        mid[30..].copy_from_slice(&k.to_be_bytes());
        self.call(
            i,
            |m, h, now| m.revoke(h, now, &mid).is_ok(),
            |ok| Op::Revoke { member: mid, ok: *ok },
        )
    }

    /// The node `i` leaves the group (recorded).
    pub fn leave(&mut self, i: usize) {
        self.call(i, |m, h, _| m.leave(h), |()| Op::Leave);
    }

    /// The access-control layer revokes `member` at node `i` (recorded).
    pub fn revoke(&mut self, i: usize, member: usize) -> bool {
        let mid = id(member);
        self.call(
            i,
            |m, h, now| m.revoke(h, now, &mid).is_ok(),
            |ok| Op::Revoke { member: mid, ok: *ok },
        )
    }

    /// The address of node `i` changed (recorded).
    pub fn moved(&mut self, i: usize) {
        self.call(i, |m, _, now| m.address_changed(now), |()| Op::Moved);
    }

    /// Restart node `i` as a new process on the same host store: the sessions and logs of the old life are gone.
    pub fn restart(&mut self, i: usize, wall_ms: u64, floor: u64) -> &'static str {
        let hub_ids: Vec<NodeId> = (0..self.hubs).map(id).collect();
        let is_hub = self.nodes[i].is_hub;
        let old = &self.nodes[i].h;
        let h = Host {
            me: id(i),
            version: old.version,
            ticket: old.ticket,
            reflexive: old.reflexive,
            persistent: old.persistent,
            sealed: old.sealed,
            fail_seal: old.fail_seal,
            fail_unseal: old.fail_unseal,
            ..Host::default()
        };
        self.sessions.retain(|&(a, b)| a != i && b != i);
        let cfg = Config {
            me: id(i),
            is_hub,
            hubs: &hub_ids,
            trace: true,
        };
        let now = self.now;
        self.nodes[i].h = h;
        self.sync(i);
        let env = self.snap_env(i);
        let r = Membership::start(&cfg, &mut self.nodes[i].h, now, wall_ms, floor);
        let ret = match &r {
            Ok(_) => "ok",
            Err(vinc_membership::StartError::TooManyHubs) => "toomany",
            Err(vinc_membership::StartError::NoHubs) => "nohubs",
            Err(vinc_membership::StartError::Incarnation(e)) => match e {
                vinc_membership::incarnation::IncarnationError::Store(_) => "store",
                vinc_membership::incarnation::IncarnationError::Exhausted => "exhausted",
            },
        };
        if let Ok(m) = r {
            self.nodes[i].m = m;
            self.nodes[i].up = true;
        }
        let (events, traces) = self.take_queues(i);
        if self.rec.is_some() {
            let call = self.make_call(
                i,
                now,
                Op::Start {
                    hub: is_hub,
                    hubs: hub_ids,
                    wall: wall_ms,
                    floor,
                    ret,
                },
                env,
                (0, 0, 0),
                (events, traces),
            );
            if let Some(rc) = self.rec.as_mut() {
                rc.record(call);
            }
        }
        ret
    }

    fn process(&mut self, to: usize, from: usize, bytes: &[u8]) {
        if !self.nodes[to].up {
            return;
        }
        let peer = id(from);
        let n = self.call(
            to,
            |m, h, now| m.on_bytes(h, now, &peer, bytes),
            |r| Op::Bytes {
                peer,
                bytes: bytes.to_vec(),
                used: r.as_ref().map_or(0, |n| *n),
                bad: r.is_err(),
            },
        );
        let n = n.expect("frame parses");
        assert_eq!(n, bytes.len(), "whole frame consumed");
    }

    /// Deliver bytes that need not be a whole frame to `to` as if `from` sent them, now; returns what `on_bytes` said.
    pub fn inject_bytes(&mut self, to: usize, from: usize, bytes: &[u8]) -> Result<usize, vinc_membership::FrameError> {
        let peer = id(from);
        self.call(
            to,
            |m, h, now| m.on_bytes(h, now, &peer, bytes),
            |r| Op::Bytes {
                peer,
                bytes: bytes.to_vec(),
                used: r.as_ref().map_or(0, |n| *n),
                bad: r.is_err(),
            },
        )
    }

    fn step_event(&mut self, ev: Ev) {
        match ev {
            Ev::Deliver { to, from, bytes } => {
                if !self.nodes[to].up || (!self.sessions.contains(&(to, from)) && !self.sessions.contains(&(from, to)))
                {
                    return;
                }
                // The transport sees the packet at once; the application sees it after its processing delay.
                if let Some(e) = self.nodes[to].h.ev.get_mut(&id(from)) {
                    e.last_rx = self.now;
                }
                let at = self.now + self.lat_of(to, from);
                self.push(at, Ev::Ack { to: from, from: to });
                let at = self.now + self.nodes[to].cpu;
                self.push(at, Ev::Process { to, from, bytes });
            }
            Ev::Process { to, from, bytes } => self.process(to, from, &bytes),
            Ev::Ack { to, from } => {
                if self.nodes[to].up
                    && self.nodes[from].up
                    && self.path_ok(from, to, &Route::Session)
                    && let Some(e) = self.nodes[to].h.ev.get_mut(&id(from))
                {
                    e.last_rx = self.now;
                }
            }
            Ev::SessionUp { a, b } => {
                if !self.nodes[a].up || !self.nodes[b].up || self.cut.contains(&key(a, b)) {
                    self.sessions.remove(&(a, b));
                    return;
                }
                self.sync(a);
                self.sync(b);
                let (ia, ib) = (id(a), id(b));
                self.call(
                    b,
                    |m, h, now| m.session_up(h, now, &ia, true),
                    |()| Op::Up {
                        peer: ia,
                        incoming: true,
                    },
                );
                self.call(
                    a,
                    |m, h, now| m.session_up(h, now, &ib, false),
                    |()| Op::Up {
                        peer: ib,
                        incoming: false,
                    },
                );
            }
            Ev::SessionDown { to, from, code } => {
                if !self.nodes[to].up {
                    return;
                }
                let pf = id(from);
                self.call(
                    to,
                    |m, h, now| m.session_down(h, now, &pf, code),
                    |()| Op::Down { peer: pf, code },
                );
            }
        }
    }

    fn timers(&mut self) {
        for i in 0..self.nodes.len() {
            if self.nodes[i].up && self.nodes[i].m.poll_timeout() <= self.now {
                self.call(i, |m, h, now| m.on_timeout(h, now), |()| Op::Timeout);
            }
        }
    }

    fn keepalives(&mut self) {
        if self.keepalive == 0 || self.now < self.next_ka {
            return;
        }
        self.next_ka = self.now + self.keepalive;
        let pairs: Vec<(usize, usize)> = self.sessions.iter().copied().collect();
        for (a, b) in pairs {
            if self.path_ok(a, b, &Route::Session) && self.path_ok(b, a, &Route::Session) {
                let now = self.now;
                if let Some(e) = self.nodes[a].h.ev.get_mut(&id(b)) {
                    e.last_rx = now;
                }
                if let Some(e) = self.nodes[b].h.ev.get_mut(&id(a)) {
                    e.last_rx = now;
                }
            }
        }
    }

    /// Skip `dur` of time without running anything: a suspension. Queued events become due all at once.
    pub fn jump(&mut self, dur: u64) {
        self.now += dur;
    }

    /// Advance time by `dur` in 50 ms steps.
    pub fn run(&mut self, dur: u64) {
        let end = self.now + dur;
        while self.now < end {
            self.now += 50 * MS;
            while let Some((&k, _)) = self.q.first_key_value() {
                if k.0 > self.now {
                    break;
                }
                let ev = self.q.remove(&k).unwrap();
                self.step_event(ev);
            }
            self.keepalives();
            self.timers();
        }
    }

    /// Run until `cond` holds or `limit` passes; returns whether it held.
    pub fn run_until(&mut self, limit: u64, mut cond: impl FnMut(&Self) -> bool) -> bool {
        let end = self.now + limit;
        while self.now < end {
            if cond(self) {
                return true;
            }
            self.run(50 * MS);
        }
        cond(self)
    }

    pub fn members_of(&self, i: usize) -> Vec<NodeId> {
        self.nodes[i].m.members().map(|(m, _)| *m).collect()
    }

    pub fn has(&self, i: usize, j: usize) -> bool {
        self.nodes[i].m.members().any(|(m, _)| *m == id(j))
    }

    pub fn count_events(&self, i: usize, f: impl Fn(&Event) -> bool) -> usize {
        self.events[i].iter().filter(|(_, e)| f(e)).count()
    }

    pub fn first_event_time(&self, i: usize, f: impl Fn(&Event) -> bool) -> Option<u64> {
        self.events[i].iter().find(|(_, e)| f(e)).map(|(t, _)| *t)
    }

    /// A call into a node's machine with its host synced, then flushed.
    pub fn with<R>(&mut self, i: usize, f: impl FnOnce(&mut Membership, &mut Host, u64) -> R) -> R {
        assert!(
            self.rec.is_none(),
            "a call through `with` would be missing from the recorded trace"
        );
        self.sync(i);
        let now = self.now;
        let Node { m, h, .. } = &mut self.nodes[i];
        let r = f(m, h, now);
        self.flush(i);
        r
    }

    /// Hand a frame to a node as if `from` had sent it, now.
    pub fn inject(&mut self, to: usize, from: usize, f: &Frame<'_>) {
        let mut buf = [0u8; 8192];
        let bytes = f.encode(&mut buf).unwrap().to_vec();
        self.process(to, from, &bytes);
    }
}

pub const LEAVE: u64 = LEAVE_CODE;
