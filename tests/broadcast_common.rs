//! A small deterministic world for the broadcast tests: nodes with real signing keys, a zero-latency network whose
//! links can be cut, a host per node that records what the machine asked of it, and a virtual clock.
//!
//! Included by the `broadcast_*` test targets with `#[path]`; not a test target itself.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::type_complexity,
    clippy::cast_possible_truncation
)]

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use pinc_broadcast::{Config, Event, Host, Lane, Topics};
use pinc_crypto::{IdentityAlg, Keypair};
use pinc_membership::NodeId;

pub const SEC: u64 = 1_000_000_000;
pub const WALL0: u64 = 1_700_000_000_000;

/// The id key of node `i`.
pub fn map_key(i: usize) -> pinc_broadcast::IdKey {
    pinc_tests::id_key(0x5eed + i as u64)
}

pub const ALGS: [IdentityAlg; 4] = [
    IdentityAlg::Ed25519,
    IdentityAlg::EcdsaP256,
    IdentityAlg::MlDsa65,
    IdentityAlg::Hybrid,
];

pub fn keypair(alg: IdentityAlg, tag: u8) -> Keypair {
    Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap()
}

/// What the application heard, owned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Ev {
    Msg {
        topic: Vec<u8>,
        origin: NodeId,
        mid: [u8; 8],
        body: Vec<u8>,
    },
    Acked([u8; 8]),
    GaveUp([u8; 8]),
    Room,
    Repaired {
        topic: Vec<u8>,
        mid: [u8; 8],
    },
    Fallback {
        topic: Vec<u8>,
        mid: [u8; 8],
        to: NodeId,
    },
    Restored {
        hub: NodeId,
        topic: Vec<u8>,
    },
    Subscribed {
        hub: NodeId,
        topic: Vec<u8>,
    },
    HubFull {
        hub: NodeId,
        topic: Vec<u8>,
    },
    Acp {
        id: u32,
        origin: NodeId,
        topic: Vec<u8>,
    },
    ReachRefused(NodeId),
    ReachClosed,
    ReachOpened,
}

#[derive(Debug, Clone)]
pub struct Out {
    pub to: NodeId,
    pub lane: Lane,
    pub member: bool,
    pub bytes: Vec<u8>,
}

#[derive(Debug, Default)]
pub struct NodeHost {
    pub out: Vec<Out>,
    pub events: Vec<Ev>,
    pub reach: BTreeSet<NodeId>,
    pub hubs: BTreeSet<NodeId>,
    pub view: BTreeSet<NodeId>,
    pub wall: u64,
    /// How far this node's wall clock runs ahead of the true one, in milliseconds (negative: behind).
    pub skew_ms: i64,
    /// Peers whose stream has no room: a frame for one is refused, and the host says it is a full stream.
    pub full: BTreeSet<NodeId>,
    /// How many more frames a peer's stream takes before it is full, for a peer listed here.
    pub room: BTreeMap<NodeId, usize>,
}

impl NodeHost {
    /// Set the wall clock for a call at monotonic time `now`.
    pub fn tick(&mut self, now: u64) {
        self.wall = WALL0.saturating_add_signed(self.skew_ms + i64::try_from(now / 1_000_000).unwrap());
    }
}

impl Host for NodeHost {
    fn send(&mut self, peer: &NodeId, lane: Lane, frame: &[u8]) -> bool {
        if !self.reach.contains(peer) || self.full.contains(peer) {
            return false;
        }
        if let Some(room) = self.room.get_mut(peer) {
            if *room == 0 {
                return false;
            }
            *room -= 1;
        }
        self.out.push(Out {
            to: *peer,
            lane,
            member: false,
            bytes: frame.to_vec(),
        });
        true
    }

    fn backlogged(&self, peer: &NodeId, _len: usize) -> bool {
        self.reach.contains(peer) && (self.full.contains(peer) || self.room.get(peer) == Some(&0))
    }

    fn send_member(&mut self, peer: &NodeId, frame: &[u8]) -> bool {
        if !self.reach.contains(peer) {
            return false;
        }
        self.out.push(Out {
            to: *peer,
            lane: Lane::Main,
            member: true,
            bytes: frame.to_vec(),
        });
        true
    }

    fn hub_up(&self, hub: &NodeId) -> bool {
        self.hubs.contains(hub) && self.reach.contains(hub)
    }

    fn in_view(&self, member: &NodeId) -> bool {
        self.view.contains(member)
    }

    fn wall_ms(&self) -> u64 {
        self.wall
    }

    fn event(&mut self, event: Event<'_>) {
        self.events.push(match event {
            Event::Message {
                topic,
                origin,
                mid,
                body,
                ..
            } => Ev::Msg {
                topic: topic.to_vec(),
                origin: *origin,
                mid,
                body: body.to_vec(),
            },
            Event::PublishAcked { mid } => Ev::Acked(mid),
            Event::PublishGaveUp { mid } => Ev::GaveUp(mid),
            Event::PublishRoom => Ev::Room,
            Event::GapRepaired { topic, mid } => Ev::Repaired {
                topic: topic.to_vec(),
                mid,
            },
            Event::Fallback { topic, mid, to } => Ev::Fallback {
                topic: topic.to_vec(),
                mid,
                to: *to,
            },
            Event::Restored { hub, topic } => Ev::Restored {
                hub: *hub,
                topic: topic.to_vec(),
            },
            Event::Subscribed { hub, topic } => Ev::Subscribed {
                hub: *hub,
                topic: topic.to_vec(),
            },
            Event::HubFull { hub, topic } => Ev::HubFull {
                hub: *hub,
                topic: topic.to_vec(),
            },
            Event::AcpCheck { id, origin, topic } => Ev::Acp {
                id,
                origin: *origin,
                topic: topic.to_vec(),
            },
            Event::ReachRefused { origin } => Ev::ReachRefused(*origin),
            Event::ReachClosed => Ev::ReachClosed,
            Event::ReachOpened => Ev::ReachOpened,
        });
    }
}

struct Other<'a> {
    ty: u8,
    topic: &'a [u8],
    rest: &'a [u8],
}

pub struct Node {
    pub id: NodeId,
    pub t: Topics,
    pub h: NodeHost,
    pub hub: bool,
    /// Answer access checks at once with this verdict.
    pub auto_acp: Option<bool>,
}

pub struct Net {
    pub now: u64,
    pub algs: Vec<IdentityAlg>,
    pub limits: pinc_broadcast::Limits,
    pub hubs: usize,
    /// Whether the nodes queue trace records.
    pub trace: bool,
    pub nodes: Vec<Node>,
    queue: VecDeque<(usize, usize, bool, Vec<u8>)>,
    /// Look at (and maybe alter or drop) every frame in flight: `(from, to, &mut bytes) -> deliver?`.
    pub filter: Option<Box<dyn FnMut(usize, usize, &mut Vec<u8>) -> bool>>,
    /// Every frame delivered, as `(time, from, to, type, member session?)`.
    pub log: Vec<(u64, usize, usize, u8, bool)>,
    /// Every frame handed to a host, as `(from, to, type, lane)`.
    pub lanes: Vec<(usize, usize, u8, Lane)>,
}

impl Net {
    /// `hubs` hubs then `members` members, all with `alg` keys, fully connected, started at `start`. Every member's
    /// primary is hub 0 (when there are hubs).
    pub fn new(alg: IdentityAlg, hubs: usize, members: usize, start: u64) -> Self {
        let mut net = Self::with_algs(&vec![alg; hubs + members], hubs, start);
        for i in hubs..hubs + members {
            net.attach(i);
        }
        net
    }

    /// Attach member `i` to every hub: each hub sends it the FLOOR frame, as membership does on a new attachment.
    pub fn attach(&mut self, i: usize) {
        let hubs: Vec<usize> = (0..self.nodes.len()).filter(|j| self.nodes[*j].hub).collect();
        for hub in hubs {
            self.attach_to(i, hub);
        }
    }

    /// Attach member `i` to one hub: the hub sends it the FLOOR frame.
    pub fn attach_to(&mut self, i: usize, hub: usize) {
        let me = self.id(i);
        if self.nodes[hub].h.reach.contains(&me) {
            let mut body = [0u8; 4096];
            let n = self.nodes[hub].t.floor(&me, &mut body);
            let mut f = Vec::new();
            f.extend_from_slice(&u32::try_from(2 + n).unwrap().to_be_bytes());
            f.extend_from_slice(&[ty::FLOOR, 0]);
            f.extend_from_slice(&body[..n]);
            self.nodes[hub].h.out.push(Out {
                to: me,
                lane: Lane::Main,
                member: false,
                bytes: f,
            });
        }
        self.pump();
    }

    pub fn with_algs(algs: &[IdentityAlg], hubs: usize, start: u64) -> Self {
        Self::with_limits(algs, hubs, start, pinc_broadcast::Limits::default())
    }

    pub fn with_limits(algs: &[IdentityAlg], hubs: usize, start: u64, limits: pinc_broadcast::Limits) -> Self {
        Self::with_trace(algs, hubs, start, limits, true)
    }

    /// As [`Net::with_limits`], with the trace queue of every node on or off; a restart keeps the choice.
    pub fn with_trace(
        algs: &[IdentityAlg],
        hubs: usize,
        start: u64,
        limits: pinc_broadcast::Limits,
        trace: bool,
    ) -> Self {
        let keys: Vec<Keypair> = algs
            .iter()
            .enumerate()
            .map(|(i, a)| keypair(*a, u8::try_from(i + 1).unwrap()))
            .collect();
        let ids: Vec<NodeId> = keys.iter().map(|k| k.node_id().bytes).collect();
        let hub_ids: Vec<NodeId> = ids[..hubs].to_vec();
        let mut nodes = Vec::new();
        for (i, k) in keys.into_iter().enumerate() {
            let cfg = Config {
                me: ids[i],
                is_hub: i < hubs,
                hubs: &hub_ids,
                incarnation: (WALL0 + 1) << 16,
                trace,
                limits,
                map_keys: map_key(i),
            };
            let t = Topics::start(&cfg, Box::new(k), start, WALL0 + start / 1_000_000).unwrap();
            let h = NodeHost {
                reach: ids.iter().copied().filter(|x| *x != ids[i]).collect(),
                hubs: hub_ids.iter().copied().collect(),
                view: ids.iter().copied().filter(|x| *x != ids[i]).collect(),
                ..NodeHost::default()
            };
            nodes.push(Node {
                id: ids[i],
                t,
                h,
                hub: i < hubs,
                auto_acp: Some(true),
            });
        }
        let mut net = Self {
            now: start,
            algs: algs.to_vec(),
            trace,
            limits,
            hubs,
            nodes,
            queue: VecDeque::new(),
            filter: None,
            log: Vec::new(),
            lanes: Vec::new(),
        };
        if hubs > 0 {
            for i in hubs..net.nodes.len() {
                net.set_primary(i, 0);
            }
        }
        net
    }

    /// Replace node `i` by a fresh life of the same identity started at `at`: empty tables, a newer incarnation.
    pub fn restart(&mut self, i: usize, at: u64) {
        self.run_until(at);
        let ids: Vec<NodeId> = self.nodes.iter().map(|n| n.id).collect();
        let hub_ids: Vec<NodeId> = ids[..self.hubs].to_vec();
        let cfg = Config {
            me: ids[i],
            is_hub: i < self.hubs,
            hubs: &hub_ids,
            incarnation: ((WALL0 + at / 1_000_000 + 1) << 16) | 1,
            trace: self.trace,
            limits: self.limits,
            map_keys: map_key(i),
        };
        let skew = self.nodes[i].h.skew_ms;
        let wall = WALL0.saturating_add_signed(skew + i64::try_from(at / 1_000_000).unwrap());
        let k = keypair(self.algs[i], u8::try_from(i + 1).unwrap());
        self.nodes[i].t = Topics::start(&cfg, Box::new(k), at, wall).unwrap();
        self.nodes[i].h.events.clear();
        self.nodes[i].h.out.clear();
        // The hubs saw the old session close: they forget its subscriptions.
        let me = ids[i];
        for hub in 0..self.hubs {
            let n = &mut self.nodes[hub];
            n.t.release(&mut n.h, &me);
        }
    }

    pub fn id(&self, i: usize) -> NodeId {
        self.nodes[i].id
    }

    pub fn set_primary(&mut self, member: usize, hub: usize) {
        let (old, new) = (self.nodes[member].t.primary().copied(), self.id(hub));
        self.call(member, |t, h, now| t.primary_changed(h, now, old.as_ref(), &new));
    }

    fn call<R>(&mut self, i: usize, f: impl FnOnce(&mut Topics, &mut NodeHost, u64) -> R) -> R {
        let now = self.now;
        let n = &mut self.nodes[i];
        n.h.tick(now);
        let r = f(&mut n.t, &mut n.h, now);
        self.pump();
        r
    }

    /// Cut or heal the link between two nodes (both directions).
    pub fn link(&mut self, a: usize, b: usize, up: bool) {
        let (ia, ib) = (self.id(a), self.id(b));
        for (x, y) in [(a, ib), (b, ia)] {
            if up {
                self.nodes[x].h.reach.insert(y);
            } else {
                self.nodes[x].h.reach.remove(&y);
            }
        }
    }

    /// Cut a node off from every hub.
    pub fn cut_from_hubs(&mut self, i: usize, up: bool) {
        let hubs: Vec<usize> = (0..self.nodes.len())
            .filter(|j| self.nodes[*j].hub && *j != i)
            .collect();
        for j in hubs {
            self.link(i, j, up);
        }
    }

    fn index_of(&self, id: &NodeId) -> usize {
        self.nodes.iter().position(|n| n.id == *id).unwrap()
    }

    /// Carry every frame the nodes queued, and answer access checks, until the network is quiet.
    pub fn pump(&mut self) {
        loop {
            for i in 0..self.nodes.len() {
                let outs = std::mem::take(&mut self.nodes[i].h.out);
                for o in outs {
                    let to = self.index_of(&o.to);
                    self.lanes.push((i, to, o.bytes.get(4).copied().unwrap_or(0), o.lane));
                    self.queue.push_back((i, to, o.member, o.bytes));
                }
            }
            let Some((from, to, member, mut bytes)) = self.queue.pop_front() else {
                let mut asked = false;
                for i in 0..self.nodes.len() {
                    let Some(allow) = self.nodes[i].auto_acp else { continue };
                    let evs = std::mem::take(&mut self.nodes[i].h.events);
                    let (acp, rest): (Vec<Ev>, Vec<Ev>) = evs.into_iter().partition(|e| matches!(e, Ev::Acp { .. }));
                    self.nodes[i].h.events = rest;
                    for e in acp {
                        if let Ev::Acp { id, .. } = e {
                            let now = self.now;
                            let n = &mut self.nodes[i];
                            n.t.acp_answer(&mut n.h, now, id, allow);
                            asked = true;
                        }
                    }
                }
                if asked {
                    continue;
                }
                return;
            };
            if let Some(f) = self.filter.as_mut()
                && !f(from, to, &mut bytes)
            {
                continue;
            }
            let (now, fid) = (self.now, self.nodes[from].id);
            // The frame is parsed here, not by membership's reader, whose frame cap is below the sizes some tests use.
            let (Some(&fty), Some(&tl)) = (bytes.get(4), bytes.get(5)) else {
                continue;
            };
            let tl = usize::from(tl);
            let (Some(topic), Some(rest)) = (bytes.get(6..6 + tl), bytes.get(6 + tl..)) else {
                continue;
            };
            let o = Other { ty: fty, topic, rest };
            self.log.push((now, from, to, o.ty, member));
            let n = &mut self.nodes[to];
            n.h.tick(now);
            n.t.frame(&mut n.h, now, &fid, o.ty, o.topic, o.rest);
        }
    }

    /// Run the timers and the network up to `t`.
    pub fn run_until(&mut self, t: u64) {
        loop {
            self.pump();
            let next = self.nodes.iter().filter_map(|n| n.t.poll_timeout()).min();
            match next {
                Some(x) if x <= t => {
                    self.now = self.now.max(x);
                    let now = self.now;
                    for i in 0..self.nodes.len() {
                        let n = &mut self.nodes[i];
                        if n.t.poll_timeout().is_some_and(|x| x <= now) {
                            n.h.tick(now);
                            n.t.on_timer(&mut n.h, now);
                        }
                    }
                }
                _ => break,
            }
        }
        self.now = self.now.max(t);
        self.pump();
    }

    pub fn advance(&mut self, d: u64) {
        let t = self.now + d;
        self.run_until(t);
    }

    pub fn subscribe(&mut self, i: usize, topic: &[u8]) {
        self.call(i, |t, h, now| t.subscribe(h, now, topic).unwrap());
    }

    pub fn unsubscribe(&mut self, i: usize, topic: &[u8]) {
        self.call(i, |t, h, _| t.unsubscribe(h, topic));
    }

    pub fn publish(&mut self, i: usize, topic: &[u8], body: &[u8]) -> [u8; 8] {
        self.call(i, |t, h, now| t.publish(h, now, topic, body).unwrap())
    }

    /// The message ids node `i` delivered, in order.
    pub fn delivered(&self, i: usize) -> Vec<[u8; 8]> {
        self.nodes[i]
            .h
            .events
            .iter()
            .filter_map(|e| if let Ev::Msg { mid, .. } = e { Some(*mid) } else { None })
            .collect()
    }

    pub fn bodies(&self, i: usize) -> Vec<Vec<u8>> {
        self.nodes[i]
            .h
            .events
            .iter()
            .filter_map(|e| {
                if let Ev::Msg { body, .. } = e {
                    Some(body.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    pub fn events(&self, i: usize) -> &[Ev] {
        &self.nodes[i].h.events
    }

    /// Whether any event node `i` received names `topic`: a subscribe that ended anywhere, a message of it, a repair,
    /// a fallback or a restore. The hub's refusal notice of #695/#738 names the topic too, so a hub that cannot hold
    /// a subscription is told about through this, whatever event carries the telling.
    pub fn told_about(&self, i: usize, topic: &[u8]) -> bool {
        self.events(i).iter().any(|e| match e {
            Ev::Msg { topic: t, .. }
            | Ev::Repaired { topic: t, .. }
            | Ev::Fallback { topic: t, .. }
            | Ev::Restored { topic: t, .. }
            | Ev::Subscribed { topic: t, .. }
            | Ev::HubFull { topic: t, .. }
            | Ev::Acp { topic: t, .. } => t == topic,
            _ => false,
        })
    }

    /// The topics node `i` was told `Subscribed` about.
    pub fn subscribed(&self, i: usize) -> Vec<Vec<u8>> {
        self.events(i)
            .iter()
            .filter_map(|e| {
                if let Ev::Subscribed { topic, .. } = e {
                    Some(topic.clone())
                } else {
                    None
                }
            })
            .collect()
    }

    /// How many frames of type `ty` went over the wire so far.
    pub fn count(&self, ty: u8) -> usize {
        self.log.iter().filter(|(_, _, _, t, _)| *t == ty).count()
    }

    pub fn count_between(&self, from: usize, to: usize, ty: u8) -> usize {
        self.log
            .iter()
            .filter(|(_, f, t, y, _)| *f == from && *t == to && *y == ty)
            .count()
    }
}

pub use pinc_broadcast::wire::ty;
