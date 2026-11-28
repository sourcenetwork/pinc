//! `pinc-broadcast`: a world of hubs and members driven by a random schedule, with an adversarial network.
//!
//! Where the expected behaviour comes from: the crate documentation of `pinc_broadcast`: "A subscriber ... delivers
//! each message at most once (ids are remembered for 600 s)", "Invariants: all tables are bounded; no input panics;
//! the same inputs produce the same outputs; a message is delivered only after its signature over the exact body
//! verified", and `Event::Message`: "A message was delivered, once." The doc of `Host::send` says a lost frame is
//! covered by the repair paths, so a network that loses, delays, reorders or repeats frames is a valid input: a peer
//! that sends a frame twice is an authenticated peer sending bytes, and a lost frame is what a refused `send` is.
//!
//! The existing scenario tests (`tests/broadcast_*.rs`) run fixed schedules on a zero-latency FIFO network. Here the
//! schedule is generated: publishes and subscriptions on every node, primary changes, session cuts (held or
//! released), heals with the FLOOR frame membership sends on an attachment, member restarts, timers, and a network
//! that delivers the frames of one link at a time, drops one, or delivers again a frame sent before.
//!
//! Checked after every step: no panic; every delivered message is one an origin published, with its topic and body;
//! no node delivers a message id twice in one life (each life here is shorter than the 600 s the ids are
//! remembered); the frame storm any step starts dies down within a bound.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use ephyra::prelude::*;
use pinc_broadcast::{Config, Event, Host, IdKey, Lane, Limits, Topics};
use pinc_crypto::{IdentityAlg, Keypair};
use pinc_membership::NodeId;

const SEC: u64 = 1_000_000_000;
const WALL0: u64 = 1_700_000_000_000;
const HUBS: usize = 2;
const NODES: usize = 5;
const TOPICS: [&[u8]; 3] = [b"t0", b"t1", b"t2"];
/// The frames one step may carry before the world counts it as a storm that does not die down.
const STORM: usize = 200_000;
/// A life longer than this may deliver an id again (the dedupe set forgets after 600 s).
const LIFE_MAX: u64 = 590 * SEC;
/// The ty of the FLOOR frame (the membership hub stream type).
const FLOOR: u8 = pinc_broadcast::wire::ty::FLOOR;

static SECRETS: [u64; 7] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xff51_afd7_ed55_8ccd,
    0xc4ce_b9fe_1a85_ec53,
];

fn alg_of(i: usize) -> IdentityAlg {
    if i == NODES - 1 { IdentityAlg::EcdsaP256 } else { IdentityAlg::Ed25519 }
}

fn keypair(i: usize) -> Keypair {
    let alg = alg_of(i);
    Keypair::from_seed(alg, &vec![u8::try_from(i + 1).unwrap_or(1); alg.seed_len()]).expect("a seed of the right length")
}

#[derive(Debug, Clone)]
enum Ev {
    Msg { topic: Vec<u8>, origin: NodeId, mid: [u8; 8], body: Vec<u8> },
    Acp(u32),
}

#[derive(Debug, Default)]
struct H {
    out: Vec<(NodeId, bool, Vec<u8>)>,
    events: Vec<Ev>,
    reach: BTreeSet<NodeId>,
    hubs: BTreeSet<NodeId>,
    view: BTreeSet<NodeId>,
    wall: u64,
    /// Peers whose stream has no room now: a frame is refused and `backlogged` says so.
    full: BTreeSet<NodeId>,
}

impl Host for H {
    fn send(&mut self, peer: &NodeId, _lane: Lane, frame: &[u8]) -> bool {
        if !self.reach.contains(peer) || self.full.contains(peer) {
            return false;
        }
        self.out.push((*peer, false, frame.to_vec()));
        true
    }

    fn send_member(&mut self, peer: &NodeId, frame: &[u8]) -> bool {
        if !self.reach.contains(peer) {
            return false;
        }
        self.out.push((*peer, true, frame.to_vec()));
        true
    }

    fn backlogged(&self, peer: &NodeId, _len: usize) -> bool {
        self.reach.contains(peer) && self.full.contains(peer)
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
        match event {
            Event::Message { topic, origin, mid, body, .. } => self.events.push(Ev::Msg {
                topic: topic.to_vec(),
                origin: *origin,
                mid,
                body: body.to_vec(),
            }),
            Event::AcpCheck { id, .. } => self.events.push(Ev::Acp(id)),
            _ => {},
        }
    }
}

struct Node {
    t: Topics,
    h: H,
    born: u64,
    life: u64,
    subs: BTreeSet<usize>,
    delivered: BTreeSet<[u8; 8]>,
    /// Every id delivered in this life, however long it is.
    got: BTreeSet<[u8; 8]>,
    /// The highest wall time (ms) of a FLOOR frame a hub altered, laid out exactly as the encoder writes it, and sent
    /// to this member within the floor wait of this life (0: none).
    forged_floor: u64,
}

struct World {
    now: u64,
    ids: Vec<NodeId>,
    nodes: Vec<Node>,
    links: BTreeMap<(usize, usize), VecDeque<Vec<u8>>>,
    sent: BTreeMap<(usize, usize), Vec<Vec<u8>>>,
    published: BTreeMap<[u8; 8], (NodeId, Vec<u8>, Vec<u8>)>,
    up: BTreeSet<(usize, usize)>,
    carried: usize,
    tag: u32,
    limits: Limits,
    /// Messages delivered so far, over every node: a schedule that delivers nothing checks nothing.
    deliveries: usize,
    restarted_deliveries: usize,
    /// The wall time (ms) at which `calm` published the fresh messages.
    fresh_wall: u64,
}

/// The floor wall time (ms) of a frame laid out exactly as `Topics::floor` writes a FLOOR body behind an empty topic
/// (`floor12 hist1 [1 n (origin8 ts12)*n | 0]`, at most `ORIGIN_MAX` entries in ascending order, nothing after), or
/// `None` for any other frame. Read past the length prefix, as `World::deliver` reads a frame.
fn encoder_floor_wall(bytes: &[u8]) -> Option<u64> {
    let (&FLOOR, &0) = (bytes.get(4)?, bytes.get(5)?) else { return None };
    let rest = bytes.get(6..)?;
    let (ts, tail) = (rest.get(..12)?, rest.get(12..)?);
    let well_formed = match tail {
        [0 | 1, 0] => true,
        [0 | 1, 1, n, e @ ..] if usize::from(*n) <= pinc_broadcast::consts::ORIGIN_MAX && e.len() == usize::from(*n) * 20 => {
            e.chunks(20).zip(e.chunks(20).skip(1)).all(|(x, y)| x[..8] < y[..8])
        },
        _ => false,
    };
    well_formed.then(|| u64::from_be_bytes(ts[..8].try_into().unwrap_or([0; 8])))
}

/// The small limits: a log ring that holds one largest message (so a few small ones), two topics of three, two
/// subscribers a topic, and an adjacency table of two records.
fn small_limits() -> Limits {
    Limits {
        max_body: 64,
        log_bytes: 64 + pinc_broadcast::wire::MAX_HEAD,
        max_topics: 2,
        max_subscribers: 2,
        reach_bytes: 2 * pinc_broadcast::consts::REACH_RECORD_BASE + 200,
    }
}

fn start(i: usize, ids: &[NodeId], now: u64, life: u64, limits: Limits) -> Topics {
    let cfg = Config {
        me: ids[i],
        is_hub: i < HUBS,
        hubs: &ids[..HUBS],
        incarnation: ((WALL0 + now / 1_000_000 + 1) << 16) | life,
        trace: false,
        limits,
        map_keys: IdKey::new(0x5eed + i as u64, &SECRETS).expect("a usable key"),
    };
    Topics::start(&cfg, Box::new(keypair(i)), now, WALL0 + now / 1_000_000).expect("a valid configuration")
}

impl World {
    fn new(limits: Limits) -> Self {
        let ids: Vec<NodeId> = (0..NODES).map(|i| keypair(i).node_id().bytes).collect();
        let nodes = (0..NODES)
            .map(|i| Node {
                t: start(i, &ids, 0, 0, limits),
                h: H {
                    reach: ids.iter().copied().filter(|x| *x != ids[i]).collect(),
                    hubs: ids[..HUBS].iter().copied().collect(),
                    view: ids.iter().copied().filter(|x| *x != ids[i]).collect(),
                    wall: WALL0,
                    ..H::default()
                },
                born: 0,
                life: 0,
                subs: BTreeSet::new(),
                delivered: BTreeSet::new(),
                got: BTreeSet::new(),
                forged_floor: 0,
            })
            .collect();
        let up = (0..NODES).flat_map(|a| (0..NODES).map(move |b| (a, b))).filter(|(a, b)| a != b).collect();
        let mut w = Self {
            now: 0,
            ids,
            nodes,
            links: BTreeMap::new(),
            sent: BTreeMap::new(),
            published: BTreeMap::new(),
            up,
            carried: 0,
            tag: 0,
            limits,
            deliveries: 0,
            restarted_deliveries: 0,
            fresh_wall: 0,
        };
        for m in HUBS..NODES {
            w.attach(m, None);
        }
        w.settle();
        w
    }

    fn index(&self, id: &NodeId) -> usize {
        self.ids.iter().position(|x| x == id).unwrap_or(0)
    }

    /// Move node `i`'s output onto the links, check its events and answer its access checks, until it is quiet.
    fn flush(&mut self, i: usize) {
        for _ in 0..1000 {
            let out = std::mem::take(&mut self.nodes[i].h.out);
            for (to, _member, bytes) in out {
                let j = self.index(&to);
                self.sent.entry((i, j)).or_default().push(bytes.clone());
                self.links.entry((i, j)).or_default().push_back(bytes);
            }
            let events = std::mem::take(&mut self.nodes[i].h.events);
            let mut asked = false;
            for e in events {
                match e {
                    Ev::Msg { topic, origin, mid, body } => self.check_delivery(i, &topic, &origin, mid, &body),
                    Ev::Acp(id) => {
                        let n = &mut self.nodes[i];
                        n.t.acp_answer(&mut n.h, self.now, id, true);
                        asked = true;
                    },
                }
            }
            if !asked {
                return;
            }
        }
        panic!("node {i} keeps asking access checks");
    }

    fn check_delivery(&mut self, i: usize, topic: &[u8], origin: &NodeId, mid: [u8; 8], body: &[u8]) {
        let p = self.published.get(&mid);
        assert!(p.is_some(), "node {i} delivered a message id {mid:?} no origin published");
        let Some((o, t, b)) = p else { return };
        assert_eq!((o, &t[..], &b[..]), (origin, topic, body), "node {i} delivered {mid:?} with other fields than published");
        self.deliveries += 1;
        let n = &mut self.nodes[i];
        n.got.insert(mid);
        if n.life > 0 {
            self.restarted_deliveries += 1;
        }
        if self.now.saturating_sub(n.born) < LIFE_MAX {
            assert!(n.delivered.insert(mid), "node {i} delivered message {mid:?} twice in one life (life {})", n.life);
        }
    }

    fn tick(&mut self, i: usize) {
        self.nodes[i].h.wall = WALL0 + self.now / 1_000_000;
    }

    /// Carry one frame of link `(a, b)`.
    fn carry(&mut self, a: usize, b: usize) {
        let Some(bytes) = self.links.get_mut(&(a, b)).and_then(VecDeque::pop_front) else { return };
        self.deliver(a, b, &bytes);
    }

    fn deliver(&mut self, a: usize, b: usize, bytes: &[u8]) {
        self.carried += 1;
        assert!(self.carried < STORM, "the frames of one step do not die down");
        let (Some(&ty), Some(&tl)) = (bytes.get(4), bytes.get(5)) else { return };
        let tl = usize::from(tl);
        let (Some(topic), Some(rest)) = (bytes.get(6..6 + tl), bytes.get(6 + tl..)) else { return };
        self.tick(b);
        let from = self.ids[a];
        let now = self.now;
        let n = &mut self.nodes[b];
        n.t.frame(&mut n.h, now, &from, ty, topic, rest);
        self.flush(b);
    }

    /// Carry every frame in flight, one per link in turn, until the network is quiet.
    fn settle(&mut self) {
        loop {
            let busy: Vec<(usize, usize)> =
                self.links.iter().filter(|(_, q)| !q.is_empty()).map(|(k, _)| *k).collect();
            if busy.is_empty() {
                return;
            }
            for (a, b) in busy {
                self.carry(a, b);
            }
        }
    }

    /// Fire the timers up to `t`, carrying the network after each round.
    fn run_until(&mut self, t: u64) {
        for _ in 0..100_000 {
            self.settle();
            let next = self.nodes.iter().filter_map(|n| n.t.poll_timeout()).min();
            match next {
                Some(x) if x <= t => {
                    self.now = self.now.max(x);
                    for i in 0..NODES {
                        if self.nodes[i].t.poll_timeout().is_some_and(|x| x <= self.now) {
                            self.tick(i);
                            let now = self.now;
                            let n = &mut self.nodes[i];
                            n.t.on_timer(&mut n.h, now);
                            self.flush(i);
                        }
                    }
                },
                _ => {
                    self.now = self.now.max(t);
                    return;
                },
            }
        }
        panic!("the timers do not reach {t}");
    }

    /// Hub `hub` (or every reachable hub) sends member `m` the FLOOR frame, as membership does on an attachment.
    fn attach(&mut self, m: usize, hub: Option<usize>) {
        for j in 0..HUBS {
            if hub.is_some_and(|h| h != j) || !self.up.contains(&(j, m)) {
                continue;
            }
            let me = self.ids[m];
            let mut body = vec![0u8; 65_536];
            let n = self.nodes[j].t.floor(&me, &mut body);
            let mut f = Vec::new();
            f.extend_from_slice(&u32::try_from(2 + n).unwrap_or(0).to_be_bytes());
            f.extend_from_slice(&[FLOOR, 0]);
            f.extend_from_slice(&body[..n]);
            self.sent.entry((j, m)).or_default().push(f.clone());
            self.links.entry((j, m)).or_default().push_back(f);
        }
        if m >= HUBS && self.nodes[m].t.primary().is_none() {
            self.set_primary(m, 0);
        }
    }

    fn set_primary(&mut self, m: usize, hub: usize) {
        let old = self.nodes[m].t.primary().copied();
        let new = self.ids[hub];
        self.tick(m);
        let now = self.now;
        let n = &mut self.nodes[m];
        n.t.primary_changed(&mut n.h, now, old.as_ref(), &new);
        self.flush(m);
    }

    fn set_link(&mut self, a: usize, b: usize, up: bool) {
        let (ia, ib) = (self.ids[a], self.ids[b]);
        for (x, y, iy) in [(a, b, ib), (b, a, ia)] {
            if up {
                self.nodes[x].h.reach.insert(iy);
                self.up.insert((x, y));
            } else {
                self.nodes[x].h.reach.remove(&iy);
                self.up.remove(&(x, y));
                // The session closed: what was in flight on it is gone.
                self.links.remove(&(x, y));
            }
        }
    }

    /// The network heals: every stream takes bytes again, every member gets its sessions with the hubs back and
    /// reports a session with every other node, and subscribes to the first topic. After the floor wait each member
    /// publishes one message there, and the world runs a minute. Returns the ids published and their origins.
    fn calm(&mut self) -> Vec<([u8; 8], usize)> {
        for a in 0..NODES {
            for b in 0..NODES {
                if self.nodes[a].h.full.contains(&self.ids[b]) {
                    self.step(&Op::Choke(a as u8, b as u8));
                }
            }
        }
        for m in HUBS..NODES {
            for j in 0..HUBS {
                self.step(&Op::Heal((m - HUBS) as u8, j as u8));
            }
            self.step(&Op::Adjacent((m - HUBS) as u8, ((1u16 << NODES) - 1 - (1 << m)) as u8));
            self.step(&Op::Subscribe(m as u8, 0));
        }
        self.step(&Op::Advance(20_000));
        self.fresh_wall = WALL0 + self.now / 1_000_000;
        let mut fresh = Vec::new();
        for m in HUBS..NODES {
            self.tag += 1;
            let body = format!("fresh {} from {m}", self.tag).into_bytes();
            self.tick(m);
            let now = self.now;
            let n = &mut self.nodes[m];
            let r = n.t.publish(&mut n.h, now, TOPICS[0], &body);
            assert!(r.is_ok(), "member {m} could not publish after the network healed: {r:?}");
            if let Ok(mid) = r {
                self.published.insert(mid, (self.ids[m], TOPICS[0].to_vec(), body));
                fresh.push((mid, m));
            }
            self.flush(m);
        }
        self.step(&Op::Advance(60_000));
        fresh
    }

    fn step(&mut self, op: &Op) {
        self.carried = 0;
        match *op {
            Op::Settle => self.settle(),
            Op::Carry(pick, n) => {
                for _ in 0..n {
                    let busy: Vec<(usize, usize)> =
                        self.links.iter().filter(|(_, q)| !q.is_empty()).map(|(k, _)| *k).collect();
                    if busy.is_empty() {
                        break;
                    }
                    let (a, b) = busy[usize::from(pick) % busy.len()];
                    self.carry(a, b);
                }
            },
            Op::Drop(pick) => {
                let busy: Vec<(usize, usize)> =
                    self.links.iter().filter(|(_, q)| !q.is_empty()).map(|(k, _)| *k).collect();
                if !busy.is_empty() {
                    let k = busy[usize::from(pick) % busy.len()];
                    self.links.get_mut(&k).and_then(VecDeque::pop_front);
                }
            },
            Op::Again(pick, back) => {
                // A peer sends again a frame it sent before on a session that is still up.
                let links: Vec<(usize, usize)> =
                    self.sent.iter().filter(|(k, v)| !v.is_empty() && self.up.contains(k)).map(|(k, _)| *k).collect();
                if !links.is_empty() {
                    let (a, b) = links[usize::from(pick) % links.len()];
                    let v = &self.sent[&(a, b)];
                    let bytes = v[v.len() - 1 - usize::from(back) % v.len()].clone();
                    self.deliver(a, b, &bytes);
                }
            },
            Op::Mangle(pick, back, at, kind, val) => {
                // A peer sends an altered copy of a frame it sent: a hostile hub, relay or member.
                let links: Vec<(usize, usize)> =
                    self.sent.iter().filter(|(k, v)| !v.is_empty() && self.up.contains(k)).map(|(k, _)| *k).collect();
                if !links.is_empty() {
                    let (a, b) = links[usize::from(pick) % links.len()];
                    let v = &self.sent[&(a, b)];
                    let mut bytes = v[v.len() - 1 - usize::from(back) % v.len()].clone();
                    // Past the length prefix, which the world does not read.
                    let i = 4 + usize::from(at) % bytes.len().saturating_sub(4).max(1);
                    match kind % 5 {
                        0 => {
                            if let Some(x) = bytes.get_mut(i) {
                                *x ^= 1 << (val % 8);
                            }
                        },
                        1 => {
                            if let Some(x) = bytes.get_mut(i) {
                                *x = val;
                            }
                        },
                        2 => bytes.truncate(i),
                        3 => bytes.insert(i.min(bytes.len()), val),
                        _ => {
                            if i < bytes.len() {
                                bytes.remove(i);
                            }
                        },
                    }
                    // A FLOOR frame from a hub to a restarted member, still well formed after the change, is believed
                    // (by design: see the liveness property); the world notes what it claims.
                    if a < HUBS
                        && b >= HUBS
                        && self.now.saturating_sub(self.nodes[b].born) < pinc_broadcast::consts::FLOOR_WAIT
                        && let Some(wall) = encoder_floor_wall(&bytes)
                    {
                        let n = &mut self.nodes[b];
                        n.forged_floor = n.forged_floor.max(wall);
                    }
                    self.deliver(a, b, &bytes);
                }
            },
            Op::PublishMany(i, topic, count) => {
                for k in 0..count {
                    self.step(&Op::Publish(i, topic, k % 30));
                }
            },
            Op::Advance(ms) => {
                let t = self.now + u64::from(ms) * 1_000_000;
                self.run_until(t);
            },
            Op::Publish(i, topic, len) => {
                let i = usize::from(i) % NODES;
                let topic = TOPICS[usize::from(topic) % TOPICS.len()];
                self.tag += 1;
                let body: Vec<u8> = (0..usize::from(len)).map(|k| (self.tag as u8) ^ (k as u8)).collect();
                self.tick(i);
                let now = self.now;
                let n = &mut self.nodes[i];
                if let Ok(mid) = n.t.publish(&mut n.h, now, topic, &body) {
                    let prev = self.published.insert(mid, (self.ids[i], topic.to_vec(), body));
                    assert!(prev.is_none(), "two publishes got the message id {mid:?}");
                }
                self.flush(i);
            },
            Op::Subscribe(i, topic) => {
                let i = usize::from(i) % NODES;
                let k = usize::from(topic) % TOPICS.len();
                self.tick(i);
                let now = self.now;
                let n = &mut self.nodes[i];
                if n.t.subscribe(&mut n.h, now, TOPICS[k]).is_ok() {
                    n.subs.insert(k);
                }
                self.flush(i);
            },
            Op::Unsubscribe(i, topic) => {
                let i = usize::from(i) % NODES;
                let k = usize::from(topic) % TOPICS.len();
                self.tick(i);
                let n = &mut self.nodes[i];
                n.t.unsubscribe(&mut n.h, TOPICS[k]);
                n.subs.remove(&k);
                self.flush(i);
            },
            Op::Primary(m, hub) => {
                let m = HUBS + usize::from(m) % (NODES - HUBS);
                self.set_primary(m, usize::from(hub) % HUBS);
            },
            Op::Cut(m, hub, held) => {
                let m = HUBS + usize::from(m) % (NODES - HUBS);
                let j = usize::from(hub) % HUBS;
                if !self.up.contains(&(m, j)) {
                    return;
                }
                self.set_link(m, j, false);
                let me = self.ids[m];
                self.tick(j);
                let n = &mut self.nodes[j];
                if held {
                    n.t.hold(&mut n.h, &me);
                } else {
                    n.t.release(&mut n.h, &me);
                }
                self.flush(j);
            },
            Op::Heal(m, hub) => {
                let m = HUBS + usize::from(m) % (NODES - HUBS);
                let j = usize::from(hub) % HUBS;
                if self.up.contains(&(m, j)) {
                    return;
                }
                self.set_link(m, j, true);
                let me = self.ids[m];
                self.tick(j);
                let n = &mut self.nodes[j];
                n.t.restore(&mut n.h, &me);
                self.flush(j);
                self.attach(m, Some(j));
                let hub_id = self.ids[j];
                self.tick(m);
                let now = self.now;
                let n = &mut self.nodes[m];
                n.t.resubscribe(&mut n.h, now, &hub_id);
                self.flush(m);
            },
            Op::Adjacent(m, mask) => {
                let m = HUBS + usize::from(m) % (NODES - HUBS);
                let peers: Vec<NodeId> = (0..NODES).filter(|j| mask & (1 << j) != 0).map(|j| self.ids[j]).collect();
                self.tick(m);
                let now = self.now;
                let n = &mut self.nodes[m];
                let _ = n.t.set_adjacent(&mut n.h, now, &peers);
                self.flush(m);
            },
            Op::Choke(a, b) => {
                let a = usize::from(a) % NODES;
                let b = usize::from(b) % NODES;
                if a == b {
                    return;
                }
                let peer = self.ids[b];
                if self.nodes[a].h.full.insert(peer) {
                    return;
                }
                // The stream took bytes again: the host says so.
                self.nodes[a].h.full.remove(&peer);
                self.tick(a);
                let now = self.now;
                let n = &mut self.nodes[a];
                n.t.peer_writable(&mut n.h, now, &peer);
                self.flush(a);
            },
            Op::Restart(m) => {
                let m = HUBS + usize::from(m) % (NODES - HUBS);
                let life = self.nodes[m].life + 1;
                self.nodes[m].t = start(m, &self.ids, self.now, life, self.limits);
                self.nodes[m].born = self.now;
                self.nodes[m].life = life;
                self.nodes[m].delivered.clear();
                self.nodes[m].got.clear();
                self.nodes[m].forged_floor = 0;
                self.nodes[m].h.out.clear();
                self.nodes[m].h.events.clear();
                for j in 0..NODES {
                    self.links.remove(&(m, j));
                    self.links.remove(&(j, m));
                }
                let me = self.ids[m];
                for j in 0..HUBS {
                    self.tick(j);
                    let n = &mut self.nodes[j];
                    n.t.release(&mut n.h, &me);
                    self.flush(j);
                }
                self.attach(m, None);
                let subs: Vec<usize> = self.nodes[m].subs.iter().copied().collect();
                for k in subs {
                    self.tick(m);
                    let now = self.now;
                    let n = &mut self.nodes[m];
                    let _ = n.t.subscribe(&mut n.h, now, TOPICS[k]);
                    self.flush(m);
                }
            },
        }
    }
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
enum Op {
    Settle,
    /// Carry up to `n` frames of one link with frames in flight.
    Carry(#[ephyra(gen = gens::int(0u8..=31))] u8, #[ephyra(gen = gens::int(1u8..=8))] u8),
    /// The network loses the next frame of one link.
    Drop(#[ephyra(gen = gens::int(0u8..=31))] u8),
    /// A peer sends again one of the frames it sent on a link.
    Again(#[ephyra(gen = gens::int(0u8..=31))] u8, #[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Milliseconds of time pass.
    Advance(
        #[ephyra(gen = gens::frequency(vec![
            (6, gens::int(0u32..=4000).boxed()),
            (2, gens::int(0u32..=9000).boxed()),
            (1, gens::int(0u32..=130_000).boxed()),
        ]))]
        u32,
    ),
    /// A peer sends an altered copy of one of the frames it sent: (link, which frame, where, how, byte).
    Mangle(
        #[ephyra(gen = gens::int(0u8..=31))] u8,
        #[ephyra(gen = gens::int(0u8..=15))] u8,
        #[ephyra(gen = gens::int(0u16..=u16::MAX))] u16,
        #[ephyra(gen = gens::int(0u8..=4))] u8,
        #[ephyra(gen = gens::int(0u8..=255))] u8,
    ),
    /// Many publishes in a row from one node to one topic: the hub log fills and evicts.
    PublishMany(
        #[ephyra(gen = gens::int(0u8..=4))] u8,
        #[ephyra(gen = gens::int(0u8..=2))] u8,
        #[ephyra(gen = gens::int(1u8..=60))] u8,
    ),
    Publish(
        #[ephyra(gen = gens::int(0u8..=4))] u8,
        #[ephyra(gen = gens::int(0u8..=2))] u8,
        #[ephyra(gen = gens::frequency(vec![(4, gens::int(0u8..=40).boxed()), (1, gens::int(0u8..=255).boxed())]))] u8,
    ),
    Subscribe(#[ephyra(gen = gens::int(0u8..=4))] u8, #[ephyra(gen = gens::int(0u8..=2))] u8),
    Unsubscribe(#[ephyra(gen = gens::int(0u8..=4))] u8, #[ephyra(gen = gens::int(0u8..=2))] u8),
    Primary(#[ephyra(gen = gens::int(0u8..=2))] u8, #[ephyra(gen = gens::int(0u8..=1))] u8),
    Cut(
        #[ephyra(gen = gens::int(0u8..=2))] u8,
        #[ephyra(gen = gens::int(0u8..=1))] u8,
        #[ephyra(gen = gens::bool())] bool,
    ),
    Heal(#[ephyra(gen = gens::int(0u8..=2))] u8, #[ephyra(gen = gens::int(0u8..=1))] u8),
    Restart(#[ephyra(gen = gens::int(0u8..=2))] u8),
    /// A member names the peers it holds sessions with (bit j: node j).
    Adjacent(#[ephyra(gen = gens::int(0u8..=2))] u8, #[ephyra(gen = gens::int(0u8..=31))] u8),
    /// The stream from one node to another fills up, or (when it was full) takes bytes again.
    Choke(#[ephyra(gen = gens::int(0u8..=4))] u8, #[ephyra(gen = gens::int(0u8..=4))] u8),
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Case {
    small: bool,
    #[ephyra(gen = gens::vec(ephyra::any::<Op>()).len(0..=60))]
    ops: Vec<Op>,
}

/// No panic, nothing delivered that was not published as delivered, no id delivered twice in one life.
#[ephyra::test(gen = ephyra::any::<Case>(), tests = 300)]
fn broadcast_world_delivers_only_what_was_published_and_at_most_once(c: Case) {
    let mut w = World::new(if c.small { small_limits() } else { Limits::default() });
    for op in &c.ops {
        w.step(op);
    }
    w.carried = 0;
    w.settle();
    ephyra::cover(w.deliveries > 0, "delivered a message");
    ephyra::cover(w.deliveries > 20, "delivered over 20 messages");
    ephyra::cover(w.restarted_deliveries > 0, "a restarted member delivered");
    let rejects = |why| w.nodes.iter().map(|n| n.t.reject_stats().count(why)).sum::<u64>();
    ephyra::cover(rejects(pinc_broadcast::Reject::Duplicate) > 0, "a duplicate was refused");
    ephyra::cover(rejects(pinc_broadcast::Reject::BadSignature) > 0, "a bad signature was refused");
    ephyra::cover(rejects(pinc_broadcast::Reject::BadHead) > 0, "a bad head was refused");
    ephyra::target(w.deliveries as f64);
}

/// Liveness after any schedule: once the network heals, a message a member publishes reaches every other member
/// subscribed to its topic within a minute. From the crate documentation: "A publisher hands a message to every hub
/// ... A hub ... pushes to its subscribers", "A subscriber repairs gaps with SUB, HAVE, GET and MSG", "A restarted
/// member gathers the replay floors of the hubs for up to 15 s and holds messages meanwhile", and "A hub keeps a
/// member's subscriptions while it is held down and tells the member when they are live again". The default limits
/// only: the small ones may refuse a subscription or a log entry by design.
///
/// One case is by design and not counted (operator, 2026-11-26: hubs stay authoritative for replay floors): a member
/// a hub sent, within the floor wait of its life, an altered FLOOR frame that is still laid out exactly as the encoder
/// writes one, with a floor at or past the fresh messages' time. Such a floor is believed and silences the member until
/// it passes ("a hub that reports a floor ahead of every clock silences a restarted member until the floor passes",
/// `floors.rs`). The world cannot see whether the member was still gathering when the frame came, so a frame that
/// came after its gathering ended is excluded too. A frame the encoder never writes is still counted: it is refused.
#[ephyra::test(gen = ephyra::any::<Case>(), tests = 300)]
fn broadcast_world_delivers_a_fresh_message_to_every_subscriber_once_the_network_heals(c: Case) {
    let mut w = World::new(Limits::default());
    for op in &c.ops {
        w.step(op);
    }
    for (mid, origin) in w.calm() {
        for m in (HUBS..NODES).filter(|m| *m != origin) {
            let n = &w.nodes[m];
            if n.forged_floor >= w.fresh_wall {
                continue;
            }
            assert!(n.got.contains(&mid), "member {m} (life {}) never delivered the message {mid:?} member {origin} published after the network healed", n.life);
        }
    }
}


/// The same liveness with honest peers: the schedule without its altered frames (a lost, late, repeated or reordered
/// frame stays), so a failure here is not a hostile peer's doing.
#[ephyra::test(gen = ephyra::any::<Case>(), tests = 300)]
fn broadcast_world_with_honest_peers_delivers_a_fresh_message_to_every_subscriber_once_the_network_heals(c: Case) {
    let mut w = World::new(Limits::default());
    for op in c.ops.iter().filter(|op| !matches!(op, Op::Mangle(..))) {
        w.step(op);
    }
    for (mid, origin) in w.calm() {
        for m in (HUBS..NODES).filter(|m| *m != origin) {
            let n = &w.nodes[m];
            assert!(n.got.contains(&mid), "member {m} (life {}) never delivered the message {mid:?} member {origin} published after the network healed", n.life);
        }
    }
}
