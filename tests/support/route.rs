//! The in-memory network between two connection endpoints: [`Link`] holds one or more [`Route`]s, each a pair of
//! [`Dir`]ections with their own one-way delay, jitter, loss, duplication, reordering, datagram size limit and
//! bandwidth cap, drawing from a seeded [`SplitMix64`] so a run repeats exactly. A direction is a first-in, first-out
//! queue unless [`Params::unordered_jitter`] says otherwise; reordering is explicit ([`Params::reorder`],
//! [`Dir::delay_index`]).
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss,
    clippy::cast_sign_loss,
    clippy::missing_panics_doc,
    clippy::must_use_candidate,
    clippy::return_self_not_must_use
)]

use std::cmp::Ordering;
use std::collections::BinaryHeap;

use vinc_transport::conn::PathId;

use crate::SplitMix64;

/// One direction of a route.
#[derive(Debug, Clone, Copy)]
pub struct Params {
    pub delay_ns: u64,
    pub jitter_ns: u64,
    /// Loss probability in parts per million.
    pub loss_ppm: u32,
    pub dup_ppm: u32,
    /// Probability (ppm) that a datagram is held back by `reorder_ns`.
    pub reorder_ppm: u32,
    pub reorder_ns: u64,
    /// Each datagram draws its jitter independently and may overtake earlier ones (off: the queue keeps its order).
    pub unordered: bool,
    /// Datagrams longer than this are dropped.
    pub mtu: usize,
    /// Bits per second; 0 means unlimited.
    pub bps: u64,
    /// Longest queue behind the bandwidth cap before tail drop.
    pub queue_ns: u64,
}

impl Params {
    /// A clean link with the given one-way delay.
    pub fn new(delay_ns: u64) -> Self {
        Self {
            delay_ns,
            jitter_ns: 0,
            loss_ppm: 0,
            dup_ppm: 0,
            reorder_ppm: 0,
            reorder_ns: 0,
            unordered: false,
            mtu: 65_535,
            bps: 0,
            queue_ns: 200_000_000,
        }
    }
    pub fn loss(mut self, percent: f64) -> Self {
        self.loss_ppm = (percent * 10_000.0) as u32;
        self
    }
    pub fn dup(mut self, percent: f64) -> Self {
        self.dup_ppm = (percent * 10_000.0) as u32;
        self
    }
    pub fn reorder(mut self, percent: f64, extra_ns: u64) -> Self {
        self.reorder_ppm = (percent * 10_000.0) as u32;
        self.reorder_ns = extra_ns;
        self
    }
    /// Up to `ns` of extra delay per datagram, keeping the queue's order.
    pub fn jitter(mut self, ns: u64) -> Self {
        self.jitter_ns = ns;
        self
    }
    /// Up to `ns` of extra delay drawn independently per datagram, so datagrams sent within `ns` of each other arrive
    /// in any order (a stress model; no single real queue does this).
    pub fn unordered_jitter(mut self, ns: u64) -> Self {
        self.jitter_ns = ns;
        self.unordered = true;
        self
    }
    pub fn mtu(mut self, mtu: usize) -> Self {
        self.mtu = mtu;
        self
    }
    pub fn bandwidth(mut self, bps: u64) -> Self {
        self.bps = bps;
        self
    }
}

#[derive(Debug)]
struct Item {
    at: u64,
    seq: u64,
    data: Vec<u8>,
}
impl PartialEq for Item {
    fn eq(&self, o: &Self) -> bool {
        (self.at, self.seq) == (o.at, o.seq)
    }
}
impl Eq for Item {}
impl PartialOrd for Item {
    fn partial_cmp(&self, o: &Self) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Item {
    fn cmp(&self, o: &Self) -> Ordering {
        (o.at, o.seq).cmp(&(self.at, self.seq))
    }
}

/// One direction: parameters, randomness and the datagrams in flight.
#[derive(Debug)]
pub struct Dir {
    pub p: Params,
    rng: SplitMix64,
    heap: BinaryHeap<Item>,
    seq: u64,
    free_at: u64,
    last_at: u64,
    drop_next: u32,
    drop_index: Option<u64>,
    delay_index: Option<(u64, u64)>,
    pub sent: u64,
    pub dropped: u64,
    pub delivered: u64,
}

impl Dir {
    fn new(p: Params, seed: u64) -> Self {
        Self {
            p,
            rng: SplitMix64::new(seed),
            heap: BinaryHeap::new(),
            seq: 0,
            free_at: 0,
            last_at: 0,
            drop_next: 0,
            drop_index: None,
            delay_index: None,
            sent: 0,
            dropped: 0,
            delivered: 0,
        }
    }
    fn draw(&mut self, ppm: u32) -> bool {
        ppm > 0 && (self.rng.next_u64() % 1_000_000) < u64::from(ppm)
    }
    fn send(&mut self, now: u64, data: &[u8]) {
        self.sent += 1;
        if self.drop_index == Some(self.sent) {
            self.dropped += 1;
            return;
        }
        if self.drop_next > 0 {
            self.drop_next -= 1;
            self.dropped += 1;
            return;
        }
        if data.len() > self.p.mtu || self.draw(self.p.loss_ppm) {
            self.dropped += 1;
            return;
        }
        let mut at = now;
        if let Some(tx_ns) = (data.len() as u64 * 8 * 1_000_000_000).checked_div(self.p.bps) {
            let start = self.free_at.max(now);
            if start - now > self.p.queue_ns {
                self.dropped += 1;
                return;
            }
            self.free_at = start + tx_ns;
            at = self.free_at;
        }
        let jitter = if self.p.jitter_ns > 0 {
            self.rng.next_u64() % self.p.jitter_ns
        } else {
            0
        };
        at += self.p.delay_ns + jitter;
        if !self.p.unordered {
            at = at.max(self.last_at);
            self.last_at = at;
        }
        // Applied after the queue's order is kept, so the datagrams behind this one may overtake it.
        if let Some((k, extra)) = self.delay_index
            && k == self.sent
        {
            at += extra;
        }
        if self.draw(self.p.reorder_ppm) {
            at += self.p.reorder_ns;
        }
        self.push(at, data.to_vec());
        if self.draw(self.p.dup_ppm) {
            let extra = 1 + self.rng.next_u64() % 1_000_000;
            self.push(at + extra, data.to_vec());
        }
    }
    fn push(&mut self, at: u64, data: Vec<u8>) {
        self.seq += 1;
        self.heap.push(Item {
            at,
            seq: self.seq,
            data,
        });
    }
    /// Drop only the `k`th datagram (counting from 1) sent in this direction.
    pub fn drop_index(&mut self, k: u64) {
        self.drop_index = Some(k);
    }
    /// Hold back only the `k`th datagram (counting from 1) sent in this direction by `extra_ns`, so the ones sent
    /// after it may arrive first.
    pub fn delay_index(&mut self, k: u64, extra_ns: u64) {
        self.delay_index = Some((k, extra_ns));
    }
    /// Drop the next `n` datagrams sent in this direction.
    pub fn drop_next(&mut self, n: u32) {
        self.drop_next = n;
    }
    fn next_at(&self) -> Option<u64> {
        self.heap.peek().map(|i| i.at)
    }
    fn pop(&mut self, now: u64) -> Option<Vec<u8>> {
        if self.heap.peek().is_some_and(|i| i.at <= now) {
            self.delivered += 1;
            return self.heap.pop().map(|i| i.data);
        }
        None
    }
}

/// A route between the endpoints: `a` is how A names it, `b` how B names it.
#[derive(Debug)]
pub struct Route {
    pub a: PathId,
    pub b: PathId,
    pub ab: Dir,
    pub ba: Dir,
    pub up: bool,
}

/// The network between endpoints A and B.
#[derive(Debug)]
pub struct Link {
    pub routes: Vec<Route>,
    seed: u64,
}

impl Link {
    /// One route, named 1 by A and 2 by B, symmetric.
    pub fn new(seed: u64, p: Params) -> Self {
        let mut l = Self {
            routes: Vec::new(),
            seed,
        };
        l.add_route(PathId(1), PathId(2), p, p);
        l
    }
    pub fn add_route(&mut self, a: PathId, b: PathId, ab: Params, ba: Params) {
        let n = self.routes.len() as u64;
        self.routes.push(Route {
            a,
            b,
            ab: Dir::new(ab, self.seed ^ (n * 2 + 1)),
            ba: Dir::new(ba, self.seed ^ (n * 2 + 2)),
            up: true,
        });
    }
    pub fn route(&mut self, a: PathId) -> &mut Route {
        self.routes.iter_mut().find(|r| r.a == a).unwrap()
    }
    /// Set the parameters of both directions of a route.
    pub fn set(&mut self, a: PathId, ab: Params, ba: Params) {
        let r = self.route(a);
        r.ab.p = ab;
        r.ba.p = ba;
    }
    /// A's datagram to the route A calls `a`.
    pub fn send_a(&mut self, now: u64, a: PathId, data: &[u8]) {
        if let Some(r) = self.routes.iter_mut().find(|r| r.a == a && r.up) {
            r.ab.send(now, data);
        }
    }
    /// B's datagram to the route B calls `b`.
    pub fn send_b(&mut self, now: u64, b: PathId, data: &[u8]) {
        if let Some(r) = self.routes.iter_mut().find(|r| r.b == b && r.up) {
            r.ba.send(now, data);
        }
    }
    pub fn next_at(&self) -> Option<u64> {
        self.routes
            .iter()
            .flat_map(|r| [r.ab.next_at(), r.ba.next_at()])
            .flatten()
            .min()
    }
    pub(crate) fn pop_b(&mut self, now: u64) -> Option<(PathId, Vec<u8>)> {
        self.routes.iter_mut().find_map(|r| r.ab.pop(now).map(|d| (r.b, d)))
    }
    pub(crate) fn pop_a(&mut self, now: u64) -> Option<(PathId, Vec<u8>)> {
        self.routes.iter_mut().find_map(|r| r.ba.pop(now).map(|d| (r.a, d)))
    }
    /// NAT rebinding: B now sees A's datagrams on the route `a` as coming from `new_b`.
    pub fn rebind(&mut self, a: PathId, new_b: PathId) {
        self.route(a).b = new_b;
    }
}
