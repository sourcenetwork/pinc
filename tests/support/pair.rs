//! Two connections joined by a network the test controls datagram by datagram.
//!
//! [`Pair`] takes two connected [`Node`]s and keeps every datagram they send in a pool. A test (or a seeded schedule)
//! decides which datagram reaches which node, when, how often and in what order, so loss, reordering and
//! duplication are explicit steps and not random draws. Time is a number the caller moves.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::indexing_slicing,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

use pinc_security::{Env, ResponderStores};
use pinc_transport::conn::{Drop, KeyEvent, KeysView, Lent, PathId, Transmit};

use super::{Net, Node, PK, TK};

/// A datagram a node sent.
#[derive(Debug, Clone)]
pub struct Dgram {
    /// Whether node A sent it.
    pub from_a: bool,
    pub path: PathId,
    pub bytes: Vec<u8>,
}

/// A step of the key layer of one node, in the order the steps happened.
#[derive(Debug, Clone)]
pub struct Logged {
    /// Whether node A took the step.
    pub a: bool,
    pub ev: KeyEvent,
    /// The key state of the node right after the step, when the connection could take it.
    pub view: Option<KeysView>,
    /// For a sealed packet: its datagram in the pool.
    pub dgram: Option<usize>,
}

/// Two connected nodes and the datagrams between them.
pub struct Pair<'a> {
    pub a: Node<'a>,
    pub b: Node<'a>,
    pub stores: Box<ResponderStores<PK, TK>>,
    pub now: u64,
    pub pool: Vec<Dgram>,
    /// What the receivers refused: `(to_a, reason)`.
    pub drops: Vec<(bool, Drop)>,
    /// Every key-layer step of both nodes, in order.
    pub events: Vec<Logged>,
    buf: Vec<u8>,
}

impl<'a> Pair<'a> {
    /// Take over a connected network: the nodes and the time. Datagrams still in flight on the link are lost.
    pub fn from_net(net: Net<'a, '_>) -> Self {
        let Net { mut a, mut b, now, .. } = net;
        // What the connections noted while they connected is not part of the pair's story.
        let _ = (a.conn.trace_take(), b.conn.trace_take());
        a.conn.trace_enable();
        b.conn.trace_enable();
        Self {
            a,
            b,
            stores: Box::default(),
            now,
            pool: Vec::new(),
            drops: Vec::new(),
            events: Vec::new(),
            buf: vec![0u8; 65_536],
        }
    }

    pub fn node(&mut self, a: bool) -> &mut Node<'a> {
        if a { &mut self.a } else { &mut self.b }
    }

    /// Let node `a` (or B) build every datagram it wants to send now; returns their indices in the pool.
    pub fn pump(&mut self, a: bool) -> Vec<usize> {
        let now = self.now;
        let mut made = Vec::new();
        loop {
            let node = if a { &mut self.a } else { &mut self.b };
            let mut env = Env {
                provider: &node.prov,
                now,
                drbg: &mut node.drbg,
            };
            let Some(Transmit {
                path,
                len,
                segment_size,
            }) = node
                .conn
                .poll_transmit(&mut env, &mut Lent { spill: &mut node.spill }, &mut self.buf)
            else {
                break;
            };
            for seg in self.buf[..len].chunks(segment_size) {
                made.push(self.pool.len());
                self.pool.push(Dgram {
                    from_a: a,
                    path,
                    bytes: seg.to_vec(),
                });
            }
        }
        node_service(self, a);
        let mut idx = made.iter().copied();
        let evs = self.node(a).conn.trace_take();
        for (ev, view) in evs {
            let dgram = if matches!(ev, KeyEvent::Sent { .. }) {
                idx.next()
            } else {
                None
            };
            self.events.push(Logged { a, ev, view, dgram });
        }
        assert!(idx.next().is_none(), "a datagram without a sealed packet");
        made
    }

    /// Move the key-layer steps of node `a` into [`Pair::events`].
    fn drain(&mut self, a: bool) {
        for (ev, view) in self.node(a).conn.trace_take() {
            self.events.push(Logged {
                a,
                ev,
                view,
                dgram: None,
            });
        }
    }

    /// Deliver pool datagram `idx` to the node it is addressed to (any number of times is allowed).
    pub fn deliver(&mut self, idx: usize) {
        self.deliver_with(idx, |_| {});
    }

    /// As [`Pair::deliver`], with the bytes changed by `tamper` first (the pool keeps the original).
    pub fn deliver_with(&mut self, idx: usize, tamper: impl FnOnce(&mut Vec<u8>)) {
        let now = self.now;
        let d = self.pool[idx].clone();
        let to_a = !d.from_a;
        let mut bytes = d.bytes;
        tamper(&mut bytes);
        let result = if to_a {
            let mut env = Env {
                provider: &self.a.prov,
                now,
                drbg: &mut self.a.drbg,
            };
            self.a.conn.handle_datagram(
                &mut env,
                &mut Lent {
                    spill: &mut self.a.spill,
                },
                path_of(d.path, true),
                &mut bytes,
            )
        } else {
            let mut env = Env {
                provider: &self.b.prov,
                now,
                drbg: &mut self.b.drbg,
            };
            self.b.conn.handle_datagram_with(
                &mut env,
                &mut Lent {
                    spill: &mut self.b.spill,
                },
                &mut self.stores,
                path_of(d.path, false),
                &mut bytes,
            )
        };
        if let Err(e) = result {
            self.drops.push((to_a, e));
        }
        node_service(self, to_a);
        self.drain(to_a);
    }

    /// Run the timers of a node that are due at `now`.
    pub fn fire_timers(&mut self, a: bool) {
        let now = self.now;
        let node = self.node(a);
        if node.conn.poll_timeout().is_some_and(|t| t <= now) {
            let mut env = Env {
                provider: &node.prov,
                now,
                drbg: &mut node.drbg,
            };
            node.conn.handle_timeout(&mut env, &mut Lent { spill: &mut node.spill });
        }
        node_service(self, a);
        self.drain(a);
    }

    /// Move time forward by `ns` and run the timers that came due.
    pub fn advance(&mut self, ns: u64) {
        self.now += ns;
        self.fire_timers(true);
        self.fire_timers(false);
    }

    /// Deliver every datagram of `idxs` in order.
    pub fn deliver_all(&mut self, idxs: &[usize]) {
        for &i in idxs {
            self.deliver(i);
        }
    }

    /// Let the two nodes talk with no loss until neither has anything to send or a timer due within 200 ms (a
    /// bounded number of rounds). Timers that come due move the time forward.
    pub fn settle(&mut self) {
        for _ in 0..200 {
            let mut sent = self.pump(true);
            sent.extend(self.pump(false));
            if !sent.is_empty() {
                self.deliver_all(&sent);
                continue;
            }
            let next = [self.a.conn.poll_timeout(), self.b.conn.poll_timeout()]
                .into_iter()
                .flatten()
                .min();
            match next {
                Some(t) if t <= self.now + 200 * super::MS => {
                    self.now = self.now.max(t);
                    self.fire_timers(true);
                    self.fire_timers(false);
                }
                _ => break,
            }
        }
    }
}

fn node_service(p: &mut Pair<'_>, a: bool) {
    let now = p.now;
    p.node(a).service(now);
}

/// The path id the receiving node names a route: A names it 1, B names it 2.
fn path_of(sender_path: PathId, to_a: bool) -> PathId {
    let _ = sender_path;
    if to_a { PathId(1) } else { PathId(2) }
}
