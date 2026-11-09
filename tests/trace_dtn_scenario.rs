//! Trace generation for the delay-tolerant scenarios: four nodes that each run the real `Forwarder`, `CustodyBook`
//! and `Ledger` joined by a seeded network that delays and loses messages and by contacts that come and go, recorded
//! as ndjson (`dtn_scenario.ndjson`) for the TLA+ trace check (`TraceDtnScenario.tla`) and the Lean replay
//! (`Vinc/TraceDtnScenario.lean`).
//!
//! One bundle (id 1, one byte) is created at node 1 with `BUDGET` copies for node 4. The host glue of a node is what
//! the models call the system: a handover of copies is offered custody (`CustodyBook::offer`) only to a higher node
//! (the ranked policy of the proofs); a bundle message at the destination marks the delivery and is answered with a
//! signed `CustodyAck` (real Ed25519, encoded to bytes and decoded at the sender); at a relay the book accepts custody
//! (the ledger may refuse: the copies are dropped and nothing is acknowledged) and the forwarder holds the copies (a
//! repeated hold ignores them); an ack is verified, then the forwarder is told `Acked` and the book `on_ack`; an ack
//! with a bad signature is dropped; time passes with `Tick` on every forwarder and `expire` on every book; a poll
//! that releases a bundle calls `delivered` on the book; the mailbox layer admits items to the shared ledger and a
//! bundle it evicts is forgotten by the forwarder.
//!
//! A run is a seeded random mix of contacts (a link flips on both nodes), ticks, polls, deliveries of any message in
//! the network, losses, pressure and forged acks, preceded by scripted runs: a chain with a recurring contact to the
//! destination (delivered before the expiry), and an outage over the expiry (released at the expiry with no link up).
//! After every event the line carries what an observer sees on every node: the copies held and handed, whether the
//! book holds the bundle, the ledger's bytes and length and the class of the bundle's item, the book's length and the
//! timers. The test asserts the facts of every scenario itself (the copy account, the ledgers, custody never leaves a
//! node before expiry except by delivery or by an ack from the node it was offered to, some node holds custody until
//! the bundle is delivered or expired), so it is meaningful without the proof tools. The trace is written to the
//! directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
//!
//! The end-to-end chain test seals a real bundle, moves it over two hops through `Reception` with range proofs and
//! opens it at the destination.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    unreachable_pub
)]

mod dtn_common;

use vinc_crypto::{IdentityAlg, Keypair, NodeId};
use vinc_dtn::custody::{CustodyAck, CustodyBook, CustodyError, Incoming};
use vinc_dtn::forward::{Action, ForwardError, Forwarder, Held, Input, Policy};
use vinc_dtn::head::BundleId;
use vinc_dtn::hlc::Hlc;
use vinc_dtn::store::{Class, Key, Ledger, Space, StoreError};
use vinc_tests::SplitMix64;

const N: usize = 4;
const BUDGET: u16 = 4;
const EXP: u64 = 30;
const RETRY: u64 = 2;
const MAX_SENDS: u8 = 3;
const LEDGER_BUDGET: u64 = 3;
const PB: u64 = 2;
/// The node whose ledger has no room at all (index), so it refuses custody.
const TIGHT: usize = 2;
const BUNDLE: BundleId = BundleId([1; 32]);

type Fwd = Forwarder<1, 3, 3, 2>;
type Book = CustodyBook<2>;
type Led = Ledger<3>;

fn key(i: usize) -> Keypair {
    let mut seed = vec![0; IdentityAlg::Ed25519.seed_len()];
    SplitMix64::new(0x5CE0 + i as u64).fill(&mut seed);
    Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap()
}

struct Node {
    kp: Keypair,
    fwd: Fwd,
    book: Book,
    led: Led,
    /// The offer id last made to each peer, repeated by a retransmission.
    last_offer: [u64; N],
}

#[derive(Clone)]
enum Msg {
    Bun {
        id: u64,
        from: usize,
        to: usize,
        copies: u16,
        fresh: bool,
        off: u64,
    },
    Ack {
        id: u64,
        from: usize,
        to: usize,
        bytes: Vec<u8>,
    },
}

impl Msg {
    fn id(&self) -> u64 {
        match self {
            Self::Bun { id, .. } | Self::Ack { id, .. } => *id,
        }
    }
}

struct Sim {
    nodes: Vec<Node>,
    ids: Vec<NodeId>,
    net: Vec<Msg>,
    up: [[bool; N]; N],
    t: u64,
    seq: u64,
    dropped: u32,
    released: u32,
    delivered: bool,
    replayed: bool,
    lines: Vec<String>,
    /// Whether a node held custody before the last event, to assert how it ended.
    held_before: [bool; N],
    /// How many outcomes of each kind were met.
    met: std::collections::BTreeMap<&'static str, u32>,
}

fn policy() -> Policy {
    Policy {
        retry_ms: RETRY,
        max_sends: MAX_SENDS,
    }
}

fn mailbox(k: u8) -> Key {
    Key {
        space: Space::MAILBOX,
        id: [k; 32],
    }
}

impl Sim {
    fn new(lines_start: &mut Vec<String>) -> Self {
        let kps: Vec<Keypair> = (0..N).map(key).collect();
        let ids: Vec<NodeId> = kps.iter().map(Keypair::node_id).collect();
        let mut nodes: Vec<Node> = kps
            .into_iter()
            .enumerate()
            .map(|(i, kp)| Node {
                kp,
                fwd: Fwd::new(policy(), 0),
                book: Book::new(),
                led: Led::new(if i == TIGHT { 0 } else { LEDGER_BUDGET }),
                last_offer: [0; N],
            })
            .collect();
        let n0 = &mut nodes[0];
        n0.book
            .accept(
                &mut n0.led,
                Incoming {
                    bundle: BUNDLE,
                    bytes: 1,
                    expires: EXP,
                    previous: ids[0],
                    offer: 0,
                },
                0,
                |_| {},
            )
            .unwrap();
        n0.fwd
            .step(
                0,
                Input::Hold(Held {
                    id: BUNDLE,
                    destination: ids[N - 1],
                    expires: EXP,
                    copies: BUDGET,
                }),
            )
            .unwrap();
        let mut s = Self {
            nodes,
            ids,
            net: vec![],
            up: [[false; N]; N],
            t: 0,
            seq: 0,
            dropped: 0,
            released: 0,
            delivered: false,
            replayed: false,
            lines: std::mem::take(lines_start),
            held_before: [false; N],
            met: std::collections::BTreeMap::new(),
        };
        s.lines.push(format!(r#"{{"t":"sc","e":"new","ns":{}}}"#, s.obs()));
        s.held_before = s.holding();
        s
    }

    fn meet(&mut self, what: &'static str) {
        *self.met.entry(what).or_insert(0) += 1;
    }

    fn idx(&self, id: &NodeId) -> usize {
        self.ids.iter().position(|x| x == id).unwrap()
    }

    fn holding(&self) -> [bool; N] {
        std::array::from_fn(|i| self.nodes[i].book.holds(&BUNDLE))
    }

    /// The observables of every node.
    fn obs(&self) -> String {
        let parts: Vec<String> = (0..N)
            .map(|i| {
                let n = &self.nodes[i];
                let class = match n.led.get(&BUNDLE.store_key()) {
                    None => 0,
                    Some(e) if e.class == Class::Custody => 1,
                    Some(_) => 2,
                };
                let tm: Vec<String> = (0..N)
                    .filter(|&p| p != i)
                    .map(|p| {
                        n.fwd
                            .timer_remaining(&self.ids[p], &BUNDLE)
                            .map_or("-1".to_string(), |r| r.to_string())
                    })
                    .collect();
                format!(
                    "[{},{},{},{},{},{},{},[{}]]",
                    n.fwd.copies_held(&BUNDLE).unwrap_or(0),
                    n.fwd.copies_handed(&BUNDLE),
                    u8::from(n.book.holds(&BUNDLE)),
                    n.led.used(),
                    n.led.len(),
                    class,
                    n.book.len(),
                    tm.join(",")
                )
            })
            .collect();
        format!("[{}]", parts.join(","))
    }

    fn emit(&mut self, body: String) {
        let obs = self.obs();
        self.lines.push(format!(r#"{{"t":"sc",{body},"ns":{obs}}}"#));
        self.check();
        self.held_before = self.holding();
    }

    fn held_total(&self) -> u32 {
        self.nodes
            .iter()
            .map(|n| u32::from(n.fwd.copies_held(&BUNDLE).unwrap_or(0)))
            .sum()
    }

    fn in_flight(&self) -> u32 {
        self.net
            .iter()
            .map(|m| match m {
                Msg::Bun {
                    copies, fresh: true, ..
                } => u32::from(*copies),
                _ => 0,
            })
            .sum()
    }

    /// The facts of every scenario, after every event.
    fn check(&self) {
        // The copy account, while no retransmitted hold was accepted after the bundle finished.
        let total = self.held_total() + self.in_flight() + self.dropped + self.released;
        if !self.replayed {
            assert_eq!(total, u32::from(BUDGET), "the copy account");
        }
        for (i, n) in self.nodes.iter().enumerate() {
            assert!(
                n.led.used() <= n.led.budget(),
                "node {i}: the ledger is over its budget"
            );
            if n.book.holds(&BUNDLE) {
                let e = n.led.get(&BUNDLE.store_key()).expect("a held bundle is in the ledger");
                assert_eq!(
                    e.class,
                    Class::Custody,
                    "node {i}: custody class behind the book's back"
                );
            }
        }
        // Until the bundle is delivered or expired some node keeps custody (ranked policy).
        if !self.delivered && self.t < EXP {
            assert!(
                self.holding().iter().any(|h| *h),
                "custody was lost before delivery or expiry"
            );
        }
    }

    /// Custody of a node ended at the last event: it must be by an ack from the offered node, a delivery or the expiry.
    fn assert_ended_by(&self, i: usize, allowed: bool) {
        if self.held_before[i] && !self.nodes[i].book.holds(&BUNDLE) {
            assert!(
                allowed || self.t >= EXP,
                "node {i}: custody ended without an ack, a delivery or the expiry"
            );
        }
    }

    fn contact(&mut self, a: usize, b: usize, up: bool) {
        let (ia, ib) = (self.ids[a], self.ids[b]);
        let (inp_a, inp_b) = if up {
            (Input::LinkUp(ib), Input::LinkUp(ia))
        } else {
            (Input::LinkDown(ib), Input::LinkDown(ia))
        };
        self.nodes[a].fwd.step(self.t, inp_a).unwrap();
        self.nodes[b].fwd.step(self.t, inp_b).unwrap();
        self.up[a][b] = up;
        self.up[b][a] = up;
        self.emit(format!(r#""e":"contact","a":{},"b":{},"up":{}"#, a + 1, b + 1, up));
        for i in 0..N {
            self.assert_ended_by(i, false);
        }
    }

    fn tick(&mut self) {
        self.t += 1;
        for n in &mut self.nodes {
            n.fwd.step(self.t, Input::Tick).unwrap();
            n.book.expire(&mut n.led, self.t, |_| {});
        }
        self.emit(r#""e":"tick""#.to_string());
        for i in 0..N {
            self.assert_ended_by(i, false);
        }
        if self.t >= EXP {
            for n in &self.nodes {
                assert!(
                    !n.book.holds(&BUNDLE) && !n.led.contains(&BUNDLE.store_key()),
                    "expiry kept custody"
                );
            }
        }
    }

    fn poll(&mut self, i: usize) {
        let before = u32::from(self.nodes[i].fwd.copies_held(&BUNDLE).unwrap_or(0));
        let action = self.nodes[i].fwd.poll();
        let mid = self.seq;
        let body = match action {
            None => {
                self.meet("poll_quiet");
                format!(r#""e":"poll","n":{},"a":"none""#, i + 1)
            }
            Some(Action::Send {
                peer,
                copies,
                retransmit,
                ..
            }) => {
                let to = self.idx(&peer);
                let mut off = if retransmit { self.nodes[i].last_offer[to] } else { 0 };
                if copies > 0 && !retransmit && to > i {
                    // A relieved node still sprays its copies but holds no record to offer from.
                    match self.nodes[i].book.offer(&BUNDLE, peer) {
                        Ok(id) => {
                            off = id;
                            self.nodes[i].last_offer[to] = id;
                            self.meet("offer");
                        }
                        Err(CustodyError::Unknown) => self.meet("offer_unknown"),
                        Err(e) => panic!("unexpected {e:?}"),
                    }
                }
                self.net.push(Msg::Bun {
                    id: mid,
                    from: i,
                    to,
                    copies,
                    fresh: !retransmit,
                    off,
                });
                self.seq += 1;
                self.meet(if retransmit { "retransmit" } else { "send" });
                format!(
                    r#""e":"poll","n":{},"a":"send","p":{},"c":{},"r":{},"mid":{mid},"off":{off}"#,
                    i + 1,
                    to + 1,
                    copies,
                    retransmit
                )
            }
            Some(Action::Release(b)) => {
                assert_eq!(b, BUNDLE);
                self.released += before;
                let n = &mut self.nodes[i];
                let r = n.book.delivered(&mut n.led, &BUNDLE);
                assert!(matches!(r, Ok(()) | Err(CustodyError::Unknown)));
                self.meet("release");
                format!(r#""e":"poll","n":{},"a":"release""#, i + 1)
            }
        };
        let released = matches!(action, Some(Action::Release(_)));
        self.emit(body);
        // A node's own release ends its custody on delivery or expiry only.
        for j in 0..N {
            self.assert_ended_by(j, j == i && released);
        }
    }

    fn deliver(&mut self, k: usize) {
        let m = self.net.remove(k);
        let t = self.t;
        let (body, relief) = match m.clone() {
            Msg::Bun {
                id,
                from,
                to,
                copies,
                fresh,
                off,
            } => {
                let outcome;
                if to == N - 1 {
                    self.delivered = true;
                    outcome = "dest";
                    self.meet("delivered");
                } else {
                    let prev = self.ids[from];
                    let node = &mut self.nodes[to];
                    let acc = node.book.accept(
                        &mut node.led,
                        Incoming {
                            bundle: BUNDLE,
                            bytes: 1,
                            expires: EXP,
                            previous: prev,
                            offer: off,
                        },
                        t,
                        |_| {},
                    );
                    match acc {
                        Err(CustodyError::Store(StoreError::CustodyRefused)) => {
                            if fresh {
                                self.dropped += u32::from(copies);
                            }
                            outcome = "refused";
                        }
                        Err(CustodyError::Capacity) => {
                            if fresh {
                                self.dropped += u32::from(copies);
                            }
                            outcome = "capacity";
                        }
                        Err(CustodyError::Store(StoreError::Expired)) => {
                            if fresh {
                                self.dropped += u32::from(copies);
                            }
                            outcome = "other";
                        }
                        Err(e) => panic!("unexpected {e:?}"),
                        Ok(_) => {
                            let held = Held {
                                id: BUNDLE,
                                destination: self.ids[N - 1],
                                expires: EXP,
                                copies,
                            };
                            match node.fwd.step(t, Input::Hold(held)) {
                                Ok(()) => {
                                    if !fresh {
                                        self.replayed = true;
                                    }
                                    outcome = "held";
                                }
                                Err(
                                    ForwardError::Duplicate
                                    | ForwardError::Full
                                    | ForwardError::NoCopies
                                    | ForwardError::Finished,
                                ) => {
                                    if fresh {
                                        self.dropped += u32::from(copies);
                                    }
                                    outcome = "holdrefused";
                                }
                                Err(e) => panic!("unexpected {e:?}"),
                            }
                        }
                    }
                    self.meet(outcome);
                }
                if outcome != "refused" && outcome != "capacity" && outcome != "other" {
                    let ack =
                        CustodyAck::sign(BUNDLE, self.ids[from], off, Hlc::new(t, 0), &self.nodes[to].kp).unwrap();
                    let mut bytes = vec![0; ack.encoded_len()];
                    ack.encode(&mut bytes).unwrap();
                    let aid = self.seq;
                    self.seq += 1;
                    self.net.push(Msg::Ack {
                        id: aid,
                        from: to,
                        to: from,
                        bytes,
                    });
                }
                (
                    format!(r#""e":"bun","m":{id},"o":"{outcome}","aid":{}"#, self.seq - 1),
                    false,
                )
            }
            Msg::Ack {
                id, from, to, bytes, ..
            } => {
                let ack = CustodyAck::decode(&bytes).unwrap();
                ack.verify().unwrap();
                assert_eq!(self.idx(&ack.custodian), from);
                let node = &mut self.nodes[to];
                let before = node.book.holds(&BUNDLE);
                let _ = node.fwd.step(
                    t,
                    Input::Acked {
                        peer: ack.custodian,
                        bundle: BUNDLE,
                    },
                );
                let r = node.book.on_ack(&mut node.led, &ack);
                let o = match r {
                    Ok(()) => "ok",
                    Err(CustodyError::Unknown) => "unknown",
                    Err(CustodyError::NotOffered) => "notoffered",
                    Err(CustodyError::Store(StoreError::Unknown)) => "storeunknown",
                    Err(e) => panic!("unexpected {e:?}"),
                };
                self.meet(match o {
                    "ok" => "relief",
                    "unknown" => "ack_unknown",
                    "notoffered" => "ack_notoffered",
                    _ => "ack_storeunknown",
                });
                (
                    format!(r#""e":"ack","m":{id},"o":"{o}""#),
                    before && !self.nodes[to].book.holds(&BUNDLE),
                )
            }
        };
        let to = match m {
            Msg::Bun { to, .. } | Msg::Ack { to, .. } => to,
        };
        self.emit(body);
        for j in 0..N {
            self.assert_ended_by(j, relief && j == to);
        }
    }

    fn lose(&mut self, k: usize) {
        let m = self.net.remove(k);
        if let Msg::Bun {
            copies, fresh: true, ..
        } = m
        {
            self.dropped += u32::from(copies);
        }
        self.meet("lose");
        self.emit(format!(r#""e":"lose","m":{}"#, m.id()));
    }

    fn pressure(&mut self, i: usize, k: u8) {
        let t = self.t;
        let mut trial = self.nodes[i].led.clone();
        let mut evicted = vec![];
        if trial
            .admit(mailbox(k), PB, Class::Transit, EXP + 100, t, |e| evicted.push(e.key))
            .is_err()
        {
            return;
        }
        self.nodes[i].led = trial;
        let forgotten = evicted.iter().any(|key| key.space == Space::DTN);
        if forgotten {
            self.released += u32::from(self.nodes[i].fwd.copies_held(&BUNDLE).unwrap_or(0));
            let _ = self.nodes[i].fwd.step(t, Input::Forget(BUNDLE));
            self.meet("forget");
        }
        self.meet("pressure");
        self.emit(format!(r#""e":"press","n":{},"k":{k}"#, i + 1));
        for j in 0..N {
            self.assert_ended_by(j, false);
        }
    }

    /// An ack whose signature does not verify: dropped by the glue, nothing moves.
    fn forged(&mut self, from: usize, to: usize) {
        let ack = CustodyAck::sign(BUNDLE, self.ids[to], 0, Hlc::new(self.t, 0), &self.nodes[from].kp).unwrap();
        let mut bytes = vec![0; ack.encoded_len()];
        ack.encode(&mut bytes).unwrap();
        let last = bytes.len() - 1;
        bytes[last] ^= 1;
        let bad = CustodyAck::decode(&bytes).unwrap();
        assert!(bad.verify().is_err());
        self.meet("forged");
        self.emit(format!(r#""e":"bad","a":{},"b":{}"#, from + 1, to + 1));
    }

    fn random_step(&mut self, rng: &mut SplitMix64) {
        let r = rng.next_u64() % 100;
        match r {
            0..=17 => {
                let a = (rng.next_u64() % N as u64) as usize;
                let b = (rng.next_u64() % N as u64) as usize;
                if a != b {
                    let (a, b) = (a.min(b), a.max(b));
                    self.contact(a, b, !self.up[a][b]);
                }
            }
            18..=31 => {
                if self.t < EXP + 3 {
                    self.tick();
                }
            }
            32..=60 => self.poll((rng.next_u64() % N as u64) as usize),
            61..=85 => {
                if !self.net.is_empty() {
                    let k = (rng.next_u64() % self.net.len() as u64) as usize;
                    self.deliver(k);
                }
            }
            86..=90 => {
                if !self.net.is_empty() {
                    let k = (rng.next_u64() % self.net.len() as u64) as usize;
                    self.lose(k);
                }
            }
            91..=96 => self.pressure((rng.next_u64() % N as u64) as usize, 1 + (rng.next_u64() % 2) as u8),
            _ => {
                let a = (rng.next_u64() % N as u64) as usize;
                let b = (a + 1 + (rng.next_u64() % (N as u64 - 1)) as usize) % N;
                self.forged(a, b);
            }
        }
    }

    /// Poll every node until quiet and deliver every message in order, as a lasting contact would.
    fn settle(&mut self) {
        for _ in 0..40 {
            let mut busy = false;
            for i in 0..N {
                while self.nodes[i].fwd.poll_probe() {
                    busy = true;
                    self.poll(i);
                }
            }
            while !self.net.is_empty() {
                busy = true;
                self.deliver(0);
            }
            if !busy {
                return;
            }
        }
        panic!("the network did not settle");
    }
}

/// Whether a poll would act, without acting: poll a clone.
trait Probe {
    fn poll_probe(&self) -> bool;
}
impl Probe for Fwd {
    fn poll_probe(&self) -> bool {
        self.clone().poll().is_some()
    }
}

fn finish(sim: Sim, name: &str, all: &mut Vec<String>) -> Sim {
    println!("scenario {name}: {} events, met {:?}", sim.lines.len(), sim.met);
    let mut sim = sim;
    all.append(&mut sim.lines);
    sim
}

/// Scripted: a chain 1 -> 2 -> 4 with contacts that recur before the expiry; the bundle is delivered and released.
fn chain(all: &mut Vec<String>) -> Sim {
    let mut s = Sim::new(all);
    s.contact(0, 1, true);
    s.settle();
    s.contact(0, 1, false);
    s.tick();
    s.contact(1, 3, true);
    s.settle();
    assert!(s.delivered, "delivery under a recurring contact");
    s.tick();
    s.settle();
    assert!(s.met["relief"] >= 1, "node 1 was relieved");
    finish(s, "chain", all)
}

/// Scripted: an outage over the expiry. No link is ever up after the first handover; time passes the expiry; every
/// node releases the bundle and every ledger drops it, whatever the links did.
fn outage(all: &mut Vec<String>) -> Sim {
    let mut s = Sim::new(all);
    s.contact(0, 1, true);
    s.settle();
    s.contact(0, 1, false);
    // A transfer to node 2 that was lost leaves a timer; the link is down so it does not run.
    for _ in 0..EXP + 2 {
        s.tick();
    }
    for i in 0..N {
        s.poll(i);
        s.poll(i);
    }
    assert!(!s.delivered);
    for n in &s.nodes {
        assert!(n.fwd.copies_held(&BUNDLE).is_none() && !n.book.holds(&BUNDLE) && !n.led.contains(&BUNDLE.store_key()));
    }
    finish(s, "outage", all)
}

/// Scripted: a lost ack is retransmitted and acknowledged; a refused custody drops the copies.
fn lossy(all: &mut Vec<String>) -> Sim {
    let mut s = Sim::new(all);
    s.contact(0, 1, true);
    s.poll(0);
    // the handover reaches node 2 but its ack is lost
    s.deliver(0);
    s.lose(0);
    for _ in 0..=RETRY {
        s.tick();
    }
    s.poll(0);
    s.deliver(0);
    s.deliver(0);
    finish(s, "lossy", all)
}

#[test]
fn scenarios_hold_and_write_the_trace() {
    let mut all: Vec<String> = vec![];
    let mut met: std::collections::BTreeMap<&'static str, u32> = std::collections::BTreeMap::new();
    let mut add = |s: Sim| {
        for (k, v) in s.met {
            *met.entry(k).or_insert(0) += v;
        }
    };
    add(chain(&mut all));
    add(outage(&mut all));
    add(lossy(&mut all));
    for seed in 0..40u64 {
        let mut rng = SplitMix64::new(0xD7A0 + seed);
        let mut s = Sim::new(&mut all);
        for _ in 0..220 {
            s.random_step(&mut rng);
        }
        add(finish(s, &format!("random {seed}"), &mut all));
    }
    for want in [
        "poll_quiet",
        "offer",
        "send",
        "retransmit",
        "release",
        "delivered",
        "held",
        "holdrefused",
        "refused",
        "relief",
        "ack_unknown",
        "ack_notoffered",
        "lose",
        "forget",
        "pressure",
        "forged",
    ] {
        assert!(met.get(want).copied().unwrap_or(0) > 0, "outcome {want} was never met");
    }
    println!("met {met:?}");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = all.join("\n");
        text.push('\n');
        std::fs::write(std::path::Path::new(&dir).join("dtn_scenario.ndjson"), text).unwrap();
    }
}

/// A real bundle over two hops: sealed at the source, received with range proofs at the relay, forwarded, received
/// at the destination and opened.
#[test]
fn a_sealed_bundle_crosses_a_chain_and_opens() {
    use dtn_common::{ALGS, make, plan, recipient};
    use vinc_crypto::Software;
    use vinc_dtn::bundle::{Reception, serve, serve_len};
    use vinc_dtn::seal::decapsulate;

    let src = dtn_common::keypair(ALGS[0], 11);
    let dst = recipient(ALGS[0], 12, 1);
    let payload: Vec<u8> = (0..5000u32).map(|x| (x % 251) as u8).collect();
    let sealed = make(&src, &dst, plan(3, 2, 0), &payload, 99);
    let layout = sealed.signed.head().layout().unwrap();
    let total = layout.total_symbols();
    let mut carried_sealed = sealed.sealed.clone();
    let mut carried_outboard = sealed.outboard.clone();
    let mut now = 1_000;
    for _hop in 0..2 {
        now += 100;
        let mut buf = vec![0u8; layout.total_len() as usize];
        let mut rx = Reception::<8>::new(&sealed.signed, &mut buf, now).unwrap();
        let mut stream = vec![0; serve_len(&layout, &(0..total)).unwrap()];
        serve(&layout, &carried_sealed, &carried_outboard, &(0..total), &mut stream).unwrap();
        rx.feed(0..total, &stream).unwrap();
        assert!(rx.is_complete());
        let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
        dtn_common::finish(&mut rx, &mut outboard).unwrap();
        carried_sealed = rx.sealed().to_vec();
        carried_outboard = outboard;
    }
    let mut stream = vec![0; serve_len(&layout, &(0..total)).unwrap()];
    serve(&layout, &carried_sealed, &carried_outboard, &(0..total), &mut stream).unwrap();
    let mut buf2 = vec![0u8; layout.total_len() as usize];
    let mut rx2 = Reception::<8>::new(&sealed.signed, &mut buf2, now).unwrap();
    rx2.feed(0..total, &stream).unwrap();
    let cipher = decapsulate(&Software, &dst.keys, &dst.dk, &dst.xs, sealed.signed.head()).unwrap();
    let mut out = vec![0; layout.padded_len() as usize];
    let n = rx2.open(&Software, &cipher, &mut out).unwrap();
    assert_eq!(&out[..n], &payload[..]);
}
