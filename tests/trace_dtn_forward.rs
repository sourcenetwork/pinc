//! Trace generation for the spray-and-wait forwarder: seeded random runs of the real `Forwarder` through its public
//! API (`step`, `poll`, `copies_held`, `copies_handed`, `timer_remaining`), recorded as ndjson for the TLA+ trace
//! check (`TraceDtnForward.tla`) and the Lean replay (`Vinc/TraceDtnForward.lean`).
//!
//! The world is small so that every branch is met: three peers (node ids 1 to 3), three bundles (ids 1 to 3), tables of
//! two bundles, two links and two transfers, retry 3 ms and 3 sends, times of a few tens of milliseconds (time also
//! goes backwards in a call, which the forwarder must ignore). A run mixes the inputs in a seeded order: ticks, holds
//! (with zero copies, repeated, with full tables), links up and down (also a third link on a two-link table),
//! acknowledgements (also of nothing), forgets (also of nothing), and polls that drain the machine or stop early.
//!
//! What is recorded is what an observer sees: the input with its time, the error it returned, the action each poll
//! returned, and after every call `ch` (copies held per bundle, 0 for none), `cd` (copies handed per bundle) and `tm`
//! (the timer of each (bundle, peer) transfer plus one, 0 for no running timer). The links, the delivered flag and
//! the transfer phases are not readable, so the model has to reproduce them for the later observations to match.
//!
//! The test asserts everything itself against a tracker written here that does not share code with the forwarder
//! (copy balance per bundle, the halving rule, one transfer per (bundle, peer), the send count of a transfer, timers
//! frozen on a down link, the release order, the quiet condition, the give-up condition), and that every branch of the
//! forwarder was met, so it is meaningful without the proof tools. The main world goes to `dtn_forward.ndjson` and is
//! checked by both TLA+ and Lean; `dtn_forward_edge.ndjson` holds other capacities and policies (a retry of 0, a
//! limit of 0 and 1 sends) and times next to `u64::MAX`, and is replayed by Lean only (the TLA+ constants are those of
//! the main world). The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is
//! written.
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
    clippy::manual_midpoint,
    unreachable_pub
)]

use std::collections::{HashMap, HashSet};

use vinc_crypto::{IdentityAlg, NodeId};
use vinc_dtn::forward::{Action, ForwardError, Forwarder, Held, Input, Policy};
use vinc_dtn::head::BundleId;
use vinc_tests::SplitMix64;

const PEERS: u8 = 3;
const IDS: u8 = 3;

fn node(n: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [n; 32],
    }
}

fn bid(n: u8) -> BundleId {
    BundleId([n; 32])
}

fn peer_of(n: &NodeId) -> u8 {
    n.bytes[0]
}

fn id_of(b: &BundleId) -> u8 {
    b.0[0]
}

const BRANCHES: [&str; 22] = [
    "hold_ok",
    "hold_nocopies",
    "hold_duplicate",
    "hold_full",
    "link_new",
    "link_toggle",
    "link_full",
    "ack_ok",
    "ack_deliver",
    "ack_unknown",
    "forget_ok",
    "forget_unknown",
    "back_in_time",
    "send_spray",
    "send_deliver",
    "send_retransmit",
    "gave_up",
    "release_expired",
    "release_delivered",
    "timer_frozen",
    "spray_blocked_by_full_table",
    "wait_single_copy",
];

fn err_name(e: Result<(), ForwardError>) -> &'static str {
    match e {
        Ok(()) => "ok",
        Err(ForwardError::Duplicate) => "Duplicate",
        Err(ForwardError::Full) => "Full",
        Err(ForwardError::NoCopies) => "NoCopies",
        Err(ForwardError::Unknown) => "Unknown",
    }
}

fn input_json(inp: &Input) -> String {
    match inp {
        Input::Tick => r#"{"k":"tick"}"#.into(),
        Input::Hold(h) => format!(
            r#"{{"k":"hold","id":{},"dest":{},"exp":{},"copies":{}}}"#,
            id_of(&h.id),
            peer_of(&h.destination),
            h.expires,
            h.copies
        ),
        Input::LinkUp(p) => format!(r#"{{"k":"up","peer":{}}}"#, peer_of(p)),
        Input::LinkDown(p) => format!(r#"{{"k":"down","peer":{}}}"#, peer_of(p)),
        Input::Acked { peer, bundle } => format!(r#"{{"k":"ack","peer":{},"id":{}}}"#, peer_of(peer), id_of(bundle)),
        Input::Forget(b) => format!(r#"{{"k":"forget","id":{}}}"#, id_of(b)),
    }
}

/// The independent tracker: what an observer infers from the inputs, without the forwarder's tables.
struct Track {
    now: u64,
    policy: Policy,
    /// Per live bundle: copies received, destination, expiry.
    rcv: HashMap<u8, (u16, u8, u64)>,
    delivered: HashSet<u8>,
    /// Per live (bundle, peer) transfer: sends so far and copies handed.
    sends: HashMap<(u8, u8), (u8, u16)>,
    /// Peers whose link is up, and peers that have a link slot.
    up: HashSet<u8>,
    known: HashSet<u8>,
    /// Running timers (link-up milliseconds left) of transfers that still send.
    timer: HashMap<(u8, u8), u64>,
}

struct Run<const B: usize, const L: usize, const T: usize> {
    f: Forwarder<B, L, T>,
    tr: Track,
    lines: Vec<String>,
    cover: HashSet<&'static str>,
}

fn snap<const B: usize, const L: usize, const T: usize>(f: &Forwarder<B, L, T>) -> String {
    let ch: Vec<String> = (1..=IDS)
        .map(|i| f.copies_held(&bid(i)).unwrap_or(0).to_string())
        .collect();
    let cd: Vec<String> = (1..=IDS).map(|i| f.copies_handed(&bid(i)).to_string()).collect();
    let tm: Vec<String> = (1..=IDS)
        .map(|i| {
            let row: Vec<String> = (1..=PEERS)
                .map(|p| f.timer_remaining(&node(p), &bid(i)).map_or(0, |r| r + 1).to_string())
                .collect();
            format!("[{}]", row.join(","))
        })
        .collect();
    format!(
        r#""ch":[{}],"cd":[{}],"tm":[{}]"#,
        ch.join(","),
        cd.join(","),
        tm.join(",")
    )
}

impl<const B: usize, const L: usize, const T: usize> Run<B, L, T> {
    fn new(policy: Policy, now: u64) -> Self {
        let lines = vec![format!(
            r#"{{"t":"fw","e":"new","b":{B},"l":{L},"tt":{T},"retry":{},"max":{},"now":{now}}}"#,
            policy.retry_ms, policy.max_sends
        )];
        Self {
            f: Forwarder::new(policy, now),
            tr: Track {
                now,
                policy,
                rcv: HashMap::new(),
                delivered: HashSet::new(),
                sends: HashMap::new(),
                up: HashSet::new(),
                known: HashSet::new(),
                timer: HashMap::new(),
            },
            lines,
            cover: HashSet::new(),
        }
    }

    fn forget(&mut self, id: u8) {
        self.tr.rcv.remove(&id);
        self.tr.delivered.remove(&id);
        self.tr.sends.retain(|(i, _), _| *i != id);
        self.tr.timer.retain(|(i, _), _| *i != id);
    }

    fn step(&mut self, now: u64, inp: Input) {
        if now < self.tr.now {
            self.cover.insert("back_in_time");
        }
        let dt = now.saturating_sub(self.tr.now);
        self.tr.now = self.tr.now.max(now);
        // Time is charged to the timers whose link was up before the input; a timer on a down link keeps its time.
        for ((_, p), r) in &mut self.tr.timer {
            if self.tr.up.contains(p) {
                *r = r.saturating_sub(dt);
            } else if dt > 0 {
                self.cover.insert("timer_frozen");
            }
        }
        let res = self.f.step(now, inp);
        match inp {
            Input::Tick => assert_eq!(res, Ok(())),
            Input::Hold(h) => {
                let id = id_of(&h.id);
                if h.copies == 0 {
                    assert_eq!(res, Err(ForwardError::NoCopies));
                    self.cover.insert("hold_nocopies");
                } else if self.tr.rcv.contains_key(&id) {
                    assert_eq!(res, Err(ForwardError::Duplicate), "a repeated hold is ignored");
                    self.cover.insert("hold_duplicate");
                } else if self.tr.rcv.len() == B {
                    assert_eq!(res, Err(ForwardError::Full));
                    self.cover.insert("hold_full");
                } else {
                    assert_eq!(res, Ok(()));
                    self.tr.rcv.insert(id, (h.copies, peer_of(&h.destination), h.expires));
                    self.cover.insert("hold_ok");
                }
            }
            Input::LinkUp(p) | Input::LinkDown(p) => {
                let (up, pn) = (matches!(inp, Input::LinkUp(_)), peer_of(&p));
                if !self.tr.known.contains(&pn) && self.tr.known.len() == L {
                    assert_eq!(res, Err(ForwardError::Full));
                    self.cover.insert("link_full");
                } else {
                    assert_eq!(res, Ok(()));
                    self.cover.insert(if self.tr.known.contains(&pn) {
                        "link_toggle"
                    } else {
                        "link_new"
                    });
                    self.tr.known.insert(pn);
                    if up {
                        self.tr.up.insert(pn);
                    } else {
                        self.tr.up.remove(&pn);
                    }
                }
            }
            Input::Acked { peer, bundle } => {
                let (id, p) = (id_of(&bundle), peer_of(&peer));
                if self.tr.sends.contains_key(&(id, p)) {
                    assert_eq!(res, Ok(()));
                    self.cover.insert("ack_ok");
                    self.tr.timer.remove(&(id, p));
                    if p == self.tr.rcv[&id].1 {
                        self.tr.delivered.insert(id);
                        self.cover.insert("ack_deliver");
                    }
                } else {
                    assert_eq!(res, Err(ForwardError::Unknown));
                    self.cover.insert("ack_unknown");
                }
            }
            Input::Forget(b) => {
                let id = id_of(&b);
                if self.tr.rcv.contains_key(&id) {
                    assert_eq!(res, Ok(()));
                    self.forget(id);
                    self.cover.insert("forget_ok");
                } else {
                    assert_eq!(res, Err(ForwardError::Unknown));
                    self.cover.insert("forget_unknown");
                }
            }
        }
        self.lines.push(format!(
            r#"{{"t":"fw","e":"step","now":{now},"in":{},"err":"{}",{}}}"#,
            input_json(&inp),
            err_name(res),
            snap(&self.f)
        ));
        self.check_books();
    }

    /// The copy balance per live bundle and the timers the tracker predicts.
    fn check_books(&self) {
        for id in 1..=IDS {
            if let Some((rcv, _, _)) = self.tr.rcv.get(&id) {
                let held = u32::from(self.f.copies_held(&bid(id)).expect("a live bundle is held"));
                let handed: u32 = self
                    .tr
                    .sends
                    .iter()
                    .filter(|((i, _), _)| *i == id)
                    .map(|(_, (_, g))| u32::from(*g))
                    .sum();
                assert_eq!(held + handed, u32::from(*rcv), "copies of bundle {id}");
                assert_eq!(self.f.copies_handed(&bid(id)), handed);
                assert!(held >= 1, "a holder keeps a copy");
            } else {
                assert_eq!(self.f.copies_held(&bid(id)), None);
                assert_eq!(self.f.copies_handed(&bid(id)), 0);
            }
            for p in 1..=PEERS {
                let seen = self.f.timer_remaining(&node(p), &bid(id));
                assert_eq!(seen, self.tr.timer.get(&(id, p)).copied(), "timer of ({id}, {p})");
            }
        }
    }

    /// Poll until quiet, or for at most `limit` actions.
    fn drain(&mut self, limit: u32) {
        for _ in 0..limit {
            if !self.poll() {
                return;
            }
        }
    }

    /// Transfers whose timer vanished from the forwarder have given up: that needs a timer of 0, the link up and
    /// the sends used. After a quiet poll nothing may be left that could send or give up.
    fn settle_gave_up(&mut self, quiet: bool) {
        let policy = self.tr.policy;
        let vanished: Vec<(u8, u8)> = self
            .tr
            .timer
            .keys()
            .copied()
            .filter(|k| self.f.timer_remaining(&node(k.1), &bid(k.0)).is_none())
            .collect();
        for k in vanished {
            assert_eq!(self.tr.timer[&k], 0);
            assert!(self.tr.up.contains(&k.1));
            assert!(self.tr.sends[&k].0 >= policy.max_sends, "gave up early");
            self.tr.timer.remove(&k);
            self.cover.insert("gave_up");
        }
        if quiet {
            for (k, r) in &self.tr.timer {
                assert!(!(*r == 0 && self.tr.up.contains(&k.1)), "a due transfer was left alone");
            }
        }
    }

    /// One poll, every effect checked against the tracker; whether an action came back.
    fn poll(&mut self) -> bool {
        let now = self.tr.now;
        let policy = self.tr.policy;
        let done: Vec<u8> = self
            .tr
            .rcv
            .iter()
            .filter(|(i, (_, _, exp))| self.tr.delivered.contains(i) || *exp <= now)
            .map(|(i, _)| *i)
            .collect();
        let act = self.f.poll();
        let line = match act {
            Some(Action::Release(b)) => {
                let id = id_of(&b);
                assert!(
                    done.contains(&id),
                    "released a bundle that is neither expired nor delivered"
                );
                self.cover.insert(if self.tr.delivered.contains(&id) {
                    "release_delivered"
                } else {
                    "release_expired"
                });
                self.forget(id);
                format!(r#"{{"k":"release","bundle":{id}}}"#)
            }
            Some(Action::Send {
                peer,
                bundle,
                copies,
                retransmit,
            }) => {
                assert!(done.is_empty(), "a send while a bundle is done");
                let (p, id) = (peer_of(&peer), id_of(&bundle));
                assert!(self.tr.up.contains(&p), "a send over a link that is down");
                let key = (id, p);
                if retransmit {
                    let (n, g) = self.tr.sends[&key];
                    assert_eq!(copies, g);
                    assert_eq!(self.tr.timer[&key], 0, "a retransmission before the timer ran out");
                    assert!(n < policy.max_sends, "a retransmission past the limit");
                    self.tr.sends.insert(key, (n + 1, g));
                    self.tr.timer.insert(key, policy.retry_ms);
                    self.cover.insert("send_retransmit");
                } else {
                    assert!(!self.tr.sends.contains_key(&key), "a second transfer to the same peer");
                    let held = self.f.copies_held(&bundle).unwrap();
                    if p == self.tr.rcv[&id].1 {
                        assert_eq!(copies, 0, "a delivery carries no copies");
                        self.cover.insert("send_deliver");
                    } else {
                        assert!(copies >= 1);
                        // The holder had `held + copies` before the send and handed half of it.
                        assert_eq!(copies, (held + copies) / 2);
                        self.cover.insert("send_spray");
                    }
                    self.tr.sends.insert(key, (1, copies));
                    self.tr.timer.insert(key, policy.retry_ms);
                }
                format!(r#"{{"k":"send","peer":{p},"bundle":{id},"copies":{copies},"retr":{retransmit}}}"#)
            }
            None => {
                assert!(done.is_empty(), "poll was quiet with a bundle done");
                self.settle_gave_up(true);
                self.check_quiet();
                r#"{"k":"none"}"#.to_string()
            }
        };
        if act.is_some() {
            self.settle_gave_up(false);
        }
        self.lines
            .push(format!(r#"{{"t":"fw","e":"poll","act":{line},{}}}"#, snap(&self.f)));
        self.check_books();
        act.is_some()
    }

    /// When poll is quiet: every live bundle with a link up has a transfer to that peer, or the peer is not its
    /// destination and a single copy is left, or the transfer table is full.
    fn check_quiet(&mut self) {
        for id in self.tr.rcv.keys().copied().collect::<Vec<_>>() {
            for &p in &self.tr.up.clone() {
                if self.tr.sends.contains_key(&(id, p)) {
                    continue;
                }
                let held = self.f.copies_held(&bid(id)).unwrap();
                if p != self.tr.rcv[&id].1 && held / 2 == 0 {
                    self.cover.insert("wait_single_copy");
                    continue;
                }
                assert_eq!(self.tr.sends.len(), T, "poll was quiet with work to do for ({id}, {p})");
                self.cover.insert("spray_blocked_by_full_table");
            }
        }
    }

    fn hold(&mut self, now: u64, id: u8, dest: u8, exp: u64, copies: u16) {
        self.step(
            now,
            Input::Hold(Held {
                id: bid(id),
                destination: node(dest),
                expires: exp,
                copies,
            }),
        );
    }

    /// A seeded random run of `steps` inputs. `tmax` bounds the time steps and the lifetimes, `base` the time origin.
    fn drive(&mut self, rng: &mut SplitMix64, steps: usize, base: u64) {
        let mut now = base;
        for _ in 0..steps {
            now = match rng.next_u64() % 12 {
                0 => now.saturating_sub(1 + rng.next_u64() % 5),
                1..=3 => now,
                _ => now.saturating_add(rng.next_u64() % 7).min(base.saturating_add(60)),
            };
            let node_n = |rng: &mut SplitMix64| 1 + (rng.next_u64() % u64::from(PEERS)) as u8;
            match rng.next_u64() % 100 {
                10..=29 => {
                    let id = 1 + (rng.next_u64() % u64::from(IDS)) as u8;
                    let dest = node_n(rng);
                    let exp = now.saturating_add(1 + rng.next_u64() % 40);
                    let copies = [0u16, 1, 2, 3, 4, 8, 5][(rng.next_u64() % 7) as usize];
                    self.hold(now, id, dest, exp, copies);
                }
                30..=49 => self.step(now, Input::LinkUp(node(node_n(rng)))),
                50..=59 => self.step(now, Input::LinkDown(node(node_n(rng)))),
                60..=77 => {
                    let known: Vec<(u8, u8)> = self.tr.sends.keys().copied().collect();
                    let (id, p) = if !known.is_empty() && rng.next_u64().is_multiple_of(2) {
                        known[(rng.next_u64() % known.len() as u64) as usize]
                    } else {
                        (1 + (rng.next_u64() % u64::from(IDS)) as u8, node_n(rng))
                    };
                    self.step(
                        now,
                        Input::Acked {
                            peer: node(p),
                            bundle: bid(id),
                        },
                    );
                }
                78..=82 => self.step(now, Input::Forget(bid(1 + (rng.next_u64() % u64::from(IDS)) as u8))),
                _ => self.step(now, Input::Tick),
            }
            match rng.next_u64() % 4 {
                0 => {}
                1 => self.drain(1),
                _ => self.drain(6),
            }
        }
        self.drain(16);
    }
}

fn write(name: &str, lines: &[String]) {
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = lines.join("\n");
        text.push('\n');
        std::fs::write(std::path::Path::new(&dir).join(format!("{name}.ndjson")), text).unwrap();
    }
}

#[test]
fn the_forwarder_matches_its_models() {
    let policy = Policy {
        retry_ms: 3,
        max_sends: 3,
    };
    let mut lines = vec![];
    let mut cover = HashSet::new();
    for seed in 0..40u64 {
        let mut run = Run::<2, 2, 2>::new(policy, 0);
        run.drive(&mut SplitMix64::new(seed), 70, 0);
        lines.append(&mut run.lines);
        cover.extend(run.cover);
    }
    for b in BRANCHES {
        assert!(cover.contains(b), "branch {b} was never met");
    }
    write("dtn_forward", &lines);
}

#[test]
fn other_capacities_policies_and_times_near_the_limit() {
    let mut lines = vec![];
    for (n, (retry, max)) in [(0u64, 0u8), (0, 1), (1, 1), (2, 5), (3, 2)].into_iter().enumerate() {
        let policy = Policy {
            retry_ms: retry,
            max_sends: max,
        };
        for seed in 0..6u64 {
            let s = seed + 100 * n as u64;
            let mut a = Run::<1, 1, 1>::new(policy, 0);
            a.drive(&mut SplitMix64::new(s), 60, 0);
            let mut b = Run::<3, 2, 4>::new(policy, 5);
            b.drive(&mut SplitMix64::new(s + 7), 60, 5);
            // Times next to u64::MAX: the clock saturates and timers never wrap.
            let mut c = Run::<2, 2, 2>::new(policy, u64::MAX - 80);
            c.drive(&mut SplitMix64::new(s + 13), 60, u64::MAX - 80);
            lines.append(&mut a.lines);
            lines.append(&mut b.lines);
            lines.append(&mut c.lines);
        }
    }
    write("dtn_forward_edge", &lines);
}
