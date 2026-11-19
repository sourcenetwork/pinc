//! Trace generation for the reach of a hub: the real `Topics` machines of a hub whose adjacency table holds three
//! records and four members, driven through the broadcast harness with the probes of the `trace` feature of
//! `pinc-broadcast` that read a member's record at the hub and run the reach timer alone. Members send their first
//! record, sessions come and go (each end names the peers it holds sessions with in a new record), members subscribe
//! and publish, a member leaves, and at the end the hub's timer expires the records. Every event is a line of
//! `bcast/reach.ndjson` for the TLA+ trace check (`TraceBroadcastReach.tla`): the action of the model; the last event
//! of each call carries the hub's record of every member and whether its table is closed. A fourth member's record
//! does not fit the table: it is refused and the table closes.
//!
//! The scripted run makes each case the model names; a seeded run of 60 actions among three members follows on the
//! same hub, then the sweep. The test asserts the facts it relies on itself: the fourth member's records are refused
//! and only the first closes the table, a message reaches a subscriber exactly when a chain of sessions links the two,
//! and after the sweep no record is live and no refused node waits. The trace is written to the directory in
//! `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_contains,
    clippy::manual_is_multiple_of
)]

#[path = "broadcast_common.rs"]
mod common;

use std::collections::BTreeSet;
use std::fmt::Write as _;

use common::{Ev, Net, SEC};
use pinc_broadcast::Limits;
use pinc_broadcast::consts::{REACH_RECORD_BASE, RECORD_TTL, REFRESH};
use pinc_crypto::IdentityAlg;
use pinc_tests::SplitMix64;

const T: &[u8] = b"reach";

struct World {
    net: Net,
    /// The sessions, as `(u, v)` with `u < v`.
    sessions: BTreeSet<(usize, usize)>,
    first: BTreeSet<usize>,
    subscribed: BTreeSet<usize>,
    left: BTreeSet<usize>,
    bodies: u32,
    out: String,
    refused_4: u32,
    closing_4: u32,
}

impl World {
    /// The hub's records and whether its table is closed.
    fn proj(&self) -> String {
        let t = &self.net.nodes[0].t;
        let recs: Vec<String> = (1..=4)
            .map(|n| {
                let (seq, live, peers) = t.reach_record(&self.net.id(n)).unwrap_or((0, false, Vec::new()));
                let mut ps: Vec<usize> = peers.iter().map(|p| self.member(p)).collect();
                ps.sort_unstable();
                let ps: Vec<String> = ps.iter().map(usize::to_string).collect();
                format!(r#"{{"seq":{seq},"live":{live},"peers":[{}]}}"#, ps.join(","))
            })
            .collect();
        format!(r#","tab":[{}],"shut":{}"#, recs.join(","), t.reach_stats().closed)
    }

    fn member(&self, id: &[u8; 32]) -> usize {
        (1..=4).find(|m| self.net.id(*m) == *id).unwrap()
    }

    fn event(&mut self, op: &str, keys: &str, last: bool) {
        let p = if last { self.proj() } else { String::new() };
        let _ = writeln!(self.out, r#"{{"t":"reach","op":"{op}"{keys}{p}}}"#);
    }

    fn peers_of(&self, x: usize) -> Vec<[u8; 32]> {
        self.sessions
            .iter()
            .filter_map(|(u, v)| match (*u == x, *v == x) {
                (true, _) => Some(self.net.id(*v)),
                (_, true) => Some(self.net.id(*u)),
                _ => None,
            })
            .collect()
    }

    /// Member `x` names the peers it holds sessions with; whether the hub refused the record and closed its table.
    fn record_call(&mut self, x: usize) -> (bool, bool) {
        let before = self.net.nodes[0].h.events.len();
        let (ids, now) = (self.peers_of(x), self.net.now);
        let n = &mut self.net.nodes[x];
        n.h.tick(now);
        n.t.set_adjacent(&mut n.h, now, &ids).unwrap();
        self.net.pump();
        let me = self.net.id(x);
        let evs = &self.net.nodes[0].h.events[before..];
        (
            evs.iter().any(|e| *e == Ev::ReachRefused(me)),
            evs.iter().any(|e| *e == Ev::ReachClosed),
        )
    }

    fn recv(&mut self, x: usize) {
        let (refused, closing) = self.record_call(x);
        if x == 4 {
            assert!(refused, "a record of member 4 was not refused");
            self.refused_4 += 1;
            self.closing_4 += u32::from(closing);
        } else {
            assert!(!refused && !closing, "a record of member {x} was refused");
        }
        self.event(
            "recv",
            &format!(r#","n":{x},"refused":{refused},"closing":{closing}"#),
            true,
        );
    }

    fn first_record(&mut self, x: usize) {
        assert!(self.first.insert(x));
        assert!(
            self.peers_of(x).is_empty(),
            "a member is in a session before its first record"
        );
        self.recv(x);
    }

    fn toggle(&mut self, u: usize, v: usize) {
        assert!(u < v && self.first.contains(&u) && self.first.contains(&v));
        assert!(!self.left.contains(&u) && !self.left.contains(&v));
        if !self.sessions.remove(&(u, v)) {
            self.sessions.insert((u, v));
        }
        self.event("toggle", &format!(r#","u":{u},"v":{v}"#), false);
        self.event("endturn", "", false);
        for x in [u, v] {
            self.event("report", &format!(r#","n":{x}"#), false);
            self.recv(x);
        }
        self.event("nextturn", "", false);
    }

    fn sub(&mut self, s: usize) {
        assert!(self.first.contains(&s));
        self.subscribed.insert(s);
        self.net.subscribe(s, T);
        self.event("sub", &format!(r#","s":{s}"#), true);
    }

    /// Whether a chain of sessions links `a` and `b`; member 4 has no record, so it is never linked.
    fn linked(&self, a: usize, b: usize) -> bool {
        let mut seen = BTreeSet::from([a]);
        let mut todo = vec![a];
        while let Some(x) = todo.pop() {
            for (u, v) in &self.sessions {
                let next = if *u == x {
                    *v
                } else if *v == x {
                    *u
                } else {
                    continue;
                };
                if next != 4 && x != 4 && seen.insert(next) {
                    todo.push(next);
                }
            }
        }
        seen.contains(&b)
    }

    fn publish(&mut self, o: usize) {
        self.bodies += 1;
        let mid = self.net.publish(o, T, format!("body{}", self.bodies).as_bytes());
        let targets: Vec<usize> = self
            .subscribed
            .iter()
            .copied()
            .filter(|s| *s != o && !self.left.contains(s))
            .collect();
        for (i, s) in targets.iter().enumerate() {
            let got = self.net.delivered(*s).contains(&mid);
            assert_eq!(got, self.linked(o, *s), "message of {o} to {s}: delivered {got}");
            self.event(
                "hand",
                &format!(r#","o":{o},"s":{s},"got":{got}"#),
                i + 1 == targets.len(),
            );
        }
    }

    fn leave(&mut self, x: usize) {
        assert!(
            self.peers_of(x).is_empty(),
            "member {x} leaves while it holds a session"
        );
        let id = self.net.id(x);
        let n0 = &mut self.net.nodes[0];
        n0.t.release(&mut n0.h, &id);
        self.net.pump();
        self.left.insert(x);
        self.event("leave", &format!(r#","n":{x}"#), true);
    }

    fn sweep(&mut self) {
        let live_before: Vec<bool> = (1..=4)
            .map(|n| self.net.nodes[0].t.reach_record(&self.net.id(n)).is_some_and(|r| r.1))
            .collect();
        let before = self.net.nodes[0].h.events.len();
        let t = self.net.now + RECORD_TTL + REFRESH + SEC;
        let n0 = &mut self.net.nodes[0];
        n0.h.tick(t);
        n0.t.reach_sweep(&mut n0.h, t);
        let opened = n0.h.events[before..].contains(&Ev::ReachOpened);
        let mut evs: Vec<(&str, String)> = Vec::new();
        for n in 1..=4usize {
            let now_live = self.net.nodes[0].t.reach_record(&self.net.id(n)).is_some_and(|r| r.1);
            if live_before[n - 1] && !now_live {
                evs.push(("expire", format!(r#","n":{n}"#)));
            }
        }
        if self.left.contains(&4) {
            evs.push(("drain", r#","n":4"#.to_owned()));
        }
        if opened {
            evs.push(("reopen", String::new()));
        }
        assert!(!evs.is_empty(), "the sweep did nothing");
        let last = evs.len() - 1;
        for (i, (op, keys)) in evs.iter().enumerate() {
            self.event(op, keys, i == last);
        }
        for n in 1..=4 {
            let live = self.net.nodes[0].t.reach_record(&self.net.id(n)).is_some_and(|r| r.1);
            assert!(!live, "the record of member {n} is live after the sweep");
        }
        let stats = self.net.nodes[0].t.reach_stats();
        assert_eq!(stats.waiting, 0, "a refused node still waits after the sweep");
        assert!(!stats.closed, "the table is closed after the sweep");
    }

    fn shut(&self) -> bool {
        self.net.nodes[0].t.reach_stats().closed
    }
}

fn scripted(w: &mut World) {
    for x in 1..=3 {
        w.first_record(x);
    }
    for s in 1..=3 {
        w.sub(s);
    }
    w.publish(1);
    w.toggle(1, 2);
    w.publish(1);
    w.toggle(2, 3);
    w.publish(3);
    w.toggle(1, 2);
    w.publish(1);
    w.publish(2);
    assert!(!w.shut());
    w.first_record(4);
    assert!(w.shut(), "the table is open after a refusal for want of room");
    w.sub(4);
    w.publish(1);
    w.publish(2);
    w.toggle(3, 4);
    w.publish(3);
    w.toggle(3, 4);
    assert!(w.shut());
    w.leave(4);
    assert_eq!(
        (w.refused_4, w.closing_4),
        (3, 1),
        "member 4's records were not all refused, or closed the table twice"
    );
}

fn seeded(w: &mut World) {
    let mut rng = SplitMix64::traced(0x5747_0008);
    for _ in 0..60 {
        if rng.next_u64() % 2 == 0 {
            let (u, v) = [(1, 2), (1, 3), (2, 3)][usize::try_from(rng.next_u64() % 3).unwrap()];
            w.toggle(u, v);
        } else {
            w.publish(usize::try_from(1 + rng.next_u64() % 3).unwrap());
        }
    }
}

#[test]
fn reach_trace() {
    assert_eq!(REACH_RECORD_BASE, 256);
    let mut net = Net::with_limits(
        &[IdentityAlg::Ed25519; 5],
        1,
        SEC,
        Limits {
            reach_bytes: 1248,
            ..Limits::default()
        },
    );
    for i in 1..=4 {
        net.attach(i);
    }
    let mut w = World {
        net,
        sessions: BTreeSet::new(),
        first: BTreeSet::new(),
        subscribed: BTreeSet::new(),
        left: BTreeSet::new(),
        bodies: 0,
        out: String::new(),
        refused_4: 0,
        closing_4: 0,
    };
    scripted(&mut w);
    seeded(&mut w);
    w.sweep();
    assert!(w.out.lines().count() > 200);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("reach.ndjson"), &w.out).unwrap();
    }
}
