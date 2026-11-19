//! Trace generation for a hub pushing a topic over streams that fill up: the real `Topics` machine of a hub with a log
//! of three messages and two subscribers whose streams take two frames each, driven through its public API
//! (`frame`, `peer_writable`) with the probes of the `trace` feature of `pinc-broadcast` that read the log's bounds
//! and a subscriber's place. The test holds every frame between the hub and the others: a stream is a queue of the
//! frames the hub sent, drained one at a time (the host's room grows by one), and a publish is handed to the hub when
//! the test chooses, again after a refusal. Every event is one line of `bcast/push.ndjson` for the TLA+ trace check
//! (`TraceBroadcastPush.tla`): a store, a refusal (the hub would evict a message still owed), a duplicate, a drain,
//! and the pushes a writable stream resumes; after each, the log's positions, each subscriber's place and each
//! stream. Time never moves, so no subscriber is let go.
//!
//! The scripted run makes each case the model names; a seeded run of 250 actions follows on the same hub. The test
//! asserts the facts it relies on itself: every logged message costs the same bytes, a refusal sends no acknowledgement
//! and changes nothing, a store sends one, each subscriber is sent every acknowledged message once in order, and the
//! script reached a refusal, an eviction, each subscriber behind, and a writable that sent one frame and one that sent
//! none. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    unreachable_pub
)]

#[path = "broadcast_common.rs"]
mod common;

use std::collections::{HashMap, VecDeque};
use std::fmt::Write as _;

use common::{Net, Out, SEC, ty};
use pinc_broadcast::Limits;
use pinc_broadcast::wire::MAX_HEAD;
use pinc_crypto::IdentityAlg;
use pinc_membership::NodeId;
use pinc_tests::SplitMix64;

const T: &[u8] = b"push";
/// The most messages of the run: the model's `N`.
const MESSAGES: u32 = 40;

fn body(m: u32) -> Vec<u8> {
    vec![m as u8; MAX_HEAD.div_ceil(2)]
}

/// A message handed to the hub: the frame type and the frame's bytes after the topic.
struct Msg {
    ty: u8,
    rest: Vec<u8>,
}

struct Push {
    net: Net,
    /// The bytes one logged message takes in the ring.
    l: usize,
    msgs: Vec<Msg>,
    number: HashMap<[u8; 8], u32>,
    /// The message numbers of the frames in each subscriber's stream, oldest first.
    stream: [VecDeque<u32>; 2],
    /// Every frame each subscriber was ever sent, in order.
    sent: [Vec<u32>; 2],
    /// The messages the hub acknowledged, in order.
    acked: Vec<u32>,
    /// The messages the hub refused and that were not stored since, oldest first.
    refused: VecDeque<u32>,
    out: String,
    // what the run reached
    refusals: u32,
    evictions: u32,
    behind: [u32; 2],
    writable_one: u32,
    writable_none: u32,
}

fn arr(v: &[u32]) -> String {
    let s: Vec<String> = v.iter().map(u32::to_string).collect();
    format!("[{}]", s.join(","))
}

impl Push {
    fn new() -> Self {
        let limits = Limits {
            max_body: MAX_HEAD.div_ceil(2),
            log_bytes: 1 << 20,
            ..Limits::default()
        };
        let calibrate = |limits| {
            let mut net = Net::with_limits(&[IdentityAlg::Ed25519; 4], 1, SEC, limits);
            for i in 1..=3 {
                net.attach(i);
            }
            net.subscribe(1, T);
            net.subscribe(2, T);
            net
        };
        let mut cal = calibrate(limits);
        cal.publish(3, T, &body(1));
        let l = cal.nodes[0].t.log_bounds(T).2;
        assert!(l > 0, "the calibration logged nothing");
        assert!(
            MAX_HEAD.div_ceil(2) + MAX_HEAD <= 3 * l,
            "three messages do not fit three of the ring"
        );
        let mut net = calibrate(Limits {
            log_bytes: 3 * l,
            ..limits
        });
        for s in 1..=2 {
            let id = net.id(s);
            net.nodes[0].h.room.insert(id, 2);
        }
        net.nodes[0].h.out.clear();
        Self {
            net,
            l,
            msgs: Vec::new(),
            number: HashMap::new(),
            stream: [VecDeque::new(), VecDeque::new()],
            sent: [Vec::new(), Vec::new()],
            acked: Vec::new(),
            refused: VecDeque::new(),
            out: String::new(),
            refusals: 0,
            evictions: 0,
            behind: [0; 2],
            writable_one: 0,
            writable_none: 0,
        }
    }

    fn id(&self, i: usize) -> NodeId {
        self.net.id(i)
    }

    /// The projection after an event, as the trace spec reads it; notes what the state reached.
    fn proj(&mut self) -> String {
        let t = &self.net.nodes[0].t;
        let (base, end, _) = t.log_bounds(T);
        let behind: Vec<u64> = (1..=2)
            .map(|s| match t.push_place(T, &self.net.id(s)) {
                Some((next, _)) if next < end => next + 1,
                _ => 0,
            })
            .collect();
        for (n, b) in self.behind.iter_mut().zip(&behind) {
            *n += u32::from(*b > 0);
        }
        let stream: Vec<String> = self
            .stream
            .iter()
            .map(|q| arr(&q.iter().copied().collect::<Vec<_>>()))
            .collect();
        format!(
            r#""top":{end},"base":{},"behind":[{},{}],"stream":[{}]"#,
            base + 1,
            behind[0],
            behind[1],
            stream.join(",")
        )
    }

    fn event(&mut self, op: &str, keys: &str) {
        let p = self.proj();
        let _ = writeln!(self.out, r#"{{"t":"push","op":"{op}"{keys},{p}}}"#);
    }

    /// A new message from the publisher, not yet handed to the hub: its number.
    fn make(&mut self) -> u32 {
        let m = u32::try_from(self.msgs.len()).unwrap() + 1;
        let (hub, now) = (self.id(0), self.net.now);
        let n3 = &mut self.net.nodes[3];
        n3.h.tick(now);
        let mid = n3.t.publish(&mut n3.h, now, T, &body(m)).unwrap();
        let f = n3.h.out.iter().find(|o| o.to == hub).unwrap().bytes.clone();
        n3.h.out.clear();
        self.msgs.push(Msg {
            ty: f[4],
            rest: f[6 + T.len()..].to_vec(),
        });
        self.number.insert(mid, m);
        m
    }

    /// File the frames the hub sent to the subscribers into their streams; how many acknowledgements it sent, and how
    /// many frames went to `only`.
    fn collect(&mut self, out: Vec<Out>, only: usize) -> (usize, usize) {
        let (publisher, subs) = (self.id(3), [self.id(1), self.id(2)]);
        let (mut packs, mut to_only) = (0, 0);
        for o in out {
            if o.to == publisher && o.bytes[4] == ty::PACK {
                packs += 1;
            }
            let Some(s) = subs.iter().position(|x| *x == o.to) else {
                continue;
            };
            assert_eq!(o.bytes[4], ty::MSG, "the hub sent a subscriber something but a message");
            let at = 6 + T.len();
            let m = self.number[&<[u8; 8]>::try_from(&o.bytes[at..at + 8]).unwrap()];
            self.stream[s].push_back(m);
            self.sent[s].push(m);
            to_only += usize::from(s + 1 == only);
        }
        (packs, to_only)
    }

    /// Hand message `m` to the hub.
    fn hand(&mut self, m: u32) {
        let (publisher, now) = (self.id(3), self.net.now);
        let (ty, rest) = {
            let msg = &self.msgs[usize::try_from(m).unwrap() - 1];
            (msg.ty, msg.rest.clone())
        };
        let before = self.net.nodes[0].t.log_bounds(T);
        let n0 = &mut self.net.nodes[0];
        n0.h.out.clear();
        n0.h.tick(now);
        n0.t.frame(&mut n0.h, now, &publisher, ty, T, &rest);
        let out = std::mem::take(&mut n0.h.out);
        let (packs, _) = self.collect(out, 0);
        let after = self.net.nodes[0].t.log_bounds(T);
        let (op, keys) = if self.acked.contains(&m) {
            ("dup", format!(r#","m":{m}"#))
        } else if packs > 0 {
            assert_eq!(packs, 1, "a store sent more than one acknowledgement");
            assert_eq!(
                after.2,
                self.l * usize::try_from(after.1 - after.0).unwrap(),
                "a log entry is not one size"
            );
            self.evictions += u32::from(after.0 > before.0);
            self.acked.push(m);
            self.refused.retain(|r| *r != m);
            ("store", format!(r#","m":{m},"pack":true"#))
        } else {
            assert_eq!(before, after, "a refused hand-over changed the log");
            self.refusals += 1;
            if !self.refused.contains(&m) {
                self.refused.push_back(m);
            }
            ("refused", format!(r#","m":{m},"pack":false"#))
        };
        self.event(op, &keys);
    }

    /// A new message, handed at once.
    fn store_new(&mut self) {
        let m = self.make();
        self.hand(m);
    }

    /// Stream `s` (1 or 2) delivers its oldest frame and the host wakes the hub.
    fn drain(&mut self, s: usize) {
        self.stream[s - 1].pop_front().unwrap();
        let (id, now) = (self.id(s), self.net.now);
        *self.net.nodes[0].h.room.get_mut(&id).unwrap() += 1;
        self.event("drain", &format!(r#","s":{s}"#));
        let n0 = &mut self.net.nodes[0];
        n0.h.out.clear();
        n0.h.tick(now);
        n0.t.peer_writable(&mut n0.h, now, &id);
        let out = std::mem::take(&mut n0.h.out);
        let (_, n) = self.collect(out, s);
        match n {
            0 => self.writable_none += 1,
            1 => self.writable_one += 1,
            _ => {}
        }
        self.event("writable", &format!(r#","s":{s},"n":{n}"#));
    }

    fn drain_all(&mut self) {
        while self.stream.iter().any(|q| !q.is_empty()) {
            for s in 1..=2 {
                if !self.stream[s - 1].is_empty() {
                    self.drain(s);
                }
            }
        }
    }

    fn check_sent(&self) {
        for s in 0..2 {
            assert_eq!(
                self.sent[s],
                self.acked,
                "subscriber {} was not sent every acknowledged message once",
                s + 1
            );
        }
    }
}

fn scripted(p: &mut Push) {
    p.store_new();
    p.store_new();
    p.store_new();
    p.store_new();
    p.store_new();
    let six = p.make();
    p.hand(six);
    for _ in 0..2 {
        p.drain(1);
    }
    p.hand(six);
    for _ in 0..2 {
        p.drain(2);
    }
    p.hand(six);
    p.hand(2);
    p.drain_all();
    p.check_sent();
    assert!(p.refusals >= 1, "the script reached no refusal");
    assert!(p.evictions >= 1, "the script reached no eviction");
    assert!(p.behind.iter().all(|b| *b > 0), "a subscriber was never behind");
    assert!(
        p.writable_one >= 1 && p.writable_none >= 1,
        "the script lacks a writable of one frame or of none"
    );
}

fn seeded(p: &mut Push) {
    let mut rng = SplitMix64::traced(0x5747_0005);
    for _ in 0..250 {
        let r = rng.next_u64() % 10;
        let nonempty: Vec<usize> = (1..=2).filter(|s| !p.stream[*s - 1].is_empty()).collect();
        if r < 4 || (r >= 5 && nonempty.is_empty()) {
            if let Some(m) = p.refused.front().copied() {
                p.hand(m);
            } else if u32::try_from(p.msgs.len()).unwrap() < MESSAGES {
                p.store_new();
            } else if let Some(m) = p.acked.last().copied() {
                p.hand(m);
            }
        } else if r == 4 {
            if !p.acked.is_empty() {
                let m = p.acked[usize::try_from(rng.next_u64()).unwrap() % p.acked.len()];
                p.hand(m);
            }
        } else {
            let s = nonempty[usize::try_from(rng.next_u64()).unwrap() % nonempty.len()];
            p.drain(s);
        }
    }
    p.drain_all();
    p.check_sent();
}

#[test]
fn push_trace() {
    let mut p = Push::new();
    scripted(&mut p);
    seeded(&mut p);
    assert!(p.out.lines().count() > 300);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        let dir = std::path::Path::new(&dir).join("bcast");
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("push.ndjson"), &p.out).unwrap();
    }
}
