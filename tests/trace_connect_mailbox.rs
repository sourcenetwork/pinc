//! Trace generation for the mailbox: seeded random runs of the real `Mailbox` through its public API, recorded as
//! ndjson (`connect_mailbox.ndjson`) for the TLA+ trace check (`TraceConnectMailbox.tla`) and the Lean replay
//! (`Vinc/TraceConnectMailbox.lean`).
//!
//! A run is one mailbox (members and bytes per member from the run's shape, the age from the run) driven by pushes of
//! bodies of every size (empty, one byte, a quarter of the quota, exactly the quota less the header, over it, over
//! the packet bound), pops (with and without a length limit), sweeps and clears, at times that step by 0 and by
//! amounts around the age. The test checks every answer against a plain reference queue written here, and the bytes
//! of every delivered body against what was stored (so the ring, with its wrap-around, is checked byte for byte).
//! What is recorded is what an observer sees: the answer, the held (messages, bytes) of the member, the counters.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    unreachable_pub
)]

mod connect_common;

use std::collections::{BTreeMap, VecDeque};
use std::fmt::Write as _;

use connect_common::nid;
use vinc_connect::carrier::MAX_PACKET_LEN;
use vinc_connect::mailbox::{ENTRY_HEAD, Mailbox, Push, Stats};
use vinc_tests::SplitMix64;

struct Msg {
    src: u8,
    flag: u8,
    body: Vec<u8>,
    t: u64,
    seq: u64,
}

/// The reference: a queue of messages per member, the rules of the module documentation.
struct Reference {
    b: usize,
    n: usize,
    age: u64,
    q: BTreeMap<u8, VecDeque<Msg>>,
    seq: u64,
    st: [u64; 7],
}

impl Reference {
    fn used(&self, k: u8) -> usize {
        self.q
            .get(&k)
            .map_or(0, |q| q.iter().map(|m| ENTRY_HEAD + m.body.len()).sum())
    }
    fn expire(&mut self, k: u8, now: u64) {
        let age = self.age;
        let mut n = 0;
        if let Some(q) = self.q.get_mut(&k) {
            while q.front().is_some_and(|m| now.saturating_sub(m.t) >= age) {
                q.pop_front();
                n += 1;
            }
        }
        self.st[4] += n;
    }
    fn push(&mut self, now: u64, k: u8, src: u8, flag: u8, body: &[u8]) -> Option<(u64, u32, bool)> {
        let size = ENTRY_HEAD + body.len();
        if body.is_empty() || body.len() > MAX_PACKET_LEN || size > self.b {
            self.st[5] += 1;
            return None;
        }
        if !self.q.contains_key(&k) && self.q.len() >= self.n {
            self.st[6] += 1;
            return None;
        }
        self.q.entry(k).or_default();
        self.expire(k, now);
        let first = self.q[&k].is_empty();
        let mut dropped = 0;
        while self.used(k) + size > self.b {
            let m = self.q.get_mut(&k).unwrap().pop_front().unwrap();
            self.st[2] += 1;
            self.st[3] += (ENTRY_HEAD + m.body.len()) as u64;
            dropped += 1;
        }
        let seq = self.seq;
        self.seq += 1;
        self.st[0] += 1;
        self.q.get_mut(&k).unwrap().push_back(Msg {
            src,
            flag,
            body: body.to_vec(),
            t: now,
            seq,
        });
        Some((seq, dropped, first))
    }
    fn pop(&mut self, now: u64, k: u8, max: usize) -> Option<Msg> {
        if !self.q.contains_key(&k) {
            return None;
        }
        self.expire(k, now);
        let q = self.q.get_mut(&k).unwrap();
        let out = if q.front().is_some_and(|m| m.body.len() <= max) {
            self.st[1] += 1;
            q.pop_front()
        } else {
            None
        };
        if q.is_empty() {
            self.q.remove(&k);
        }
        out
    }
    fn sweep(&mut self, now: u64) {
        let keys: Vec<u8> = self.q.keys().copied().collect();
        for k in keys {
            self.expire(k, now);
            if self.q[&k].is_empty() {
                self.q.remove(&k);
            }
        }
    }
    fn clear(&mut self, k: u8) {
        if let Some(q) = self.q.remove(&k) {
            self.st[4] += q.len() as u64;
        }
    }
}

fn stats_arr(s: Stats) -> [u64; 7] {
    [
        s.stored,
        s.delivered,
        s.dropped_oldest,
        s.dropped_oldest_bytes,
        s.expired,
        s.refused_oversize,
        s.refused_members,
    ]
}

fn st_json(s: [u64; 7]) -> String {
    format!("[{},{},{},{},{},{},{}]", s[0], s[1], s[2], s[3], s[4], s[5], s[6])
}

fn run<const N: usize, const B: usize>(seed: u64, age: u64, out: &mut Vec<String>) {
    let mut rng = SplitMix64::traced(seed);
    let mut m: Mailbox<N, B> = Mailbox::new(age, seed);
    let mut r = Reference {
        b: B,
        n: N,
        age,
        q: BTreeMap::new(),
        seq: 0,
        st: [0; 7],
    };
    out.push(format!(
        r#"{{"t":"mbnew","h":{ENTRY_HEAD},"b":{B},"n":{N},"age":{age},"maxpkt":{MAX_PACKET_LEN}}}"#
    ));
    let mut now = 0u64;
    for _ in 0..220 {
        let k = (rng.next_u64() % 3) as u8 + 1;
        now += match rng.next_u64() % 6 {
            0 => 0,
            1 => age.saturating_sub(1),
            2 => age,
            3 => age + 1,
            _ => rng.next_u64() % (age / 3 + 1),
        };
        match rng.next_u64() % 8 {
            0..=3 => {
                let len = match rng.next_u64() % 8 {
                    0 => 0,
                    1 => 1,
                    2 => (B - ENTRY_HEAD) / 4,
                    3 => B - ENTRY_HEAD,
                    4 => B - ENTRY_HEAD + 1,
                    5 => MAX_PACKET_LEN + 1,
                    _ => (rng.next_u64() % (B as u64 - ENTRY_HEAD as u64)) as usize + 1,
                };
                let src = 10 + (rng.next_u64() % 3) as u8;
                let flag = rng.next_u64() as u8;
                let body: Vec<u8> = (0..len).map(|i| (rng.next_u64() as u8) ^ (i as u8)).collect();
                let want = r.push(now, k, src, flag, &body);
                let got = m.push(now, &nid(k), &nid(src), flag, &body);
                let line = match (want, got) {
                    (
                        Some((seq, dropped, first)),
                        Push::Stored {
                            seq: s,
                            dropped: d,
                            first: f,
                        },
                    ) => {
                        assert_eq!((seq, dropped, first), (s, d, f));
                        format!(r#""res":"stored","seq":{s},"dropped":{d},"first":{f}"#)
                    }
                    (None, Push::TooLarge) => r#""res":"toolarge","seq":0,"dropped":0,"first":false"#.to_string(),
                    (None, Push::NoSlot) => r#""res":"noslot","seq":0,"dropped":0,"first":false"#.to_string(),
                    other => panic!("push: reference {:?}, code {:?}", other.0, other.1),
                };
                let (c, u) = m.pending(&nid(k));
                out.push(format!(
                    r#"{{"t":"mpush","now":{now},"node":{k},"src":{src},"flag":{flag},"len":{len},{line},"pc":{c},"pu":{u},"st":{}}}"#,
                    st_json(stats_arr(m.stats()))
                ));
            }
            4..=5 => {
                let max = if rng.next_u64().is_multiple_of(3) {
                    B / 4
                } else {
                    MAX_PACKET_LEN
                };
                let want = r.pop(now, k, max);
                let mut buf = [0u8; MAX_PACKET_LEN];
                let got = m.pop_fitting(now, &nid(k), &mut buf, max);
                let line = match (want, got) {
                    (Some(w), Some(g)) => {
                        assert_eq!(
                            (w.src, w.flag, w.body.len(), w.seq),
                            (g.src.bytes[0], g.flag, g.len, g.seq)
                        );
                        assert_eq!(w.body, buf[..g.len], "the ring returns the stored bytes");
                        assert!(now.saturating_sub(w.t) < age);
                        format!(
                            r#""got":true,"src":{},"flag":{},"len":{},"seq":{},"mt":{}"#,
                            w.src, w.flag, g.len, g.seq, w.t
                        )
                    }
                    (None, None) => r#""got":false,"src":0,"flag":0,"len":0,"seq":0,"mt":0"#.to_string(),
                    other => panic!("pop: reference {:?}, code {:?}", other.0.is_some(), other.1),
                };
                let (c, u) = m.pending(&nid(k));
                out.push(format!(
                    r#"{{"t":"mpop","now":{now},"node":{k},"max":{max},{line},"pc":{c},"pu":{u},"st":{}}}"#,
                    st_json(stats_arr(m.stats()))
                ));
            }
            6 => {
                r.sweep(now);
                m.sweep(now);
                out.push(format!(
                    r#"{{"t":"msweep","now":{now},"st":{}}}"#,
                    st_json(stats_arr(m.stats()))
                ));
            }
            _ => {
                r.clear(k);
                m.clear(&nid(k));
                out.push(format!(
                    r#"{{"t":"mclear","node":{k},"st":{}}}"#,
                    st_json(stats_arr(m.stats()))
                ));
            }
        }
        assert_eq!(stats_arr(m.stats()), r.st);
        assert_eq!(m.members(), r.q.len());
        for key in 1..=3u8 {
            let want = (r.q.get(&key).map_or(0, VecDeque::len), r.used(key));
            assert_eq!(m.pending(&nid(key)), want);
            assert!(want.1 <= B);
        }
    }
}

#[test]
fn the_mailbox_matches_the_reference_and_records_its_trace() {
    let mut out = Vec::new();
    for seed in 0..40u64 {
        match seed % 4 {
            0 => run::<2, 300>(seed, 20, &mut out),
            1 => run::<3, 200>(seed, 7, &mut out),
            2 => run::<1, 120>(seed, 50, &mut out),
            _ => run::<3, 1600>(seed, 15, &mut out),
        }
    }
    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut text = String::new();
    for l in &out {
        writeln!(text, "{l}").unwrap();
    }
    std::fs::write(dir.join("connect_mailbox.ndjson"), text).unwrap();
}
