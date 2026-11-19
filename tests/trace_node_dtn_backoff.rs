//! Trace generation for the backoff of the node's delay-tolerant dials: seeded runs of the node's own table
//! (`lfailed`) and redial time (`pinc-node`, built with the `trace` feature, through `DtnBackoffProbe`), recorded as
//! ndjson (`dtn_backoff.ndjson`) for the TLA+ trace check (`TraceNodeDtnBackoff.tla`).
//!
//! The calls are the node's own: `failed` (a delay-tolerant dial failed: the wait doubles from 2 s to 60 s, the entry
//! is stored when the table has room or holds the peer, the redial time is the earlier of itself and the end of the
//! wait), `waits` (the check `dial_layer` makes), `forget` (a membership event about the peer) and `fire` (the timer
//! check of the redial time). Runs: a peer failing eight times, the two sequences in which a peer is left waiting
//! with no redial time after the timer fired (recorded, nothing asserted about them beyond the rules of each call),
//! forgetting, the top of the clock, a full table, and seeded random runs.
//!
//! The test compares every call with a naive table (a map and an optional redial time, written from the docs) and
//! checks that the table never holds more than 4096 entries.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::match_same_arms
)]

use std::collections::BTreeMap;
use std::fmt::Write as _;

use pinc_node::DtnBackoffProbe;
use pinc_tests::SplitMix64;

const MAX: usize = DtnBackoffProbe::TABLE_MAX;
const FIRST: u64 = DtnBackoffProbe::FIRST;
const CAP: u64 = DtnBackoffProbe::CAP;
const S: u64 = 1_000_000_000;

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn opt(v: Option<u64>) -> String {
    v.map_or_else(|| "[]".to_string(), limbs)
}

fn entry(e: Option<(u64, u64)>) -> String {
    e.map_or_else(|| "[]".to_string(), |(u, b)| format!("[{},{}]", limbs(u), limbs(b)))
}

/// The id of peer number `n`.
fn peer(n: u32) -> [u8; 32] {
    let mut id = [0x11u8; 32];
    id[..4].copy_from_slice(&n.to_le_bytes());
    id
}

fn number(id: &[u8; 32]) -> u32 {
    u32::from_le_bytes(id[..4].try_into().unwrap())
}

struct Run {
    p: DtnBackoffProbe,
    t: BTreeMap<u32, (u64, u64)>,
    redial: Option<u64>,
    out: String,
}

impl Run {
    fn new(mut out: String, peers: u32) -> Self {
        writeln!(
            out,
            "{{\"t\":\"dtnb\",\"op\":\"init\",\"max\":{MAX},\"first\":{},\"cap\":{},\"peers\":{peers}}}",
            limbs(FIRST),
            limbs(CAP)
        )
        .unwrap();
        Self {
            p: DtnBackoffProbe::new(),
            t: BTreeMap::new(),
            redial: None,
            out,
        }
    }

    fn entry_of(&self, n: u32) -> Option<(u64, u64)> {
        let e = self.p.entry(&peer(n));
        assert_eq!(e, self.t.get(&n).copied(), "entry of peer {n}");
        e
    }

    /// A dial of peer `n` failed at `now`; returns the end of the wait.
    fn fail(&mut self, now: u64, n: u32) -> u64 {
        let at = self.p.failed(now, &peer(n));
        let back = self.t.get(&n).map_or(FIRST, |(_, b)| b.saturating_mul(2).min(CAP));
        if self.t.len() < MAX || self.t.contains_key(&n) {
            self.t.insert(n, (now.saturating_add(back), back));
        }
        let end = now.saturating_add(back);
        self.redial = Some(self.redial.map_or(end, |r| r.min(end)));
        assert_eq!(at, end, "end of the wait of peer {n} at {now}");
        assert_eq!(
            self.p.redial_at(),
            self.redial,
            "redial time after peer {n} failed at {now}"
        );
        assert_eq!(self.p.len(), self.t.len(), "length");
        assert!(self.p.len() <= MAX, "the table passed {MAX} entries");
        let e = self.entry_of(n);
        writeln!(
            self.out,
            "{{\"t\":\"dtnb\",\"op\":\"fail\",\"now\":{},\"peer\":{n},\"at\":{},\"e\":{},\"len\":{},\"redial\":{}}}",
            limbs(now),
            limbs(at),
            entry(e),
            self.p.len(),
            opt(self.p.redial_at())
        )
        .unwrap();
        at
    }

    fn waits(&mut self, now: u64, n: u32) -> bool {
        let r = self.p.waits(now, &peer(n));
        assert_eq!(
            r,
            self.t.get(&n).is_some_and(|(u, _)| now < *u),
            "waits of peer {n} at {now}"
        );
        let e = self.entry_of(n);
        writeln!(
            self.out,
            "{{\"t\":\"dtnb\",\"op\":\"waits\",\"now\":{},\"peer\":{n},\"r\":{r},\"e\":{}}}",
            limbs(now),
            entry(e)
        )
        .unwrap();
        r
    }

    fn forget(&mut self, n: u32) {
        self.p.forget(&peer(n));
        self.t.remove(&n);
        assert_eq!(self.p.len(), self.t.len(), "length after forgetting peer {n}");
        writeln!(
            self.out,
            "{{\"t\":\"dtnb\",\"op\":\"forget\",\"peer\":{n},\"len\":{}}}",
            self.p.len()
        )
        .unwrap();
    }

    fn fire(&mut self, now: u64) -> bool {
        let r = self.p.fire(now);
        let want = self.redial.is_some_and(|t| now >= t);
        if want {
            self.redial = None;
        }
        assert_eq!(r, want, "fire at {now}");
        assert_eq!(self.p.redial_at(), self.redial, "redial time after the timer at {now}");
        writeln!(
            self.out,
            "{{\"t\":\"dtnb\",\"op\":\"fire\",\"now\":{},\"r\":{r},\"redial\":{}}}",
            limbs(now),
            opt(self.p.redial_at())
        )
        .unwrap();
        r
    }

    fn dump(&mut self) {
        let all = self.p.entries();
        let want: Vec<_> = self.t.iter().map(|(n, (u, b))| (*n, *u, *b)).collect();
        let got: Vec<_> = all.iter().map(|(id, u, b)| (number(id), *u, *b)).collect();
        assert_eq!(got.len(), want.len(), "dump length");
        let mut sorted = got;
        sorted.sort_unstable();
        assert_eq!(sorted, want, "dump");
        let list = want
            .iter()
            .map(|(n, u, b)| format!("[{n},{},{}]", limbs(*u), limbs(*b)))
            .collect::<Vec<_>>()
            .join(",");
        writeln!(self.out, "{{\"t\":\"dtnb\",\"op\":\"dump\",\"entries\":[{list}]}}").unwrap();
    }
}

/// Run 1: one peer fails eight times; r picks when each failure comes.
fn doubling(r: u64, out: String) -> String {
    let mut run = Run::new(out, 1);
    let mut now = 5 * S;
    let mut until = 0;
    let waits = [2, 4, 8, 16, 32, 60, 60, 60].map(|s| s * S);
    for (i, want) in waits.into_iter().enumerate() {
        now = match r {
            0 => now,
            1 if i > 0 => now + S,
            2 => now.max(until),
            3 => now.max(until + 1),
            _ => now,
        };
        until = run.fail(now, 1);
        assert_eq!(run.entry_of(1).map(|e| e.1), Some(want), "wait of failure {i}");
        for t in [until - 1, until, until + 1] {
            let w = run.waits(t, 1);
            assert_eq!(w, t < until, "waits at {t}");
        }
    }
    run.finish()
}

/// Run 2: the two sequences that leave a peer waiting with no redial time after the timer fired. Recorded as they are.
fn lost_redial(r: u64, out: String) -> String {
    let base = r * 7 * S;
    let mut run = Run::new(out, 2);
    if r % 2 == 0 {
        run.fail(base, 1);
        run.fail(base + S, 2);
        run.fire(base + 2 * S);
        run.waits(base + 2 * S, 2);
        run.fire(base + 3 * S);
    } else {
        run.fail(base, 1);
        run.fail(base + S, 1);
        run.fire(base + 2 * S);
        run.waits(base + 2 * S, 1);
        run.fire(base + 5 * S);
    }
    run.finish()
}

/// Run 3: failures of three peers, forgotten in turn.
fn forgetting(r: u64, out: String) -> String {
    let mut run = Run::new(out, 3);
    let mut now = r * S;
    for n in 1..=3 {
        run.fail(now, n);
        run.fail(now, n);
        now += S;
    }
    for n in [1u32, 3, 2] {
        run.forget(n);
        assert!(!run.waits(now, n), "peer {n} still waits after it was forgotten");
        let at = run.fail(now, n);
        assert_eq!(at, now + FIRST, "a failure after a forget does not start again");
        now += S;
    }
    run.dump();
    run.finish()
}

/// Run 4: the top of the clock's range.
fn top(r: u64, out: String) -> String {
    let mut run = Run::new(out, 2);
    for (i, now) in [u64::MAX - 3 * S, u64::MAX - 1, u64::MAX].into_iter().enumerate() {
        let n = if r == 1 { 1 + (i as u32 % 2) } else { 1 };
        let at = run.fail(now, n);
        if now >= u64::MAX - 1 {
            assert_eq!(at, u64::MAX, "the end of the wait did not saturate");
        }
    }
    assert!(
        !run.waits(u64::MAX, 1),
        "a wait that ends at the top still waits at the top"
    );
    run.finish()
}

/// Run 5: a full table.
fn full(r: u64, out: String) -> String {
    let mut run = Run::new(out, MAX as u32 + 1);
    for n in 1..=MAX as u32 {
        run.fail(if r == 0 { 0 } else { u64::from(n) }, n);
    }
    run.dump();
    let now = MAX as u64 + 10;
    let before = run.redial;
    run.fail(now, MAX as u32 + 1);
    assert_eq!(run.entry_of(MAX as u32 + 1), None, "a full table stored a new peer");
    assert_eq!(run.p.len(), MAX);
    assert_eq!(run.redial, before, "the redial time moved");
    run.fail(now + 1, 5);
    assert_eq!(
        run.entry_of(5).map(|e| e.1),
        Some(2 * FIRST),
        "a held peer's wait did not double"
    );
    assert!(!run.waits(now + 1, MAX as u32 + 1));
    run.forget(1);
    run.fail(now + 2, MAX as u32 + 1);
    assert!(run.entry_of(MAX as u32 + 1).is_some(), "a freed place was not used");
    run.dump();
    run.finish()
}

impl Run {
    fn finish(self) -> String {
        self.out
    }
}

/// Run 6: seeded random calls.
fn random(r: u64, out: String) -> String {
    let mut rng = SplitMix64::new(0x6474_6200 + r);
    let peers = 2 + (rng.next_u64() % 7) as u32;
    let mut run = Run::new(out, peers);
    let mut now = 0u64;
    for step in 0..300 {
        now = match rng.next_u64() % 50 {
            0 => now.max(u64::MAX - rng.next_u64() % (4 * S)),
            _ => now.saturating_add(match rng.next_u64() % 5 {
                0 => 0,
                1 => 1,
                2 => 500_000_000,
                3 => 2 * S,
                _ => rng.next_u64() % (120 * S),
            }),
        };
        let n = 1 + (rng.next_u64() % u64::from(peers)) as u32;
        match rng.next_u64() % 6 {
            0..=2 => {
                run.fail(now, n);
            }
            3 => {
                run.waits(now, n);
            }
            4 => run.forget(n),
            _ => {
                run.fire(now);
            }
        }
        if step % 50 == 49 {
            run.dump();
        }
    }
    run.dump();
    run.finish()
}

#[test]
fn dtn_backoff() {
    let mut out = String::new();
    for r in 0..4 {
        out = doubling(r, out);
    }
    for r in 0..4 {
        out = lost_redial(r, out);
    }
    for r in 0..4 {
        out = forgetting(r, out);
    }
    for r in 0..2 {
        out = top(r, out);
    }
    for r in 0..2 {
        out = full(r, out);
    }
    for r in 0..40 {
        out = random(r, out);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dtn_backoff.ndjson"), &out).unwrap();
    }
}
