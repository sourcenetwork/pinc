//! Trace generation for the bound on the node's timer: seeded runs of a real `Bound` (`pinc-node`, built with the
//! `trace` feature, through `timers_probe::TimerProbe`), recorded as ndjson (`timer_bound.ndjson`) for the TLA+ trace
//! check (`TraceNodeTimerBound.tla`).
//!
//! A run is a series of timer calls, each given the nine deadlines the layers left (as free inputs: what a layer
//! names is covered by the layers' own models) and followed by answers for some deadline of the layers. The runs
//! are layers that move their deadlines (one of them asks to be called again at once, and the next call moves it),
//! one and two layers that leave a deadline due for 3 to 6 calls, the top of the clock's range, time going back and
//! seeded random deadlines.
//!
//! The test keeps a naive account of its own (the time and the due flags of the last call) and checks each call
//! against it: the flags, the held time, the counters and their total, and the answer.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    unreachable_pub,
    clippy::redundant_closure_for_method_calls
)]

use std::fmt::Write as _;

use pinc_node::timers_probe::{TICK, TIMERS, TimerProbe};
use pinc_tests::SplitMix64;

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

fn list<T>(v: &[T], f: impl Fn(&T) -> String) -> String {
    format!("[{}]", v.iter().map(f).collect::<Vec<_>>().join(","))
}

/// A probe with the naive account of the bound beside it.
struct Run {
    probe: TimerProbe,
    out: String,
    last: Option<u64>,
    left: [bool; TIMERS],
    stuck: [u64; TIMERS],
    held: Option<u64>,
}

impl Run {
    fn new(out: String) -> Self {
        let mut out = out;
        writeln!(
            out,
            "{{\"t\":\"tb\",\"op\":\"init\",\"n\":{TIMERS},\"tick\":{}}}",
            limbs(TICK)
        )
        .unwrap();
        Self {
            probe: TimerProbe::new(),
            out,
            last: None,
            left: [false; TIMERS],
            stuck: [0; TIMERS],
            held: None,
        }
    }

    /// A timer call at `now` that left `dues`; returns the flags.
    fn call(&mut self, now: u64, dues: [Option<u64>; TIMERS]) -> [bool; TIMERS] {
        let flags = self.probe.check(now, dues);
        let mut want = [false; TIMERS];
        let mut any = false;
        let last = self.last.replace(now);
        for i in 0..TIMERS {
            let due = dues[i].filter(|d| *d <= now);
            let stuck = self.left[i] && last.is_some_and(|l| due.is_some_and(|d| d <= l));
            self.left[i] = due.is_some();
            if stuck {
                want[i] = self.stuck[i] == 0;
                self.stuck[i] += 1;
                any = true;
            }
        }
        self.held = any.then(|| now.saturating_add(TICK));
        assert_eq!(flags, want, "flags at {now} for {dues:?}");
        assert_eq!(self.probe.held(), self.held, "held at {now} for {dues:?}");
        assert_eq!(self.probe.stuck(), self.stuck, "counters at {now} for {dues:?}");
        assert_eq!(self.probe.total(), self.stuck.iter().sum::<u64>(), "total at {now}");
        assert!(self.stuck.iter().all(|n| *n < 1 << 31), "a counter reached 2^31");
        writeln!(
            self.out,
            "{{\"t\":\"tb\",\"op\":\"check\",\"now\":{},\"dues\":{},\"first\":{},\"held\":{},\"stats\":{}}}",
            limbs(now),
            list(&dues, |d| opt(*d)),
            list(&flags, |b| b.to_string()),
            opt(self.probe.held()),
            list(&self.probe.stuck(), u64::to_string)
        )
        .unwrap();
        flags
    }

    fn answer(&mut self, due: Option<u64>) {
        let r = self.probe.answer(due);
        assert_eq!(
            r,
            due.map(|d| self.held.map_or(d, |h| d.max(h))),
            "answer for {due:?} held {:?}",
            self.held
        );
        if let (Some(h), Some(x)) = (self.held, r) {
            assert!(x >= h, "answer {x} is before the held time {h}");
        }
        writeln!(
            self.out,
            "{{\"t\":\"tb\",\"op\":\"answer\",\"due\":{},\"r\":{}}}",
            opt(due),
            opt(r)
        )
        .unwrap();
    }

    /// The answers after a call: none, the earliest deadline, and the held time and its neighbours.
    fn answers(&mut self, dues: &[Option<u64>; TIMERS]) {
        self.answer(None);
        self.answer(dues.iter().flatten().copied().min());
        if let Some(h) = self.held {
            for d in [h.saturating_sub(1), h, h.saturating_add(1)] {
                self.answer(Some(d));
            }
        }
    }

    fn finish(mut self) -> String {
        writeln!(
            self.out,
            "{{\"t\":\"tb\",\"op\":\"stats\",\"stuck\":{},\"total\":{}}}",
            list(&self.probe.stuck(), u64::to_string),
            self.probe.total()
        )
        .unwrap();
        self.out
    }
}

/// What a layer that keeps the contract names: nothing, a later time, or the time of the call once (`asks`), which
/// the next call moves to a later time.
fn good(rng: &mut SplitMix64, now: u64, asks: &mut bool) -> Option<u64> {
    if std::mem::take(asks) {
        return Some(now + 1 + rng.next_u64() % 1_000_000_000);
    }
    match rng.next_u64() % 3 {
        0 => None,
        1 => Some(now + 1 + rng.next_u64() % 1_000_000_000),
        _ => {
            *asks = true;
            Some(now)
        }
    }
}

fn step(rng: &mut SplitMix64) -> u64 {
    match rng.next_u64() % 4 {
        0 => 0,
        1 => 1,
        2 => 1_000_000,
        _ => rng.next_u64() % 1_000_000_000,
    }
}

/// Runs 1 to 3: good layers, with the deadlines of `idx` left due for `len` calls from call `start`.
fn layers(seed: u64, idx: &[usize], start: usize, lens: &[usize], out: String) -> String {
    let mut rng = SplitMix64::new(seed);
    let mut run = Run::new(out);
    let mut asks = [false; TIMERS];
    let mut fixed = [None::<u64>; TIMERS];
    let mut now = 1_000_000_000u64;
    for c in 0..60 {
        // the call that starts a stuck window is a later time than the call before, so that its deadline is
        // not already due at that call
        now += if c == start {
            step(&mut rng).max(1)
        } else {
            step(&mut rng)
        };
        let mut dues = [None; TIMERS];
        for (i, due) in dues.iter_mut().enumerate() {
            *due = good(&mut rng, now, &mut asks[i]);
        }
        for (k, &i) in idx.iter().enumerate() {
            if c == start {
                fixed[i] = Some(now);
                asks[i] = false;
            }
            if (start..start + lens[k]).contains(&c) {
                dues[i] = fixed[i];
            }
        }
        let flags = run.call(now, dues);
        if idx.is_empty() {
            assert!(flags.iter().all(|f| !f), "a good layer was flagged");
            assert_eq!(run.probe.held(), None);
            assert_eq!(run.probe.total(), 0);
        }
        for (k, &i) in idx.iter().enumerate() {
            assert_eq!(flags[i], c == start + 1 && lens[k] >= 2, "flag of {i} at call {c}");
            if (start + 1..start + lens[k]).contains(&c) {
                assert_eq!(
                    run.probe.held(),
                    Some(now.saturating_add(TICK)),
                    "held at stuck call {c}"
                );
            }
        }
        run.answers(&dues);
        if idx.is_empty() {
            let m = dues.iter().flatten().copied().min();
            assert_eq!(run.probe.answer(m), m, "a good layer's deadline was moved");
        }
    }
    run.finish()
}

/// Run 4: the top of the clock's range, two deadlines left due throughout.
fn top(r: usize, out: String) -> String {
    let starts = [
        u64::MAX - 2_000_000,
        u64::MAX - 1_000_000,
        u64::MAX - 1,
        u64::MAX,
        u64::MAX - 2_000_000,
    ];
    let mut run = Run::new(out);
    let mut now = starts[r];
    for _ in 0..8 {
        let mut dues = [None; TIMERS];
        dues[0] = Some(starts[r]);
        dues[4] = Some(starts[r]);
        run.call(now, dues);
        run.answers(&dues);
        now = now.saturating_add(u64::from(r % 2 == 1 || r == 4));
    }
    assert!(run.probe.held().is_some(), "nothing was held at the top of the clock");
    if r == 3 {
        assert_eq!(run.probe.held(), Some(u64::MAX), "the held time did not saturate");
    }
    run.finish()
}

/// Run 5: time going back with a deadline left due across the calls.
fn back(r: usize, out: String) -> String {
    let mut rng = SplitMix64::new(0x7462_2000 + r as u64);
    let mut run = Run::new(out);
    let d = 1000 + r as u64;
    for _ in 0..12 {
        let now = if r == 4 {
            500 + rng.next_u64() % 1000
        } else {
            2000 + rng.next_u64() % 1000
        };
        let mut dues = [None; TIMERS];
        dues[3] = Some(d);
        run.call(now, dues);
        run.answers(&dues);
    }
    run.finish()
}

/// Run 6: random deadlines and a clock that sometimes goes back.
fn random(r: u64, out: String) -> String {
    let mut rng = SplitMix64::new(0x7462_1000 + r);
    let mut run = Run::new(out);
    let mut now = 1_000_000_000u64;
    let mut prev = [None::<u64>; TIMERS];
    let mut last = None::<u64>;
    for _ in 0..100 {
        now = match rng.next_u64() % 20 {
            0 => now.saturating_sub(rng.next_u64() % 1_000_000_000),
            1..=6 => now,
            _ => now + rng.next_u64() % 1_000_000_000,
        };
        let mut dues = [None; TIMERS];
        for (i, due) in dues.iter_mut().enumerate() {
            *due = match rng.next_u64() % 6 {
                0 => None,
                1 => Some(rng.next_u64() % 4_000_000_000),
                2 => Some(now),
                3 => Some(now.saturating_sub(rng.next_u64() % 1_000_000_000)),
                4 => prev[i],
                _ => last,
            };
        }
        prev = dues;
        last = Some(now);
        run.call(now, dues);
        run.answers(&dues);
        run.answer(Some(rng.next_u64() % 4_000_000_000));
    }
    run.finish()
}

#[test]
fn timer_bound() {
    let mut out = String::new();
    for r in 0..20u64 {
        out = layers(0x7462_0000 + r, &[], 0, &[], out);
    }
    for r in 0..20u64 {
        let mut rng = SplitMix64::new(0x7462_0100 + r);
        let i = (rng.next_u64() % TIMERS as u64) as usize;
        let start = 2 + (rng.next_u64() % 20) as usize;
        let len = 3 + (rng.next_u64() % 4) as usize;
        out = layers(0x7462_0200 + r, &[i], start, &[len], out);
    }
    for r in 0..10u64 {
        let l0 = 3 + (r % 4) as usize;
        let l8 = 3 + ((r / 2) % 4) as usize;
        out = layers(0x7462_0300 + r, &[0, 8], 3 + r as usize, &[l0, l8], out);
    }
    for r in 0..5 {
        out = top(r, out);
    }
    for r in 0..5 {
        out = back(r, out);
    }
    for r in 0..40 {
        out = random(r, out);
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("timer_bound.ndjson"), &out).unwrap();
    }
}
