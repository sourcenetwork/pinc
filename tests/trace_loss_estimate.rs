//! Trace generation for the node-wide loss estimate and the tail-repair decision (`pinc-transport`, built with the
//! `trace` feature): real `LossEstimate`s, recorded as ndjson (`loss_estimate.ndjson`) for the TLA+ trace check
//! (`TraceLossEstimate.tla`).
//!
//! Batches of every size from none to `u32::MAX` are recorded, then read, then asked for the repair decision at ages
//! on both sides of the minimum, with every pair of flags: a sweep of every pair of counts, walks of the estimate to
//! each of its fixed points, a climb and a fall through the repair threshold, and seeded calls.
//!
//! The test replays the estimate packet by packet (the module documentation's rule) and checks every call against it
//! and the repair decision against its definition, so it is meaningful without the proof tools. The trace is written
//! to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub,
    clippy::indexing_slicing,
    clippy::many_single_char_names
)]

use std::fmt::Write as _;

use pinc_tests::{SplitMix64, trace_cases};
use pinc_transport::recovery::{LOSS_SCALE, LossEstimate, REPAIR_MIN_AGE, REPAIR_THRESHOLD, SECOND};

const COUNTS: [u32; 16] = [
    0,
    1,
    2,
    31,
    32,
    33,
    299,
    300,
    301,
    400,
    65535,
    65536,
    65537,
    1 << 20,
    u32::MAX - 1,
    u32::MAX,
];
const AGES: [u64; 10] = [
    0,
    1,
    2 * SECOND - 1,
    2 * SECOND,
    2 * SECOND + 1,
    1 << 31,
    1 << 32,
    10 * SECOND,
    u64::MAX - 1,
    u64::MAX,
];

fn limbs(v: u64, n: usize) -> String {
    let l: Vec<String> = (0..n).map(|i| ((v >> (16 * i)) & 0xffff).to_string()).collect();
    format!("[{}]", l.join(","))
}

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    repair_true: bool,
    repair_false_all_set: bool,
}

/// One estimate, the naive replay of it and the record.
struct Run<'a> {
    e: LossEstimate,
    x: u32,
    out: &'a mut String,
    seen: &'a mut Seen,
}

impl<'a> Run<'a> {
    /// A new estimate: its `new` event.
    fn new(out: &'a mut String, seen: &'a mut Seen) -> Self {
        let r = Run {
            e: LossEstimate::new(),
            x: 0,
            out,
            seen,
        };
        assert_eq!(r.e.get(), 0, "a new estimate is not zero");
        let _ = writeln!(r.out, r#"{{"t":"loss","op":"new","v":0}}"#);
        r.same();
        r
    }

    fn same(&self) {
        assert_eq!(self.e.get(), self.x, "the estimate is not the replay of the packets");
        assert!(self.e.get() <= LOSS_SCALE);
    }

    fn reset(&mut self) {
        self.e.reset();
        self.x = 0;
        assert_eq!(self.e.get(), 0, "a reset estimate is not zero");
        let _ = writeln!(self.out, r#"{{"t":"loss","op":"reset","v":0}}"#);
    }

    fn record(&mut self, lost: u32, acked: u32) {
        let before = self.x;
        // each loop stops at the first step that changes nothing: every later one would change nothing too
        for _ in 0..acked {
            let next = self.x - (self.x >> 5);
            if next == self.x {
                break;
            }
            self.x = next;
        }
        for _ in 0..lost {
            let next = self.x + ((LOSS_SCALE - self.x) >> 5);
            if next == self.x {
                break;
            }
            self.x = next;
        }
        self.e.record(lost, acked);
        self.same();
        if lost == 0 && acked == 0 {
            assert_eq!(self.x, before);
        }
        if lost > 0 && acked == 0 {
            assert!(self.x >= before, "losses lowered the estimate");
        }
        if lost == 0 && acked > 0 {
            assert!(self.x <= before, "acknowledgements raised the estimate");
        }
        let _ = writeln!(
            self.out,
            r#"{{"t":"loss","op":"record","lost":{},"acked":{},"v":{}}}"#,
            limbs(u64::from(lost), 2),
            limbs(u64::from(acked), 2),
            self.e.get()
        );
    }

    fn get(&mut self) {
        self.same();
        let _ = writeln!(self.out, r#"{{"t":"loss","op":"get","v":{}}}"#, self.e.get());
    }

    fn repair(&mut self, age: u64, drained: bool, direct: bool) {
        let ans = self.e.should_send_repair(age, drained, direct);
        let want = age >= REPAIR_MIN_AGE && drained && direct && self.e.get() >= REPAIR_THRESHOLD;
        assert_eq!(ans, want, "the repair decision is not its definition");
        self.seen.repair_true |= ans;
        self.seen.repair_false_all_set |= !ans && drained && direct && age >= REPAIR_MIN_AGE;
        let _ = writeln!(
            self.out,
            r#"{{"t":"loss","op":"repair","age":{},"drained":{drained},"direct":{direct},"ans":{ans}}}"#,
            limbs(age, 4)
        );
    }

    /// The decision for the given ages with every pair of flags.
    fn repairs(&mut self, ages: &[u64]) {
        for &age in ages {
            for drained in [false, true] {
                for direct in [false, true] {
                    self.repair(age, drained, direct);
                }
            }
        }
    }

    /// Record `(lost, acked)` until the estimate stops changing, then 5 more times.
    fn walk(&mut self, lost: u32, acked: u32) {
        let mut n = 0;
        loop {
            let before = self.e.get();
            self.record(lost, acked);
            n += 1;
            assert!(n <= 400, "the walk did not settle within 400 records");
            if self.e.get() == before {
                break;
            }
        }
        for _ in 0..5 {
            let before = self.e.get();
            self.record(lost, acked);
            assert_eq!(self.e.get(), before, "a settled estimate moved");
        }
    }
}

#[test]
fn the_loss_estimate_matches_the_model() {
    let mut rng = SplitMix64::traced(0x6c6f_7373);
    let (mut out, mut seen) = (String::new(), Seen::default());

    // 1. the sweep of every pair of counts
    for &l in &COUNTS {
        for &a in &COUNTS {
            let mut r = Run::new(&mut out, &mut seen);
            r.record(l, a);
            r.get();
            r.record(l, a);
            r.repairs(&[0, 2 * SECOND - 1, 2 * SECOND, u64::MAX]);
        }
    }

    // 2. walks to the edges
    let mut r = Run::new(&mut out, &mut seen);
    for (l, a) in [(1, 0), (0, 1), (u32::MAX, 0), (0, u32::MAX)] {
        r.walk(l, a);
        r.repairs(&AGES);
    }
    r.reset();
    r.get();

    // 3. around the threshold
    let mut r = Run::new(&mut out, &mut seen);
    // the records of a climb to the threshold, counted on the replay
    let mut n = 0;
    let mut x = 0u32;
    while x < REPAIR_THRESHOLD {
        x += (LOSS_SCALE - x) >> 5;
        n += 1;
    }
    for i in 1..=n {
        r.record(1, 0);
        if i + 3 >= n {
            r.repairs(&AGES);
        }
    }
    assert!(r.e.get() >= REPAIR_THRESHOLD);
    while r.e.get() >= REPAIR_THRESHOLD {
        r.record(0, 1);
    }
    r.repairs(&AGES);

    // 4. seeded estimates
    let mut below = |n: u64| rng.next_u64() % n;
    for _ in 0..trace_cases(50, 200) {
        let mut r = Run::new(&mut out, &mut seen);
        for _ in 0..50 {
            match below(20) {
                0..=12 => {
                    let mut count = || {
                        if below(2) == 0 {
                            COUNTS[below(16) as usize]
                        } else {
                            below(1000) as u32
                        }
                    };
                    let l = count();
                    let a = count();
                    r.record(l, a);
                }
                13..=14 => r.get(),
                15..=18 => {
                    let age = if below(2) == 0 {
                        AGES[below(10) as usize]
                    } else {
                        below(4 * SECOND)
                    };
                    let (drained, direct) = (below(2) == 1, below(2) == 1);
                    r.repair(age, drained, direct);
                }
                _ => r.reset(),
            }
        }
    }

    assert!(seen.repair_true, "the repair answer was never true");
    assert!(
        seen.repair_false_all_set,
        "the repair answer was never false with every flag set"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("loss_estimate.ndjson"), &out).unwrap();
    }
}
