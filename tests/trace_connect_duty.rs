//! Trace generation for the beacon schedule and the radio adapter of the local network (`pinc_connect::local::Duty`
//! and `Radio`): seeded and boundary runs of the real types, recorded as ndjson (`connect_duty.ndjson`) for the TLA+
//! trace check (`TraceConnectDuty.tla`).
//!
//! A schedule run counts in milliseconds from an origin: it is created (`new`), polled (`poll`), restarted
//! (`restart`) and told whether a mailbox serves the node (`mailbox`), and every event shows the deadline and the
//! count of beacons sent. A radio run counts in nanoseconds: a medium (`new`) and the frames admitted to it
//! (`admit`). A run far from `u64::MAX` has an origin of 1000 s; a run at the limit puts `u64::MAX` at a small
//! relative time `top`, so that the models, which count from the origin, see the saturation the code does there.
//!
//! The test checks by itself, far from the limit: the next deadline after a release, at most five releases in a
//! burst, none in the steady phase while a mailbox serves the node, one `sent` per release, and the admission of
//! frames (too long, a duty of zero, too early, and exactly at the off time). The runs at the limit are recorded and
//! checked against the model only: there a release at `u64::MAX` leaves no deadline (-1 in the trace, the model's
//! `Never`), so no later poll there releases, and an admission at `u64::MAX` closes the medium. The model's `Never`
//! and its checked addition check these runs.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::cognitive_complexity,
    unreachable_pub,
    clippy::manual_checked_ops,
    clippy::manual_is_multiple_of
)]

use std::fmt::Write as _;

use pinc_connect::local::{BURST, BURST_GAP, Duty, Radio, STEADY_GAP};
use pinc_tests::{SplitMix64, soaking};

const MS: u64 = 1_000_000;
const FAR: u64 = 1_000 * 1_000_000_000;

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    burst5: u32,
    steady: u32,
    skip: u32,
    too_long: u32,
    too_early: u32,
    duty0: u32,
}

struct T {
    out: String,
    seen: Seen,
}

/// One schedule run.
struct Sched {
    d: Duty,
    o: u64,
    top: i64,
    burst_from: u64,
    mailbox: bool,
    closed: bool,
    burst_true: u32,
}

impl Sched {
    fn at_limit(&self) -> bool {
        self.top >= 0
    }

    fn rel(&self, abs: u64) -> u64 {
        assert!(abs >= self.o, "a deadline before the origin");
        let d = abs - self.o;
        assert_eq!(d % MS, 0, "a deadline off the millisecond grid");
        d / MS
    }

    /// The relative deadline, in milliseconds (`None` when the schedule has no next instant).
    fn next(&self) -> Option<u64> {
        self.d.deadline().map(|a| self.rel(a))
    }

    /// The deadline as the trace records it: milliseconds, or -1 for none (the model's `Never`).
    fn nx(&self) -> String {
        self.next().map_or("-1".into(), |n| n.to_string())
    }

    /// A run starting at relative time `at`: far from the limit when `top` is negative, else with `u64::MAX` at `top`.
    fn start(t: &mut T, top: i64, at: u64) -> Self {
        let o = if top < 0 { FAR } else { u64::MAX - (top as u64) * MS };
        let now = o + at * MS;
        let s = Self {
            d: Duty::new(now),
            o,
            top,
            burst_from: now,
            mailbox: false,
            closed: false,
            burst_true: 0,
        };
        let _ = writeln!(
            t.out,
            r#"{{"t":"duty","op":"new","at":{at},"top":{top},"next":{},"sent":{}}}"#,
            s.nx(),
            s.d.sent()
        );
        s
    }

    fn poll(&mut self, t: &mut T, at: u64) -> bool {
        if self.at_limit() {
            assert!(at as i64 <= self.top, "a call after the limit");
        }
        let now = self.o + at * MS;
        let was_next = self.d.deadline();
        let sent = self.d.sent();
        let r = self.d.poll(now);
        assert_eq!(self.d.sent(), sent + u64::from(r), "sent is not one per release");
        if !self.at_limit() {
            let in_steady = now.saturating_sub(self.burst_from) >= BURST;
            if r {
                assert!(self.d.deadline().is_some_and(|d| d > now));
                let after = now + BURST_GAP;
                let want = if after.saturating_sub(self.burst_from) < BURST {
                    after
                } else {
                    now + STEADY_GAP
                };
                assert_eq!(self.d.deadline(), Some(want), "the next deadline after a release");
                assert!(
                    !(in_steady && self.mailbox),
                    "a release in the steady phase with a mailbox"
                );
                t.seen.steady += u32::from(in_steady);
            } else if self.mailbox && in_steady && was_next.is_some_and(|w| now >= w) {
                t.seen.skip += 1;
            }
            if !self.closed {
                if in_steady {
                    self.closed = true;
                } else if r {
                    self.burst_true += 1;
                    assert!(self.burst_true <= 5, "more than five releases in a burst");
                    t.seen.burst5 += u32::from(self.burst_true == 5);
                }
            }
        }
        let _ = writeln!(
            t.out,
            r#"{{"t":"duty","op":"poll","at":{at},"r":{r},"next":{},"sent":{}}}"#,
            self.nx(),
            self.d.sent()
        );
        r
    }

    fn restart(&mut self, t: &mut T, at: u64) {
        let now = self.o + at * MS;
        self.d.restart(now);
        self.burst_from = now;
        self.closed = false;
        self.burst_true = 0;
        let _ = writeln!(
            t.out,
            r#"{{"t":"duty","op":"restart","at":{at},"next":{},"sent":{}}}"#,
            self.nx(),
            self.d.sent()
        );
    }

    fn set_mailbox(&mut self, t: &mut T, v: bool) {
        self.d.set_mailbox(v);
        self.mailbox = v;
        let _ = writeln!(
            t.out,
            r#"{{"t":"duty","op":"mailbox","v":{v},"next":{},"sent":{}}}"#,
            self.nx(),
            self.d.sent()
        );
    }
}

fn polls(s: &mut Sched, t: &mut T, from: u64, to: u64, step: u64) {
    let mut at = from;
    while at <= to {
        s.poll(t, at);
        at += step;
    }
}

fn schedule_runs(t: &mut T, rng: &mut SplitMix64) {
    // 1. the plain schedule, then a restart
    let mut s = Sched::start(t, -1, 0);
    polls(&mut s, t, 0, 200_000, 100);
    s.restart(t, 200_000);
    polls(&mut s, t, 200_000, 210_000, 100);
    // 2. polls exactly at each deadline, then one before it and one at it
    let mut s = Sched::start(t, -1, 0);
    for _ in 0..15 {
        let at = s.next().unwrap();
        s.poll(t, at);
    }
    let at = s.next().unwrap();
    s.poll(t, at - 1);
    s.poll(t, at);
    // 3. late polls
    let mut s = Sched::start(t, -1, 0);
    for at in [0, 2500, 4999, 5000, 5001, 64_999, 65_000, 125_000] {
        s.poll(t, at);
    }
    // 4. the clock stepping back
    let mut s = Sched::start(t, -1, 0);
    for at in [3000, 2000, 2999, 3000, 4000] {
        s.poll(t, at);
    }
    // 5. a mailbox
    let mut s = Sched::start(t, -1, 0);
    s.set_mailbox(t, true);
    polls(&mut s, t, 0, 130_000, 500);
    s.set_mailbox(t, false);
    polls(&mut s, t, 130_000, 200_000, 500);
    s.set_mailbox(t, true);
    polls(&mut s, t, 200_000, 270_000, 500);
    // 6. restarts in the burst, at its end, in the steady phase
    let mut s = Sched::start(t, -1, 0);
    polls(&mut s, t, 0, 2000, 500);
    s.restart(t, 2000);
    polls(&mut s, t, 2000, 5000, 500);
    s.restart(t, 5000);
    polls(&mut s, t, 5000, 70_000, 500);
    s.restart(t, 70_000);
    polls(&mut s, t, 70_000, 80_000, 500);
    // 7. at the limit, the steady phase runs into u64::MAX
    let mut s = Sched::start(t, 70_000, 0);
    polls(&mut s, t, 0, 70_000, 1000);
    for _ in 0..5 {
        s.poll(t, 70_000);
    }
    // 8. at the limit, the burst runs into u64::MAX
    let mut s = Sched::start(t, 3_000, 0);
    for at in [0, 1000, 2000, 3000, 3000, 3000] {
        s.poll(t, at);
    }
    // 9. random runs
    for i in 0..50 {
        let limit = i % 5 == 4;
        let top = if limit {
            60_000 + (rng.next_u64() % 140_001) as i64
        } else {
            -1
        };
        let mut s = Sched::start(t, top, 0);
        let mut cur = 0u64;
        let clamp = |at: u64| if limit { at.min(top as u64) } else { at };
        for _ in 0..200 {
            match rng.next_u64() % 100 {
                0..=79 => {
                    let at = clamp(match rng.next_u64() % 10 {
                        0..=2 => s.next().unwrap_or(cur),
                        3..=5 => cur + rng.next_u64() % 2001,
                        6 | 7 => cur + rng.next_u64() % 70_001,
                        _ => cur.saturating_sub(rng.next_u64() % 1001),
                    });
                    s.poll(t, at);
                    cur = at;
                }
                80..=84 => s.restart(t, cur),
                _ => {
                    let v = rng.next_u64() % 2 == 0;
                    s.set_mailbox(t, v);
                }
            }
        }
    }
}

/// One radio run.
struct Air {
    r: Radio,
    o: u64,
    top: i64,
    ready: u64,
}

impl Air {
    fn start(t: &mut T, mtu: usize, nspb: u64, duty: u64, top: i64) -> Self {
        let o = if top < 0 { FAR } else { u64::MAX - top as u64 };
        let _ = writeln!(
            t.out,
            r#"{{"t":"radio","op":"new","mtu":{mtu},"nspb":{nspb},"duty":{duty},"top":{top}}}"#
        );
        Self {
            r: Radio::new(mtu, nspb, duty),
            o,
            top,
            ready: 0,
        }
    }

    fn admit(&mut self, t: &mut T, at: u64, len: usize) -> bool {
        if self.top >= 0 {
            assert!(at as i64 <= self.top, "a call after the limit");
        }
        let now = self.o + at;
        let r = self.r.admit(now, len);
        if self.top < 0 {
            let (mtu, nspb, duty) = (self.r.mtu, self.r.ns_per_byte, self.r.duty_permille);
            let early = len <= mtu && duty != 0 && now < self.ready;
            assert_eq!(r, len <= mtu && duty != 0 && !early, "admit len={len} at={at}");
            if r {
                self.ready = now + (len as u64) * nspb * 1000 / duty;
            }
            t.seen.too_long += u32::from(len > mtu);
            t.seen.duty0 += u32::from(len <= mtu && duty == 0);
            t.seen.too_early += u32::from(early);
        }
        let _ = writeln!(t.out, r#"{{"t":"radio","op":"admit","at":{at},"len":{len},"r":{r}}}"#);
        r
    }
}

/// The off time of a frame of `len` bytes on a medium, as the test computes it.
fn off(len: usize, nspb: u64, duty: u64) -> u64 {
    if duty == 0 {
        0
    } else {
        (len as u64) * nspb * 1000 / duty
    }
}

fn radio_runs(t: &mut T, rng: &mut SplitMix64) {
    const MEDIA: [(usize, u64, u64); 7] = [
        (255, 0, 10),
        (255, 32, 10),
        (255, 32, 0),
        (255, 32, 1000),
        (255, 32, 1500),
        (1500, 600, 1),
        (64, 1, 999),
    ];
    // 1. each medium, each length, around the off time
    for (mtu, nspb, duty) in MEDIA {
        for len in [0, 1, mtu, mtu + 1] {
            let mut a = Air::start(t, mtu, nspb, duty, -1);
            let o = off(len, nspb, duty);
            a.admit(t, 0, len);
            for at in [o.saturating_sub(1), o, o + 1] {
                a.admit(t, at, len);
            }
        }
    }
    // 2. at the limit
    let mut a = Air::start(t, 255, 32, 10, 1_000);
    for at in [0, 990, 1000, 1000, 1000] {
        a.admit(t, at, 1);
    }
    // 3. random runs
    for _ in 0..30 {
        let (mtu, nspb, duty) = MEDIA[(rng.next_u64() % 7) as usize];
        let mut a = Air::start(t, mtu, nspb, duty, -1);
        let span = off(mtu, nspb, duty) * 2;
        let mut cur = 0u64;
        for _ in 0..100 {
            let len = (rng.next_u64() % (mtu as u64 + 3)) as usize;
            cur = if rng.next_u64() % 5 == 0 {
                cur.saturating_sub(rng.next_u64() % 1001)
            } else {
                (cur + rng.next_u64() % (span + 1)).min(1_000_000_000)
            };
            a.admit(t, cur, len);
        }
    }
}

#[test]
fn beacon_schedule_and_radio_match_the_model() {
    let mut rng = SplitMix64::traced(0xD07_1CCE);
    let mut t = T {
        out: String::new(),
        seen: Seen::default(),
    };
    schedule_runs(&mut t, &mut rng);
    radio_runs(&mut t, &mut rng);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("connect_duty.ndjson"), &t.out).unwrap();
    }
    if !soaking() {
        let s = &t.seen;
        assert!(s.burst5 > 0, "no burst of exactly five releases");
        assert!(s.steady > 0, "no steady release after a burst");
        assert!(s.skip > 0, "no poll skipped for a mailbox");
        assert!(
            s.too_long > 0 && s.too_early > 0 && s.duty0 > 0,
            "a refusal was never recorded"
        );
    }
}
