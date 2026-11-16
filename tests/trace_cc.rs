//! Trace generation for congestion control and pacing: seeded random runs of a real `Cubic` controller and `Pacer`
//! (`vinc-transport`, built with the `trace` feature), recorded as ndjson (`cc.ndjson`) for the TLA+ trace check
//! (`TraceCc.tla`) and the Lean replay (`Vinc/TraceCc.lean`).
//!
//! A run feeds the controller the calls the recovery engine makes: round-trip samples, acknowledgements (with and
//! without a smoothed or minimum round trip, a segment size, packets in order and out), losses (with and without a
//! queueing delay), a new path, a restore, a resume after idle, the gate slack and the gate itself; and the pacer
//! packets sent and release queries. After every call the controller shows its state (`trace_view`). The checkers
//! replay each call with the operators of the model and require the state recorded. The runs of `cc.ndjson` keep
//! every number within what the 32-bit checker holds (a threshold not set, or a release time past the end, is
//! recorded as `2^31 - 1`); the runs of `cc_wide.ndjson`, read by the Lean replay only, take windows up to `2^40`,
//! byte counts and times up to `u64::MAX`, and a segment size outside its clamp.
//!
//! The test asserts what it can itself (the window stays between its floor and cap, a loss never raises it, the
//! pacer charges each packet its size and pauses exactly at the packet that brings its burst to the budget) so it is
//! meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::similar_names,
    unreachable_pub
)]

use std::fmt::Write as _;

use vinc_tests::SplitMix64;
use vinc_transport::recovery::trace::CcView;
use vinc_transport::recovery::{AckInput, Cubic, MAX_CWND, MIN_CWND, MS, Pacer, burst_budget};

/// The largest value of a 32-bit checker integer.
const TOP: u64 = (1 << 31) - 1;

fn opt(x: Option<u64>) -> i128 {
    x.map_or(-1, i128::from)
}

fn clamp(v: u64, wide: bool) -> u64 {
    if wide { v } else { v.min(TOP) }
}

fn view_json(v: &CcView, wide: bool) -> String {
    format!(
        r#"{{"cwnd":{},"ss":{},"wmax":{},"west":{},"k":{},"epoch":{},"rec":{},"streak":{},"rend":{},"ref":{},"rmin":{},"samp":{},"pst":{},"pby":{},"rate":{},"slack":{}}}"#,
        v.cwnd,
        clamp(v.ssthresh, wide),
        v.w_max,
        v.w_est,
        v.k_ms,
        opt(v.epoch),
        opt(v.recovery),
        v.streak,
        v.round_end,
        opt(v.reference),
        opt(v.round_min),
        v.samples,
        opt(v.probe_start),
        v.probe_bytes,
        v.rate,
        v.slack
    )
}

struct Run<'a> {
    c: Cubic,
    p: Pacer,
    out: &'a mut String,
    id: u32,
    wide: bool,
    now: u64,
    la: u64,
    sends: u32,
}

impl Run<'_> {
    fn log(&mut self, body: &str) {
        let v = view_json(&self.c.trace_view(), self.wide);
        let _ = writeln!(self.out, r#"{{"t":"txcc","run":{},{body},"v":{v}}}"#, self.id);
    }

    fn plog(&mut self, body: &str) {
        let (spent, next, start) = self.p.trace_view();
        let _ = writeln!(
            self.out,
            r#"{{"t":"txcc","run":{},{body},"v":{{"spent":{spent},"next":{},"start":{}}}}}"#,
            self.id,
            clamp(next, self.wide),
            clamp(start, self.wide)
        );
    }

    fn check(&self, before: &CcView) {
        let a = self.c.trace_view();
        assert!(
            (MIN_CWND..=MAX_CWND).contains(&a.cwnd),
            "the window {} left its floor and cap",
            a.cwnd
        );
        assert!(a.streak <= 4);
        assert!(a.w_est <= MAX_CWND);
        let _ = before;
    }
}

fn pick<T: Copy>(rng: &mut SplitMix64, from: &[T]) -> T {
    from[(rng.next_u64() % from.len() as u64) as usize]
}

fn run(seed: u64, out: &mut String, id: u32, steps: u32, wide: bool) {
    let mut rng = SplitMix64::traced(seed);
    let mut r = Run {
        c: Cubic::new(),
        p: Pacer::new(),
        out,
        id,
        wide,
        now: MS,
        la: 0,
        sends: 0,
    };
    let _ = writeln!(
        r.out,
        r#"{{"t":"txcc","run":{id},"op":"init","v":{}}}"#,
        view_json(&r.c.trace_view(), wide)
    );
    let mut srtt: Option<u64> = None;
    let mut min_rtt: Option<u64> = None;
    let mut mss = 1200u64;
    let mut next_pn = 1u64;
    let mut paced_in_burst = 0u32;
    for _ in 0..steps {
        if !wide && r.now > 900 * MS {
            break;
        }
        match rng.next_u64() % 100 {
            0..=11 => {
                let s = if wide {
                    pick(&mut rng, &[0, 1, 5 * MS, u64::MAX, 1 << 40])
                } else {
                    pick(&mut rng, &[MS, 3 * MS, 5 * MS, 20 * MS, 300 * MS])
                };
                r.c.on_rtt_sample(s);
                r.log(&format!(r#""op":"rtt","s":{s}"#));
            }
            12..=19 => {
                srtt = pick(&mut rng, &[None, Some(3 * MS), Some(10 * MS), Some(30 * MS)]);
                min_rtt = pick(&mut rng, &[None, Some(MS), Some(5 * MS), Some(40 * MS), Some(300 * MS)]);
                if wide {
                    srtt = pick(&mut rng, &[None, Some(0), Some(u64::MAX), Some(1 << 50), srtt]);
                    min_rtt = pick(&mut rng, &[None, Some(0), Some(u64::MAX), Some(1 << 50), min_rtt]);
                }
                mss = if wide {
                    pick(&mut rng, &[0, 1, 1200, 9000, 65_535, 70_000, 1 << 20])
                } else {
                    pick(&mut rng, &[1200, 1400])
                };
            }
            20..=59 => {
                let ss = r.c.in_slow_start();
                let mut mn = min_rtt;
                if !wide && !ss {
                    // congestion avoidance with the rate gate in play is checked by the Lean replay alone
                    mn = mn.filter(|m| (2 * MS..250 * MS).contains(m));
                }
                let step = if wide {
                    pick(&mut rng, &[0, 1, MS, 1 << 40, u64::MAX / 2])
                } else {
                    pick(&mut rng, &[0, 0, MS, 3 * MS])
                };
                r.now = if wide {
                    r.now.saturating_add(step)
                } else if r.now + step <= 900 * MS {
                    r.now + step
                } else {
                    r.now
                };
                r.la = r.la.saturating_add(rng.next_u64() % 4);
                if wide && rng.next_u64().is_multiple_of(9) {
                    r.la = pick(&mut rng, &[0, u64::MAX, 1 << 62]);
                }
                next_pn = r.la.saturating_add(rng.next_u64() % 6);
                let acked = if wide {
                    pick(&mut rng, &[0, 1, 1200, 44_000, 1 << 30, 1 << 40, 1 << 50, u64::MAX])
                } else if ss {
                    1 + rng.next_u64() % 20_000
                } else {
                    1 + rng.next_u64() % 12_000
                };
                let before = r.c.trace_view();
                let a = AckInput {
                    now: r.now,
                    acked,
                    largest_acked: r.la,
                    next_pn,
                    srtt,
                    min_rtt: mn,
                    mss,
                };
                r.c.on_acked(&a);
                r.check(&before);
                r.log(&format!(
                    r#""op":"ack","now":{},"acked":{acked},"la":{},"np":{next_pn},"srtt":{},"mn":{},"mss":{mss}"#,
                    r.now,
                    r.la,
                    opt(srtt),
                    opt(mn)
                ));
            }
            60..=69 => {
                let before = r.c.trace_view();
                let newest = if wide {
                    pick(&mut rng, &[0, r.now, u64::MAX])
                } else {
                    r.now.saturating_sub(rng.next_u64() % (6 * MS))
                };
                let lat = pick(&mut rng, &[None, Some(2 * MS), Some(9 * MS), Some(80 * MS)]);
                let mn = pick(&mut rng, &[None, Some(2 * MS), Some(30 * MS)]);
                let (lat, mn) = if wide {
                    (
                        pick(&mut rng, &[lat, Some(u64::MAX), Some(0)]),
                        pick(&mut rng, &[mn, Some(u64::MAX)]),
                    )
                } else {
                    (lat, mn)
                };
                if wide && rng.next_u64().is_multiple_of(3) {
                    r.now = r.now.saturating_add(1 << 40);
                }
                let reduced = r.c.on_loss(r.now, newest, lat, mn);
                let after = r.c.trace_view();
                assert!(after.cwnd <= before.cwnd, "a loss raised the window");
                if !reduced {
                    assert_eq!(after, before, "a loss in the same episode changed the controller");
                }
                r.check(&before);
                r.log(&format!(
                    r#""op":"loss","now":{},"newest":{newest},"lat":{},"mn":{},"r":{}"#,
                    r.now,
                    opt(lat),
                    opt(mn),
                    reduced
                ));
            }
            70..=73 => {
                let before = r.c.trace_view();
                r.c.new_path(r.now, next_pn);
                r.check(&before);
                r.log(&format!(r#""op":"newpath","now":{},"np":{next_pn}"#, r.now));
            }
            74..=77 => {
                let before = r.c.trace_view();
                let cw = if wide {
                    pick(&mut rng, &[0, 5000, 1 << 39, 1 << 41, u64::MAX])
                } else {
                    pick(&mut rng, &[3000, 20_000, 90_000, 400_000, 2_000_000])
                };
                let ss = if wide {
                    pick(&mut rng, &[0, 1 << 20, u64::MAX])
                } else {
                    pick(&mut rng, &[10_000, 1 << 20, 1 << 30])
                };
                r.c.restore(cw, ss);
                assert!(r.c.trace_view().cwnd >= before.cwnd, "a restore lowered the window");
                r.check(&before);
                r.log(&format!(r#""op":"restore","cw":{cw},"ss":{ss}"#));
            }
            78..=81 => {
                let before = r.c.trace_view();
                r.c.resume(min_rtt);
                r.check(&before);
                r.log(&format!(r#""op":"resume","mn":{}"#, opt(min_rtt)));
            }
            82 | 83 => {
                let b = if wide {
                    pick(&mut rng, &[0, 44_000, u64::MAX])
                } else {
                    pick(&mut rng, &[0, 10_000, 44_000, 300_000])
                };
                r.c.set_gate_slack(b);
                r.log(&format!(r#""op":"slack","b":{b}"#));
            }
            84 | 85 => {
                let m = pick(&mut rng, &[MS, 5 * MS, 40 * MS, 300 * MS]);
                let m = if wide {
                    pick(&mut rng, &[m, 0, u64::MAX, 1 << 50])
                } else {
                    m
                };
                let cap = r.c.gate_cap(m);
                r.log(&format!(r#""op":"gate","mn":{m},"cap":{}"#, opt(cap)));
            }
            _ => {
                let cw = r.c.cwnd();
                if rng.next_u64().is_multiple_of(4) {
                    let q = r.now;
                    let rel = r.p.next_release(q);
                    assert!(rel >= q, "the pacer released data in the past");
                    r.plog(&format!(r#""op":"prel","now":{q},"r":{}"#, clamp(rel, wide)));
                } else {
                    // a packet leaves when the pacer lets it: not before the release
                    let at = r.p.next_release(r.now);
                    if !wide && at > 900 * MS {
                        continue;
                    }
                    r.now = at.max(r.now);
                    let mtu = if wide {
                        pick(&mut rng, &[0, 1200, 65_535, 1 << 40, u64::MAX])
                    } else {
                        pick(&mut rng, &[1200, 1452, 8952])
                    };
                    let size: u32 = if wide {
                        pick(&mut rng, &[0, 1, 1200, 65_535, u32::MAX])
                    } else {
                        let m = mtu as u32;
                        pick(&mut rng, &[40, 600, 1200, m, m, m, 2 * m + 7])
                    };
                    let s = srtt.unwrap_or(if wide { u64::MAX } else { 20 * MS });
                    let limited = rng.next_u64().is_multiple_of(2);
                    let (spent_before, next_before, _) = r.p.trace_view();
                    r.p.on_sent(r.now, size, mtu, s, cw, limited);
                    let (spent_after, next_after, start) = r.p.trace_view();
                    let charged = spent_before + u64::from(size.max(1));
                    assert!(spent_after < burst_budget(mtu), "the burst kept more than its budget");
                    if spent_before == 0 {
                        assert_eq!(start, r.now, "a burst begins with its first packet");
                    }
                    if charged < burst_budget(mtu) {
                        assert_eq!(spent_after, charged, "a packet was not charged its size");
                        assert_eq!(next_after, next_before, "a packet within the budget paused");
                        paced_in_burst += 1;
                    } else {
                        assert_eq!(
                            spent_after, 0,
                            "the packet that reached the budget did not end the burst"
                        );
                        paced_in_burst = 0;
                    }
                    r.sends += 1;
                    r.plog(&format!(
                        r#""op":"psent","now":{},"size":{size},"mtu":{mtu},"srtt":{s},"cw":{cw},"lim":{limited}"#,
                        r.now
                    ));
                }
            }
        }
    }
    let _ = paced_in_burst;
    r.log(r#""op":"end""#);
}

#[test]
fn congestion_control_runs_match_the_models() {
    let mut out = String::new();
    for id in 1..=60u32 {
        run(0x4343_0000 + u64::from(id), &mut out, id, 500, false);
    }
    let mut wide = String::new();
    for id in 901..=930u32 {
        run(0x4343_ff00 + u64::from(id), &mut wide, id, 400, true);
    }
    for needle in [
        r#""op":"ack""#,
        r#""op":"loss""#,
        r#""op":"newpath""#,
        r#""op":"restore""#,
        r#""op":"resume""#,
        r#""op":"gate""#,
        r#""op":"psent""#,
        r#""r":true"#,
        r#""r":false"#,
    ] {
        assert!(
            vinc_tests::soaking() || out.contains(needle),
            "the runs never reach {needle}"
        );
    }
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("cc.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("cc_wide.ndjson"), &wide).unwrap();
    }
}
