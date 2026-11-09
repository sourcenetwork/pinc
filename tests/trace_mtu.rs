//! Trace generation for path MTU discovery: seeded runs of the real `Mtu` state machine of one path
//! (`vinc-transport`, built with the `trace` feature), recorded as ndjson (`mtu.ndjson`) for the TLA+ trace check
//! (`TraceMtu.tla`) and the Lean replay (`Vinc/TraceMtu.lean`).
//!
//! A run starts discovery and then makes the calls the connection makes: asks which size is due (with the path
//! allowed or not, interface sizes from the minimum to a jumbo frame, low latency or not), sends, acknowledges,
//! echoes and loses probes, raises a path event, notes the full-size packets, suspects a black hole and settles the
//! suspicion. After every call the machine shows its state. A second file (`mtu_wide.ndjson`, read by the Lean
//! replay only: the TLA+ checker has 32-bit integers and the lost-probe wait is 600 s) takes times up to `u64::MAX`.
//!
//! The test asserts what it can itself (the size never falls below the floor, rises only by a raise, falls only to
//! the floor by the black-hole fallback, a probe is due only when none is in flight).
#![allow(clippy::unwrap_used, clippy::too_many_lines, unreachable_pub)]

use std::fmt::Write as _;

use vinc_tests::SplitMix64;
use vinc_transport::conn::{MIN_MTU, MtuProbe, MtuView, PROBE_MTU};

const TOP: u64 = (1 << 31) - 1;

fn opt(x: Option<u64>) -> i128 {
    x.map_or(-1, i128::from)
}

fn view_json(v: &MtuView, wide: bool) -> String {
    let c = |t: u64| if wide { t } else { t.min(TOP) };
    format!(
        r#"{{"cur":{},"infl":{},"probed":{},"jdone":{},"retry":{},"started":{},"lbig":{},"backed":{},"pbig":{},"susp":[{},{}]}}"#,
        v.current,
        v.inflight.map_or(-1, i64::from),
        v.probed,
        v.jumbo_done,
        c(v.retry_at),
        v.started,
        opt(v.last_big),
        opt(v.big_acked),
        opt(v.ping_big),
        v.suspect.map_or(-1, |(b, _)| i128::from(b)),
        v.suspect.map_or(0, |(_, a)| c(a))
    )
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, wide: bool) {
    let mut p = MtuProbe::new();
    let mut now = 1u64;
    let log = |p: &MtuProbe, out: &mut String, body: &str| {
        let _ = writeln!(
            out,
            r#"{{"t":"txmt","run":{id},{body},"v":{}}}"#,
            view_json(&p.view(), wide)
        );
    };
    let _ = writeln!(
        out,
        r#"{{"t":"txmt","run":{id},"op":"init","v":{}}}"#,
        view_json(&p.view(), wide)
    );
    let sizes = [1200u16, PROBE_MTU, 3000, 8952, 9000];
    let mut pn = 0u64;
    for _ in 0..steps {
        let before = p.view();
        match rng.next_u64() % 100 {
            0..=5 => {
                p.start();
                log(&p, out, r#""op":"start""#);
            }
            6..=14 => {
                now = if wide {
                    now.saturating_add([0, 1, 1_000_000, 700_000_000_000, 1 << 50][(rng.next_u64() % 5) as usize])
                } else {
                    (now + [0u64, 1, 1_000_000][(rng.next_u64() % 3) as usize]).min(1_900_000_000)
                };
                let allowed = rng.next_u64() % 8 != 0;
                let im = sizes[(rng.next_u64() % 5) as usize];
                let ll = rng.next_u64() % 2 == 0;
                let r = p.target(allowed, im, ll, now);
                if let Some(s) = r {
                    assert!(allowed && before.started && before.inflight.is_none() && before.retry_at <= now);
                    assert!(s > before.current, "a probe at or below the datagram size is due");
                }
                log(
                    &p,
                    out,
                    &format!(
                        r#""op":"target","allowed":{allowed},"im":{im},"ll":{ll},"now":{now},"r":{}"#,
                        r.map_or(-1, i64::from)
                    ),
                );
            }
            15..=34 => {
                // send what is due, as the connection does
                let ll = rng.next_u64() % 2 == 0;
                let im = sizes[(rng.next_u64() % 5) as usize];
                if let Some(s) = p.target(true, im, ll, now) {
                    p.probe_sent(s);
                    log(&p, out, &format!(r#""op":"sent","size":{s}"#));
                }
            }
            35..=49 => {
                let s = sizes[(rng.next_u64() % 5) as usize];
                let r = p.raise(s);
                let after = p.view();
                assert_eq!(r.is_some(), s > before.current);
                assert!(after.current >= MIN_MTU);
                log(
                    &p,
                    out,
                    &format!(r#""op":"raise","size":{s},"r":{}"#, r.map_or(-1, i64::from)),
                );
            }
            50..=59 => {
                let s = sizes[(rng.next_u64() % 5) as usize];
                p.probe_lost(s, now);
                log(&p, out, &format!(r#""op":"lost","size":{s},"now":{now}"#));
            }
            60..=66 => {
                p.event();
                log(&p, out, r#""op":"event""#);
            }
            67..=78 => {
                pn += 1 + rng.next_u64() % 3;
                let pick = |rng: &mut SplitMix64, v: u64| {
                    if rng.next_u64() % 3 == 0 {
                        None
                    } else {
                        Some(v.saturating_sub(rng.next_u64() % 4))
                    }
                };
                let lb = pick(rng, pn);
                let ba = pick(rng, pn);
                let pb = pick(rng, pn);
                p.set_big(lb, ba, pb);
                log(
                    &p,
                    out,
                    &format!(r#""op":"big","lb":{},"ba":{},"pb":{}"#, opt(lb), opt(ba), opt(pb)),
                );
            }
            79..=89 => {
                let rtt = if wide {
                    [0u64, 4_000_000, u64::MAX][(rng.next_u64() % 3) as usize]
                } else {
                    [0u64, 4_000_000][(rng.next_u64() % 2) as usize]
                };
                p.black_hole(now, rtt);
                log(&p, out, &format!(r#""op":"bh","now":{now},"rtt":{rtt}"#));
            }
            _ => {
                now = if wide {
                    now.saturating_add(10_000_000)
                } else {
                    (now + 10_000_000).min(1_900_000_000)
                };
                let dropped = p.black_hole_check(now);
                let after = p.view();
                if dropped {
                    assert_eq!(after.current, MIN_MTU);
                    assert!(after.inflight.is_none() && after.probed && after.jumbo_done && after.suspect.is_none());
                } else {
                    assert_eq!(after.current, before.current, "the size changed without the fallback");
                }
                log(&p, out, &format!(r#""op":"bhc","now":{now},"r":{dropped}"#));
            }
        }
        assert!(p.view().current >= MIN_MTU);
    }
}

#[test]
fn path_mtu_runs_match_the_models() {
    let mut rng = SplitMix64::new(0x4d54_0001);
    let mut out = String::new();
    for id in 1..=60u32 {
        run(&mut rng, &mut out, id, 300, false);
    }
    let mut wide = String::new();
    for id in 901..=930u32 {
        run(&mut rng, &mut wide, id, 300, true);
    }
    for needle in [
        r#""op":"target""#,
        r#""op":"sent""#,
        r#""op":"raise""#,
        r#""op":"lost""#,
        r#""op":"bh""#,
        r#""op":"bhc""#,
        r#""r":true"#,
    ] {
        assert!(
            out.contains(needle) || wide.contains(needle),
            "the runs never reach {needle}"
        );
    }
    assert!(
        out.lines()
            .chain(wide.lines())
            .any(|l| l.contains(r#""op":"bhc""#) && l.contains(r#""r":true,"#)),
        "the fallback is never taken"
    );
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("mtu.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("mtu_wide.ndjson"), &wide).unwrap();
    }
}
