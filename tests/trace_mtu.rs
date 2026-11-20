//! Trace generation for path MTU discovery: seeded runs of the real `Mtu` state machine of one path
//! (`pinc-transport`, built with the `trace` feature), recorded as ndjson (`mtu.ndjson`) for the TLA+ trace check
//! (`TraceMtu.tla`) and the Lean replay (`Pinc/TraceMtu.lean`).
//!
//! A run starts discovery and then makes the calls the connection makes: asks which size is due (with the path
//! allowed or not, interface sizes from the minimum to a jumbo frame, low latency or not), sends a probe of the due
//! size as a packet number, acknowledges, echoes or loses it, flushes it and acknowledges the flush's probe, raises a
//! path event, notes the full-size packets, suspects a black hole and settles the suspicion. Every outcome is
//! pn-matched, as in the code: an acknowledgement, loss or flush applies only when it names the probe in flight, an
//! echo only when a probe of exactly that size is in flight and under the path's ceiling, a flush's acknowledgement
//! only when it names the probe the flush took. After every call the machine shows its state. A second file
//! (`mtu_wide.ndjson`, read by the Lean replay only: the TLA+ checker has 32-bit integers and the lost-probe wait is
//! 600 s) takes times up to `u64::MAX`.
//!
//! The test asserts what it can itself (the size never falls below the floor, rises only by a raise, falls only to
//! the floor by the black-hole fallback, a probe is due only when none is in flight, a rise leaves nothing in
//! flight, a flush mark only with nothing in flight).
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::conn::{HEADERS_V4, JUMBO_MTU, MIN_MTU, MtuProbe, MtuView, PROBE_MTU, Rose};

const TOP: u64 = (1 << 31) - 1;

fn opt(x: Option<u64>) -> i128 {
    x.map_or(-1, i128::from)
}

/// A probe in flight or kept by a flush, as `-1` or a `[size, pn]` pair.
fn pair(x: Option<(u16, u64)>) -> String {
    match x {
        None => "-1".to_string(),
        Some((s, p)) => format!("[{s},{p}]"),
    }
}

fn view_json(v: &MtuView, wide: bool) -> String {
    let c = |t: u64| if wide { t } else { t.min(TOP) };
    format!(
        r#"{{"cur":{},"infl":{},"flushed":{},"probed":{},"jdone":{},"retry":{},"started":{},"lbig":{},"backed":{},"pbig":{},"susp":[{},{}]}}"#,
        v.current,
        pair(v.inflight),
        pair(v.flushed),
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
    let mut pn = 0u64;
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
    for _ in 0..steps {
        let before = p.view();
        match rng.next_u64() % 100 {
            0..=5 => {
                p.start();
                log(&p, out, r#""op":"start""#);
            }
            6..=13 => {
                now = if wide {
                    now.saturating_add([0, 1, 1_000_000, 700_000_000_000, 1 << 50][(rng.next_u64() % 5) as usize])
                } else {
                    (now + [0u64, 1, 1_000_000][(rng.next_u64() % 3) as usize]).min(1_900_000_000)
                };
                let allowed = !rng.next_u64().is_multiple_of(8);
                let im = sizes[(rng.next_u64() % 5) as usize];
                let ll = rng.next_u64().is_multiple_of(2);
                let r = p.target(allowed, im + HEADERS_V4, false, ll, now);
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
            14..=30 => {
                // send what is due, as the connection does, as a fresh packet number
                let ll = rng.next_u64().is_multiple_of(2);
                let im = sizes[(rng.next_u64() % 5) as usize];
                if let Some(s) = p.target(true, im + HEADERS_V4, false, ll, now) {
                    pn += 1 + rng.next_u64() % 3;
                    p.probe_sent(s, pn);
                    log(&p, out, &format!(r#""op":"sent","size":{s},"pn":{pn}"#));
                }
            }
            31..=42 => {
                // an echo: the connection raises only when a probe of exactly that size is in flight and the
                // smaller of the jumbo size and the interface's payload can carry it
                let s = sizes[(rng.next_u64() % 5) as usize];
                let im = sizes[(rng.next_u64() % 5) as usize];
                // `im` plays the interface's payload here, as in `target` above
                let ceiling = im.min(JUMBO_MTU);
                if before.inflight.is_some_and(|(sz, _)| sz == s) && s <= ceiling {
                    let r = p.raise(s);
                    assert_eq!(r.is_some(), s > before.current);
                    log(
                        &p,
                        out,
                        &format!(r#""op":"raise","size":{s},"r":{}"#, r.map_or(-1, i64::from)),
                    );
                }
            }
            43..=54 => {
                let s = sizes[(rng.next_u64() % 5) as usize];
                let at = pn.saturating_sub(rng.next_u64() % 4);
                let r = p.acked(s, at);
                assert!(after_floor(&p));
                // `-2` for a refusal (the acknowledgement names another probe), `-1` for a flat one (it names the
                // probe in flight but does not raise the size), else the size that rose.
                let r = match r {
                    None => -2,
                    Some(Rose::Flat) => -1,
                    Some(Rose::New(s)) => i64::from(s),
                };
                log(&p, out, &format!(r#""op":"ack","size":{s},"pn":{at},"r":{r}"#));
            }
            55..=63 => {
                let s = sizes[(rng.next_u64() % 5) as usize];
                let at = pn.saturating_sub(rng.next_u64() % 4);
                let applied = p.probe_lost(s, at, now);
                if applied {
                    assert!(p.view().retry_at > now, "an applied loss left no wait");
                }
                log(
                    &p,
                    out,
                    &format!(r#""op":"lost","size":{s},"pn":{at},"now":{now},"applied":{applied}"#),
                );
            }
            64..=70 => {
                let s = sizes[(rng.next_u64() % 5) as usize];
                let at = pn.saturating_sub(rng.next_u64() % 4);
                let applied = p.flush(s, at);
                if applied {
                    let after = p.view();
                    assert!(after.inflight.is_none() && after.flushed.is_some());
                }
                log(
                    &p,
                    out,
                    &format!(r#""op":"flush","size":{s},"pn":{at},"applied":{applied}"#),
                );
            }
            71..=77 => {
                let at = pn.saturating_sub(rng.next_u64() % 4);
                let r = p.flushed_acked(at);
                assert!(after_floor(&p));
                log(
                    &p,
                    out,
                    &format!(r#""op":"fack","pn":{at},"r":{}"#, r.map_or(-1, i64::from)),
                );
            }
            78..=82 => {
                p.event();
                log(&p, out, r#""op":"event""#);
            }
            83..=89 => {
                pn += 1 + rng.next_u64() % 3;
                let pick = |rng: &mut SplitMix64, v: u64| {
                    if rng.next_u64().is_multiple_of(3) {
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
            90..=94 => {
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
                    assert!(
                        after.flushed.is_none(),
                        "the fallback kept the mark of the probe the flush took"
                    );
                } else {
                    assert_eq!(after.current, before.current, "the size changed without the fallback");
                }
                log(&p, out, &format!(r#""op":"bhc","now":{now},"r":{dropped}"#));
            }
        }
        let v = p.view();
        assert!(v.current >= MIN_MTU);
        assert!(
            v.flushed.is_none() || v.inflight.is_none(),
            "a flush mark beside a probe in flight"
        );
    }
}

fn after_floor(p: &MtuProbe) -> bool {
    p.view().current >= MIN_MTU
}

#[test]
fn path_mtu_runs_match_the_models() {
    let mut rng = SplitMix64::traced(0x4d54_0001);
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
        r#""op":"ack""#,
        r#""op":"flush""#,
        r#""op":"fack""#,
        r#""op":"lost""#,
        r#""op":"bh""#,
        r#""op":"bhc""#,
        r#""r":true"#,
        r#""applied":true"#,
    ] {
        assert!(
            pinc_tests::soaking() || out.contains(needle) || wide.contains(needle),
            "the runs never reach {needle}"
        );
    }
    assert!(
        pinc_tests::soaking()
            || out
                .lines()
                .chain(wide.lines())
                .any(|l| l.contains(r#""op":"bhc""#) && l.contains(r#""r":true,"#)),
        "the fallback is never taken"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("mtu.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("mtu_wide.ndjson"), &wide).unwrap();
    }
}
