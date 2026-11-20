//! Trace generation for the platform's time and the endpoint's clock (`platform.rs`, `drive.rs`): the arithmetic of
//! `HostInstant for u64` and for `std::time::Instant`, `ns_to_ms`, and the clock and instants of an endpoint on a
//! platform whose clock the test sets. Recorded as ndjson (`platform_time.ndjson`) for the TLA+ trace check
//! `TracePlatformTime.tla`.
//!
//! Every event is a call and its answer; the checks that need no model run beside them. The `iadd` events model the
//! decided fix of the `Instant` addition (the latest instant when the step does not fit); the check of their answer runs
//! after the file is written, so the trace is complete when it fails. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub,
    missing_docs
)]

use std::cell::Cell;
use std::collections::BTreeSet;
use std::convert::Infallible;
use std::fmt::Write as _;
use std::net::SocketAddr;
use std::rc::Rc;
use std::time::{Duration, Instant};

use pinc::{Endpoint, HostInstant, Hosted, Limits, Pinc, Platform, trace_ns_to_ms};
use pinc_tests::SplitMix64;

/// The first time the endpoint sees (`drive.rs` `T0`).
const T0: u64 = 10_000_000_000;

#[derive(Clone)]
struct Clock(Rc<Cell<u64>>);

impl Platform for Clock {
    type Instant = u64;
    type Error = Infallible;

    fn now(&self) -> u64 {
        self.0.get()
    }

    fn wall_ns(&self) -> u64 {
        1_700_000_000_000_000_000
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Infallible> {
        for (i, b) in (0u8..=255).cycle().zip(out) {
            *b = i.wrapping_mul(31).wrapping_add(7);
        }
        Ok(())
    }
}

/// An endpoint on `clock`, started at the clock's value now.
fn started(clock: &Clock) -> Endpoint<impl Hosted<Platform = Clock> + use<>> {
    Pinc::builder_on(clock.clone())
        .limits(Limits {
            connections: 4,
            ..Limits::default()
        })
        .build(
            async |_buf: &mut [u8]| -> Result<(usize, SocketAddr), Infallible> { core::future::pending().await },
            async |pkt: &[u8], _to: SocketAddr| -> Result<usize, Infallible> { Ok(pkt.len()) },
            async |_at: u64| {},
        )
        .unwrap()
}

fn l4(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn l8(v: u128) -> String {
    let limbs: Vec<String> = (0..8).map(|i| ((v >> (16 * i)) & 0xffff).to_string()).collect();
    format!("[{}]", limbs.join(","))
}

fn dur(d: Duration) -> String {
    format!("{{\"s\":{},\"n\":{}}}", l4(d.as_secs()), d.subsec_nanos())
}

/// A random `u64` of a random bit width.
fn rbits(rng: &mut SplitMix64) -> u64 {
    let w = rng.next_u64() % 64 + 1;
    rng.next_u64() >> (64 - w)
}

fn rdur(rng: &mut SplitMix64) -> Duration {
    Duration::new(rbits(rng), (rng.next_u64() % 1_000_000_000) as u32)
}

fn dur_of(m: u128) -> Duration {
    Duration::new((m / 1_000_000_000) as u64, (m % 1_000_000_000) as u32)
}

/// The largest step `t` can take.
fn latest(t: Instant) -> Duration {
    if t.checked_add(Duration::MAX).is_some() {
        return Duration::MAX;
    }
    let (mut lo, mut hi) = (0u128, Duration::MAX.as_nanos());
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if t.checked_add(dur_of(mid)).is_some() {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    dur_of(lo)
}

fn boundary() -> Vec<u64> {
    let mut s = BTreeSet::from([0, 1, u64::MAX - 1, u64::MAX]);
    for j in 1..64 {
        let p = 1u64 << j;
        s.extend([p - 1, p, p + 1]);
    }
    s.into_iter().collect()
}

#[test]
fn the_platform_time_matches_the_model() {
    let mut rng = SplitMix64::traced(0x7469_6d65);
    let mut out = String::new();
    let b = boundary();
    let (mut saturated_add, mut saturated_now, mut back_below, mut back_between, mut saturated_inst, mut clipped) =
        (0, 0, 0, 0, 0, 0);

    // uadd and usince
    let add = |out: &mut String, t: u64, d: Duration| -> u64 {
        let r = HostInstant::add(t, d);
        let want = (u128::from(t) + d.as_nanos()).min(u128::from(u64::MAX));
        assert_eq!(u128::from(r), want, "{t} + {d:?}");
        let _ = writeln!(
            out,
            "{{\"t\":\"time\",\"op\":\"uadd\",\"a\":{},\"d\":{},\"r\":{}}}",
            l4(t),
            l8(d.as_nanos()),
            l4(r)
        );
        r
    };
    let since = |out: &mut String, t: u64, e: u64| -> Duration {
        let r = HostInstant::since(t, e);
        assert_eq!(r.as_nanos(), u128::from(t.saturating_sub(e)), "since {t} {e}");
        let _ = writeln!(
            out,
            "{{\"t\":\"time\",\"op\":\"usince\",\"a\":{},\"e\":{},\"r\":{}}}",
            l4(t),
            l4(e),
            l8(r.as_nanos())
        );
        r
    };
    for &t in &b {
        let rest = Duration::from_nanos(u64::MAX - t);
        let ds = [
            Duration::ZERO,
            Duration::from_nanos(1),
            Duration::from_secs(1),
            Duration::from_nanos(u64::MAX),
            Duration::from_nanos(u64::MAX) + Duration::from_nanos(1),
            Duration::MAX,
            rest,
            rest + Duration::from_nanos(1),
        ];
        for d in ds {
            let r = add(&mut out, t, d);
            saturated_add += i32::from(r == u64::MAX && u128::from(t) + d.as_nanos() > u128::from(u64::MAX));
        }
    }
    for &t in &b {
        for &e in &b {
            since(&mut out, t, e);
        }
    }
    for _ in 0..2000 {
        let (t, d) = (rbits(&mut rng), rdur(&mut rng));
        let r = add(&mut out, t, d);
        saturated_add += i32::from(r == u64::MAX && u128::from(t) + d.as_nanos() > u128::from(u64::MAX));
        let back = since(&mut out, r, t);
        if u128::from(t) + d.as_nanos() <= u128::from(u64::MAX) {
            assert_eq!(back, d, "since(add(t, d), t) is d when the sum fits");
        }
    }
    for _ in 0..2000 {
        let (t, e) = (rbits(&mut rng), rbits(&mut rng));
        since(&mut out, t, e);
    }

    // ms
    let mut ms_in = b.clone();
    for k in [1u64, 2, 1000, 4295, 65535, 18_446_744_073_709] {
        ms_in.extend([k * 1_000_000 - 1, k * 1_000_000, k * 1_000_000 + 1]);
    }
    ms_in.extend((0..1000).map(|_| rbits(&mut rng)));
    for ns in ms_in {
        let r = trace_ns_to_ms(ns);
        assert_eq!(u128::from(r), Duration::from_nanos(ns).as_millis(), "ms of {ns}");
        let _ = writeln!(out, "{{\"t\":\"time\",\"op\":\"ms\",\"a\":{},\"r\":{}}}", l4(ns), l4(r));
    }

    // now and inst
    let mut starts = vec![
        0,
        1,
        T0,
        1 << 32,
        1 << 63,
        u64::MAX - 10_000_000_000,
        u64::MAX - 1,
        u64::MAX,
    ];
    starts.extend((0..4).map(|_| rbits(&mut rng)));
    for start in starts {
        let clock = Clock(Rc::new(Cell::new(start)));
        let ep = started(&clock);
        let mut last = start;
        for i in 1..=40 {
            let p = if i % 8 == 0 {
                let below = if rng.next_u64().is_multiple_of(2) && start > 0 {
                    start
                } else {
                    last.max(1)
                };
                rng.next_u64() % below
            } else {
                let step = match rng.next_u64() % 5 {
                    0 => 0,
                    1 => 1,
                    2 => 1_000_000_000,
                    3 => 1 << 40,
                    _ => u64::MAX - last,
                };
                last.saturating_add(step)
            };
            clock.0.set(p);
            let r = ep.trace_now();
            let want = (u128::from(T0) + u128::from(p.saturating_sub(start))).min(u128::from(u64::MAX));
            assert_eq!(u128::from(r), want, "now at {p} from {start}");
            assert!(r >= T0, "the clock is below its first time");
            saturated_now += i32::from(r == u64::MAX);
            back_below += i32::from(p < start && r == T0 && p < last);
            back_between += i32::from(p >= start && p < last);
            last = p;
            let _ = writeln!(
                out,
                "{{\"t\":\"time\",\"op\":\"now\",\"st\":{},\"a\":{},\"r\":{}}}",
                l4(start),
                l4(p),
                l4(r)
            );
        }
        let top = T0.saturating_add(u64::MAX - start);
        let mut ats = vec![0, T0 - 1, T0, T0 + 1, top, top.saturating_add(1), u64::MAX];
        ats.extend((0..20).map(|_| rbits(&mut rng)));
        for at in ats {
            let r = ep.trace_instant(at);
            let want = (u128::from(start) + u128::from(at.saturating_sub(T0))).min(u128::from(u64::MAX));
            assert_eq!(u128::from(r), want, "instant of {at} from {start}");
            saturated_inst += i32::from(
                r == u64::MAX && u128::from(start) + u128::from(at.saturating_sub(T0)) > u128::from(u64::MAX),
            );
            let _ = writeln!(
                out,
                "{{\"t\":\"time\",\"op\":\"inst\",\"st\":{},\"a\":{},\"r\":{}}}",
                l4(start),
                l4(at),
                l4(r)
            );
        }
    }

    // iadd: the model is the decided fix; the check of the answer comes after the file is written
    let t = Instant::now();
    let lat = latest(t);
    assert!(t.checked_add(lat).is_some());
    if lat < Duration::MAX {
        assert!(t.checked_add(lat + Duration::from_nanos(1)).is_none());
    }
    let mut ds = vec![
        Duration::ZERO,
        Duration::from_nanos(1),
        Duration::from_secs(1),
        Duration::new(u64::MAX, 0),
        Duration::MAX,
        lat,
        lat.saturating_mul(2),
        lat.saturating_add(lat / 2),
    ];
    ds.extend(lat.checked_add(Duration::from_nanos(1)));
    ds.extend((0..300).map(|_| rdur(&mut rng)));
    let mut bad = Vec::new();
    for d in ds {
        let t = Instant::now();
        let lat = latest(t);
        let r = HostInstant::add(t, d);
        let got = HostInstant::since(r, t);
        assert!(r >= t, "an instant moved back");
        if let Some(want) = t.checked_add(d) {
            assert_eq!(r, want, "{d:?} fits and the result is not the sum");
        } else {
            clipped += 1;
            if got != lat {
                bad.push((d, got, lat));
            }
        }
        let _ = writeln!(
            out,
            "{{\"t\":\"time\",\"op\":\"iadd\",\"d\":{},\"got\":{},\"lat\":{}}}",
            dur(d),
            dur(got),
            dur(lat)
        );
    }

    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("platform_time.ndjson"), &out).unwrap();
    }
    assert!(
        bad.is_empty(),
        "a step that does not fit did not give the latest instant: {bad:?}"
    );
    if !pinc_tests::soaking() {
        assert!(saturated_add > 0, "no uadd saturated");
        assert!(saturated_now > 0, "no now saturated");
        assert!(
            back_below > 0,
            "no now was read after the clock stepped back below the start"
        );
        assert!(
            back_between > 0,
            "no now was read after the clock went back above the start"
        );
        assert!(saturated_inst > 0, "no inst saturated");
        assert!(clipped > 0, "no iadd step failed to fit");
    }
}
