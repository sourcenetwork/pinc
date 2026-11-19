//! Trace generation for the keepalive schedule: seeded and boundary inputs run through the real `Inputs::plan` and
//! `standby_due` of `pinc-core`, recorded as ndjson (`keepalive.ndjson`) for the TLA+ trace check
//! (`TraceKeepalive.tla`) and the Lean replay (`Pinc/TraceKeepalive.lean`).
//!
//! A `u64` is written as four 16-bit limbs (TLC cannot read a number above 2^31). The inputs take every role, side
//! and path kind; the clock, the last send, the last receive, the last application data and the end of the quiet
//! period are drawn from a base time and offsets that land one nanosecond either side of every constant of the
//! schedule (5, 10, 14, 20, 40, 60, 70, 90 and 120 s), with bases at 0, around 100 s and up to `u64::MAX` so that
//! every addition saturates. Every plan is compared here with a naive one written from the module documentation (a
//! list of candidate deadlines in `u128`), and its documented bounds are asserted: never before `now`, never before
//! 5 s after the last send, the review moment after `now`.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::indexing_slicing,
    clippy::cast_sign_loss,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_core::{
    ACTIVE_KEEP, DIRECT_SILENCE, HOLD_WINDOW, IDLE_DROP, IDLE_KEEP, KeepaliveInputs, PATH_KEEP, QUIET_KEEP_ACCEPTOR,
    QUIET_KEEP_DIALER, Role, standby_due,
};
use pinc_tests::SplitMix64;

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

fn sat(a: u64, b: u64) -> u128 {
    u128::from(a.saturating_add(b))
}

/// The plan as the module documentation describes it, in `u128`.
fn naive(i: &KeepaliveInputs) -> (Option<u128>, Option<u128>) {
    let now = u128::from(i.now);
    let quiet = i.role.quiet();
    let keep = match (quiet, i.dialer) {
        (true, true) => QUIET_KEEP_DIALER,
        (true, false) => QUIET_KEEP_ACCEPTOR,
        (false, _) => IDLE_KEEP,
    };
    let mut pings: Vec<u128> = Vec::new();
    let mut moments: Vec<u128> = Vec::new();
    let active_end = sat(i.last_app, ACTIVE_KEEP);
    let due5 = sat(i.last_tx, PATH_KEEP).max(now);
    if due5 < active_end {
        pings.push(due5);
    }
    moments.push(active_end);
    let idle_end = sat(i.last_app, IDLE_DROP);
    let idle = sat(i.last_tx, keep).max(now);
    if quiet || idle < idle_end {
        pings.push(idle);
    }
    if !quiet {
        moments.push(idle_end);
    }
    if quiet && i.dialer && i.direct {
        let hold_end = sat(i.last_app, HOLD_WINDOW);
        let d = sat(i.last_rx.max(i.last_tx), DIRECT_SILENCE).max(now);
        if d < hold_end {
            pings.push(d);
        }
        moments.push(hold_end);
    }
    let held = now < u128::from(i.quiet_until) && !i.in_flight;
    let mut ping = pings.into_iter().min();
    if held {
        ping = ping.map(|p| p.max(u128::from(i.quiet_until)));
        moments.push(u128::from(i.quiet_until));
    }
    let review = moments.into_iter().filter(|t| *t > now).min();
    (ping, review)
}

fn role_name(r: Role) -> &'static str {
    match r {
        Role::Hub => "hub",
        Role::Member => "member",
        Role::Other => "other",
    }
}

/// An offset that lands next to a constant of the schedule.
fn offset(rng: &mut SplitMix64) -> i128 {
    const K: [u64; 12] = [0, 5, 10, 14, 20, 40, 60, 70, 90, 120, 3, 75];
    let base = i128::from(K[(rng.next_u64() % 12) as usize] * S);
    let edge = match rng.next_u64() % 5 {
        0 => -1,
        1 => 1,
        _ => 0,
    };
    let v = base + edge;
    if rng.next_u64().is_multiple_of(2) { v } else { -v }
}

fn around(rng: &mut SplitMix64, base: u64) -> u64 {
    match rng.next_u64() % 6 {
        0 => base,
        1 => rng.next_u64() % (200 * S),
        _ => {
            let v = i128::from(base) + offset(rng);
            v.clamp(0, i128::from(u64::MAX)) as u64
        }
    }
}

#[test]
fn the_keepalive_plan_matches_the_models() {
    let mut rng = SplitMix64::new(0x6b65_6570_616c_6976);
    let mut out = String::new();
    let (mut some, mut none, mut held_n, mut direct_n, mut stopped, mut reviews) = (0u32, 0u32, 0u32, 0u32, 0u32, 0u32);
    for n in 0..12_000u32 {
        let base = match n % 8 {
            0 => 0,
            1 | 2 => 100 * S,
            3 => u64::MAX,
            4 => (u64::MAX - 130 * S).saturating_add(rng.next_u64() % (260 * S)),
            5 => 1 << 40,
            _ => rng.next_u64() % (400 * S),
        };
        let role = [Role::Hub, Role::Member, Role::Other][(rng.next_u64() % 3) as usize];
        let now = around(&mut rng, base);
        let i = KeepaliveInputs {
            role,
            dialer: rng.next_u64().is_multiple_of(2),
            direct: !rng.next_u64().is_multiple_of(3),
            now,
            last_tx: around(&mut rng, now),
            last_rx: around(&mut rng, now),
            last_app: around(&mut rng, now),
            quiet_until: if rng.next_u64().is_multiple_of(3) {
                around(&mut rng, now)
            } else {
                0
            },
            in_flight: rng.next_u64().is_multiple_of(3),
        };
        let p = i.plan();
        let (np, nr) = naive(&i);
        assert_eq!(
            p.ping_at.map(u128::from),
            np,
            "ping differs from the naive plan for {i:?}"
        );
        assert_eq!(
            p.review_at.map(u128::from),
            nr,
            "review differs from the naive plan for {i:?}"
        );
        if let Some(t) = p.ping_at {
            assert!(t >= i.now, "a ping before now: {i:?}");
            assert!(
                u128::from(t) >= sat(i.last_tx, PATH_KEEP),
                "a ping within 5 s of the last send: {i:?}"
            );
            some += 1;
            if now < i.quiet_until && !i.in_flight {
                assert!(t >= i.quiet_until, "a ping during the quiet period: {i:?}");
                held_n += 1;
            }
            if i.role.quiet() && i.dialer && i.direct {
                direct_n += 1;
            }
        } else {
            none += 1;
            assert!(!i.role.quiet(), "a quiet session without a ping: {i:?}");
            if u128::from(i.now) >= sat(i.last_app, IDLE_DROP) {
                stopped += 1;
            }
        }
        if let Some(r) = p.review_at {
            assert!(r > i.now, "a review moment not after now: {i:?}");
            reviews += 1;
            // the plan at a later now below the review moment is the same, raised to it
            if r - i.now > 1 {
                let later = i.now + (r - i.now) / 2;
                let q = KeepaliveInputs { now: later, ..i }.plan();
                assert_eq!(q.review_at, p.review_at, "the review moment moved before it: {i:?}");
                assert_eq!(
                    q.ping_at,
                    p.ping_at.map(|t| t.max(later)),
                    "the ping moved before the review: {i:?}"
                );
            }
        }
        let _ = writeln!(
            out,
            r#"{{"t":"cka","op":"plan","role":"{}","dialer":{},"direct":{},"now":{},"tx":{},"rx":{},"app":{},"qu":{},"flight":{},"ping":{},"review":{}}}"#,
            role_name(i.role),
            i.dialer,
            i.direct,
            limbs(i.now),
            limbs(i.last_tx),
            limbs(i.last_rx),
            limbs(i.last_app),
            limbs(i.quiet_until),
            i.in_flight,
            opt(p.ping_at),
            opt(p.review_at),
        );
        if n % 4 == 0 {
            let d = standby_due(i.now, i.last_tx, i.last_app);
            let want = {
                let due = sat(i.last_tx, PATH_KEEP).max(u128::from(i.now));
                (due < sat(i.last_app, ACTIVE_KEEP)).then_some(due)
            };
            assert_eq!(d.map(u128::from), want, "standby_due differs for {i:?}");
            let _ = writeln!(
                out,
                r#"{{"t":"cka","op":"standby","now":{},"tx":{},"app":{},"due":{}}}"#,
                limbs(i.now),
                limbs(i.last_tx),
                limbs(i.last_app),
                opt(d)
            );
        }
    }
    // every kind of answer was reached
    assert!(some > 1500 && none > 150 && held_n > 60 && direct_n > 150 && stopped > 30 && reviews > 1500);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(format!("{dir}/keepalive.ndjson"), out).unwrap();
    }
}
