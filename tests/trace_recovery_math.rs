//! Trace generation for the recovery integer helpers (`pinc-transport`, built with the `trace` feature): the real
//! `sat` and `icbrt`, recorded as ndjson (`recovery_math.ndjson`) for the TLA+ trace check
//! (`TraceRecoveryMath.tla`).
//!
//! `icbrt` is recorded for every n below 2000, the cubes and their neighbours, the powers of two and their
//! neighbours and seeded values, all below 2^30 (TLC's integers are 32 bits wide); above that it is only asserted,
//! up to `u128::MAX`, with `u128` arithmetic. `sat` is recorded as 8 little-endian 16-bit limbs in and 4 out.
//!
//! The test checks the definitions itself (the floor cube root, the saturating narrowing), so it is meaningful
//! without the proof tools. The trace is written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::recovery::trace::{icbrt, sat};

/// `r` is the floor cube root of `n`.
fn assert_floor_cbrt(n: u128, r: u64) {
    assert!(r < 1 << 43, "a root of 43 bits or more");
    assert!(u128::from(r).checked_pow(3).is_some_and(|c| c <= n), "r^3 is above n");
    assert!(
        u128::from(r + 1).checked_pow(3).is_none_or(|c| c > n),
        "(r + 1)^3 is not above n"
    );
}

/// `limbs` little-endian 16-bit limbs of `v`.
fn limbs(v: u128, count: usize) -> String {
    let l: Vec<String> = (0..count).map(|i| ((v >> (16 * i)) & 0xffff).to_string()).collect();
    l.join(",")
}

/// A recorded and checked `icbrt` of `n < 2^30`.
fn rec_icbrt(out: &mut String, n: u64) {
    assert!(n < 1 << 30);
    let r = icbrt(u128::from(n));
    assert_floor_cbrt(u128::from(n), r);
    assert!(r < 1024);
    let _ = writeln!(out, r#"{{"t":"icbrt","n":{n},"r":{r}}}"#);
}

/// A recorded and checked `sat`; whether it saturated.
fn rec_sat(out: &mut String, v: u128) -> bool {
    let r = sat(v);
    if v <= u128::from(u64::MAX) {
        assert_eq!(u128::from(r), v);
    } else {
        assert_eq!(r, u64::MAX);
    }
    let _ = writeln!(
        out,
        r#"{{"t":"sat","v":[{}],"r":[{}]}}"#,
        limbs(v, 8),
        limbs(u128::from(r), 4)
    );
    v > u128::from(u64::MAX)
}

/// A seeded `u128`: random bits shifted down by a random amount, so every magnitude comes.
fn wide(rng: &mut SplitMix64) -> u128 {
    let v = (u128::from(rng.next_u64()) << 64) | u128::from(rng.next_u64());
    v >> (rng.next_u64() % 128)
}

#[test]
fn the_recovery_math_matches_the_model() {
    let mut rng = SplitMix64::traced(0x6d61_7468);
    let mut out = String::new();

    // icbrt, recorded
    for n in 0..2000u64 {
        rec_icbrt(&mut out, n);
    }
    for k in 0..=1023u64 {
        let c = k * k * k;
        if let Some(below) = c.checked_sub(1) {
            rec_icbrt(&mut out, below);
        }
        rec_icbrt(&mut out, c);
        rec_icbrt(&mut out, c + 1);
    }
    for j in 0..30 {
        let p = 1u64 << j;
        if let Some(below) = p.checked_sub(1) {
            rec_icbrt(&mut out, below);
        }
        rec_icbrt(&mut out, p);
        rec_icbrt(&mut out, p + 1);
    }
    rec_icbrt(&mut out, (1 << 30) - 1);
    for _ in 0..2000 {
        let n = rng.next_u64() % (1 << 30);
        rec_icbrt(&mut out, n);
    }

    // icbrt, asserted only
    let check = |n: u128| assert_floor_cbrt(n, icbrt(n));
    for j in 30..128 {
        let p = 1u128 << j;
        check(p - 1);
        check(p);
        check(p + 1);
    }
    check(u128::MAX);
    let kmax = icbrt(u128::MAX);
    assert!(u128::from(kmax).checked_pow(3).is_some(), "kmax^3 does not fit");
    assert!(u128::from(kmax + 1).checked_pow(3).is_none(), "(kmax + 1)^3 fits");
    for k in [1u64 << 41, (1 << 42) - 1, 1 << 42, (1 << 42) + 1, kmax - 1, kmax] {
        if let Some(c) = u128::from(k).checked_pow(3) {
            check(c - 1);
            check(c);
            if let Some(up) = c.checked_add(1) {
                check(up);
            }
        }
    }
    for _ in 0..2000 {
        check(wide(&mut rng));
    }

    // sat, recorded
    let (mut saturated, mut kept) = (0u32, 0u32);
    let max = u128::from(u64::MAX);
    let fixed = [
        0,
        1,
        65535,
        65536,
        max - 1,
        max,
        max + 1,
        1 << 64,
        (1 << 64) + 5,
        1 << 127,
        u128::MAX,
    ];
    let seeded: Vec<u128> = (0..1000).map(|_| wide(&mut rng)).collect();
    for v in fixed.into_iter().chain(seeded) {
        if rec_sat(&mut out, v) {
            saturated += 1;
        } else {
            kept += 1;
        }
    }
    assert!(saturated > 0 && kept > 0, "sat never saturated, or always did");

    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("recovery_math.ndjson"), &out).unwrap();
    }
}
