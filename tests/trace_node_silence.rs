//! Trace generation for the silence bound of the node (`pinc_node::bound`), recorded as ndjson (`silence.ndjson`) for
//! the TLA+ trace check (`TraceNodeSilence.tla`).
//!
//! The two functions are pure: `give_up` (the silence after which the transport gives a path up) and `heal_after`
//! (a keepalive plus that). The run feeds both the round-trip points the model enumerates (0, the edges of every
//! power of two, the edges of the constants of the formula) with `thin` both ways, the keepalives 0, 60 s, 70 s and
//! the top of the range, and seeded random inputs, and records every answer. The test checks the floor, the growth
//! and the sum itself, and a few literal values worked out by hand.
#![allow(clippy::indexing_slicing)]
#![allow(clippy::unwrap_used, clippy::cast_possible_truncation, unreachable_pub)]

use std::collections::BTreeSet;
use std::fmt::Write as _;

use pinc_core::{QUIET_KEEP_ACCEPTOR, QUIET_KEEP_DIALER};
use pinc_node::bound::{give_up, heal_after};
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

fn give_line(out: &mut String, srtt: u64, thin: bool) {
    let r = give_up(srtt, thin);
    writeln!(
        out,
        "{{\"t\":\"sil\",\"op\":\"give\",\"srtt\":{},\"thin\":{thin},\"r\":{}}}",
        limbs(srtt),
        limbs(r)
    )
    .unwrap();
}

fn heal_line(out: &mut String, keep: u64, srtt: u64, thin: bool) {
    let r = heal_after(keep, srtt, thin);
    writeln!(
        out,
        "{{\"t\":\"sil\",\"op\":\"heal\",\"keep\":{},\"srtt\":{},\"thin\":{thin},\"r\":{}}}",
        limbs(keep),
        limbs(srtt),
        limbs(r)
    )
    .unwrap();
}

/// The round-trip points of `NodeSilence.tla`.
fn points() -> BTreeSet<u64> {
    let mut p = BTreeSet::new();
    p.insert(0);
    for j in 0..=64u32 {
        p.insert(if j == 64 { u64::MAX } else { (1u64 << j) - 1 });
    }
    for j in 0..=63u32 {
        p.insert(1u64 << j);
        p.insert((1u64 << j) + 1);
    }
    for v in [500_000u64, 333_000_000, 1_000_000_000, 2_000_000_000, 2_500_000_000] {
        p.extend([v - 1, v, v + 1]);
    }
    p.extend([10_000_000, 50_000_000, 200_000_000, 3_000_000_000]);
    p
}

#[test]
fn silence_bound() {
    let pts = points();
    let keeps = [0, QUIET_KEEP_DIALER, QUIET_KEEP_ACCEPTOR, u64::MAX - 1, u64::MAX];
    let mut out = String::new();

    for &s in &pts {
        for thin in [false, true] {
            give_line(&mut out, s, thin);
            let g = give_up(s, thin);
            let eff = if s == 0 { 333_000_000 } else { s };
            assert!(
                g >= eff.saturating_mul(8),
                "give_up({s}, {thin}) = {g} is below eight round trips"
            );
            if s >= 1_000_000_000 || thin {
                assert!(g >= 20_000_000_000, "give_up({s}, {thin}) = {g} is below 20 s");
            }
        }
    }
    for &s in &pts {
        for thin in [false, true] {
            for &k in &keeps {
                heal_line(&mut out, k, s, thin);
                check_heal(k, s, thin);
            }
        }
    }

    for thin in [false, true] {
        assert_eq!(
            give_up(0, thin),
            give_up(333_000_000, thin),
            "an unsampled path is the seeded round trip"
        );
        let mut last = 0;
        for &s in pts.iter().filter(|&&s| s != 0) {
            let g = give_up(s, thin);
            assert!(g >= last, "give_up shrank at srtt {s} (thin {thin}): {g} < {last}");
            last = g;
        }
    }

    // srtt 100 ms: base = 100 + 4 * 50 + 25 = 325 ms; wide = cap = 2 s; the timeouts are 325, 650, 1300 and then
    // 2000 ms seven times (2600 ms is cut to the cap): 2275 + 14000 = 16275 ms; need = 8 * 100 ms = 800 ms.
    assert_eq!(give_up(100_000_000, false), 16_275_000_000);
    // thin: need is 20 s, above the 16.275 s sum.
    assert_eq!(give_up(100_000_000, true), 20_000_000_000);
    assert_eq!(
        heal_after(QUIET_KEEP_DIALER, 100_000_000, false),
        QUIET_KEEP_DIALER + 16_275_000_000
    );

    let mut rng = SplitMix64::new(0x7369_6c00);
    for _ in 0..2000 {
        let x = rng.next_u64();
        let s = match x % 4 {
            0 => rng.next_u64(),
            1 => rng.next_u64() % 4_000_000_000,
            2 => rng.next_u64() % 1_000_000,
            _ => u64::MAX - rng.next_u64() % 1000,
        };
        let thin = rng.next_u64() & 1 == 1;
        give_line(&mut out, s, thin);
        let pick = rng.next_u64();
        let k = [0, QUIET_KEEP_DIALER, QUIET_KEEP_ACCEPTOR, rng.next_u64()][(pick % 4) as usize];
        heal_line(&mut out, k, s, thin);
        check_heal(k, s, thin);
    }

    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("silence.ndjson"), &out).unwrap();
    }
}

fn check_heal(k: u64, s: u64, thin: bool) {
    let h = heal_after(k, s, thin);
    assert_eq!(
        h,
        k.saturating_add(give_up(s, thin)),
        "heal_after({k}, {s}, {thin}) is not keepalive + give_up"
    );
    if k < u64::MAX {
        assert!(h > k, "heal_after({k}, {s}, {thin}) = {h} does not pass the keepalive");
    }
}
