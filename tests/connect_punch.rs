//! Hole punching: the REACH_OUT body, the probe schedule and the punch timer.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::many_single_char_names
)]

use std::net::SocketAddr;

use proptest::prelude::*;
use vinc_connect::client::punch::{
    ACTIVE_KEEP, FIRST_DELAY, GOOD_LATENCY, PROBES, Puncher, Step, UPGRADE_INTERVAL, View, decode, encode, probe_gaps,
};

const S: u64 = 1_000_000_000;
const MS: u64 = 1_000_000;

#[test]
fn nine_probes_from_max_33ms_or_srtt_over_8_doubling_to_2s() {
    assert_eq!(PROBES, 9);
    let g = probe_gaps(0);
    assert_eq!(g[0], 33_300_000);
    assert_eq!(g[1], 66_600_000);
    assert_eq!(g[8], 2 * S, "33.3 ms doubled eight times is capped at 2 s");
    let g = probe_gaps(400 * MS);
    assert_eq!(g[0], 50 * MS, "srtt / 8");
    assert_eq!(g[1], 100 * MS);
    assert_eq!(g[2], 200 * MS);
    assert_eq!(g[5], 1600 * MS);
    assert_eq!(g[6], 2 * S);
    // 8 x 33.3 ms = 266.4 ms is still the floor
    assert_eq!(probe_gaps(266 * MS)[0], 33_300_000);
    assert_eq!(probe_gaps(8 * 33_300_001)[0], 33_300_001);
}

fn addrs(n: usize) -> Vec<SocketAddr> {
    (0..n)
        .map(|i| {
            if i % 2 == 0 {
                SocketAddr::from(([10, 0, 0, i as u8], 4000 + i as u16))
            } else {
                SocketAddr::from(([0x2001, 0xdb8, 0, 0, 0, 0, 0, i as u16], 5000 + i as u16))
            }
        })
        .collect()
}

#[test]
fn reach_out_carries_up_to_eight_candidates() {
    for n in 0..=8 {
        let a = addrs(n);
        let mut b = [0u8; vinc_core::REACH_BODY_MAX];
        let len = encode(&a, &mut b).unwrap();
        let mut out = [SocketAddr::from(([0, 0, 0, 0], 0)); 8];
        assert_eq!(decode(&b[..len], &mut out), Some(n));
        assert_eq!(&out[..n], &a[..]);
        assert!(len <= vinc_core::REACH_BODY_MAX);
    }
    // a ninth is cut off at encode, refused at decode
    let a = addrs(9);
    let mut b = [0u8; vinc_core::REACH_BODY_MAX];
    let len = encode(&a, &mut b).unwrap();
    assert_eq!(b[0], 8);
    let mut body = b[..len].to_vec();
    body[0] = 9;
    let mut out = [SocketAddr::from(([0, 0, 0, 0], 0)); 8];
    assert_eq!(decode(&body, &mut out), None);
    // trailing bytes and truncation are malformed
    let mut ok = b[..len].to_vec();
    ok.push(0);
    assert_eq!(decode(&ok, &mut out), None);
    assert_eq!(decode(&b[..len - 1], &mut out), None);
    assert_eq!(decode(&[], &mut out), None);
}

proptest! {
    #[test]
    fn reach_out_decode_never_panics(body in proptest::collection::vec(any::<u8>(), 0..200)) {
        let mut out = [SocketAddr::from(([0, 0, 0, 0], 0)); 8];
        let _ = decode(&body, &mut out);
    }
}

fn view(idle: u64, direct: bool, rtt: u64, quiet: u64) -> View {
    View {
        app_idle: idle,
        direct,
        rtt,
        quiet_until: quiet,
    }
}

#[test]
fn punch_one_ms_after_establishment_then_every_60s() {
    let mut p = Puncher::off();
    assert_eq!(p.deadline(), None);
    p.established(10 * S);
    assert_eq!(p.deadline(), Some(10 * S + FIRST_DELAY));
    let v = view(0, false, 0, 0);
    assert_eq!(p.due(10 * S + FIRST_DELAY - 1, &v), Step::Wait);
    assert_eq!(p.due(10 * S + FIRST_DELAY, &v), Step::Punch);
    assert_eq!(p.deadline(), Some(10 * S + FIRST_DELAY + UPGRADE_INTERVAL));
}

#[test]
fn a_direct_path_of_10ms_or_faster_ends_the_punching() {
    for (rtt, stops) in [(GOOD_LATENCY, true), (GOOD_LATENCY + 1, false), (MS, true)] {
        let mut p = Puncher::off();
        p.established(0);
        assert_eq!(p.due(FIRST_DELAY, &view(0, true, rtt, 0)), Step::Punch);
        assert_eq!(p.deadline().is_none(), stops, "rtt {rtt}");
    }
    // a relayed path never counts, however fast
    let mut p = Puncher::off();
    p.established(0);
    p.due(FIRST_DELAY, &view(0, false, MS, 0));
    assert!(p.deadline().is_some());
}

#[test]
fn an_idle_session_only_waits_and_a_quiet_window_defers() {
    let mut p = Puncher::off();
    p.established(0);
    assert_eq!(p.due(FIRST_DELAY, &view(ACTIVE_KEEP, false, 0, 0)), Step::Wait);
    assert_eq!(p.deadline(), Some(FIRST_DELAY + UPGRADE_INTERVAL));
    let mut p = Puncher::off();
    p.established(0);
    assert_eq!(p.due(FIRST_DELAY, &view(ACTIVE_KEEP - 1, false, 0, 0)), Step::Punch);
    // a direct path inside the quiet window after a resume is left alone until the window ends
    let mut p = Puncher::off();
    p.established(0);
    assert_eq!(p.due(FIRST_DELAY, &view(0, true, 50 * MS, 10 * S)), Step::Wait);
    assert_eq!(p.deadline(), Some(10 * S + 1));
    p.arm(0);
    assert_eq!(p.deadline(), None);
}
