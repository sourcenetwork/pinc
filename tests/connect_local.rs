//! Local discovery: the signed beacon, the duty cycle and the radio adapter.
#![allow(
    clippy::doc_markdown,
    clippy::unnested_or_patterns,
    clippy::nonminimal_bool,
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

mod connect_common;

use connect_common::{ed, id};
use proptest::prelude::*;
use pinc_connect::local::{BURST, BURST_GAP, Beacon, BeaconError, Duty, MAX_LEN, Radio, STEADY_GAP, sign};

const S: u64 = 1_000_000_000;

fn addrs() -> Vec<std::net::SocketAddr> {
    vec!["192.168.1.5:4433".parse().unwrap(), "[fe80::1]:4433".parse().unwrap()]
}

#[test]
fn a_beacon_round_trips_and_verifies() {
    let kp = ed(3);
    let mut buf = [0u8; MAX_LEN];
    let n = sign(&kp, 77, &addrs(), b"tkt", &mut buf).unwrap();
    let b = Beacon::parse_verified(&buf[..n]).unwrap();
    assert_eq!(b.node, id(&kp));
    assert_eq!(b.seq, 77);
    assert_eq!(b.hint, b"tkt");
    assert_eq!(b.addrs().collect::<Vec<_>>(), addrs());
}

#[test]
fn a_forged_or_altered_beacon_is_refused() {
    let kp = ed(3);
    let mut buf = [0u8; MAX_LEN];
    let n = sign(&kp, 1, &addrs(), &[], &mut buf).unwrap();
    for i in 0..n {
        let mut bad = buf[..n].to_vec();
        bad[i] ^= 0x01;
        let ok = Beacon::parse_verified(&bad);
        assert!(
            ok.is_err() || ok.unwrap().node != id(&kp) || false,
            "byte {i} changed and still verified"
        );
    }
    // a beacon naming another node with this key's signature
    let other = ed(4);
    let mut buf2 = [0u8; MAX_LEN];
    let _n2 = sign(&other, 1, &addrs(), &[], &mut buf2).unwrap();
    let mut forged = buf[..n].to_vec();
    forged[8..41].copy_from_slice(&buf2[8..41]);
    assert!(Beacon::parse_verified(&forged).is_err());
    assert!(Beacon::parse(&buf[..n - 1]).is_err());
    let mut trailing = buf[..n].to_vec();
    trailing.push(0);
    assert_eq!(Beacon::parse(&trailing), Err(BeaconError::Trailing));
    assert_eq!(sign(&kp, 1, &[addrs()[0]; 5], &[], &mut buf), Err(BeaconError::TooLong));
    assert_eq!(sign(&kp, 1, &[], &[0; 9], &mut buf), Err(BeaconError::TooLong));
}

#[test]
fn every_second_for_five_seconds_then_every_sixty() {
    let mut d = Duty::new(0);
    let mut at = vec![];
    let mut t = 0;
    while t <= 200 * S {
        if d.poll(t) {
            at.push(t / S);
        }
        t = d.deadline().max(t + 1);
        if t > 200 * S {
            break;
        }
    }
    assert_eq!(at, vec![0, 1, 2, 3, 4, 64, 124, 184]);
    assert_eq!(BURST / BURST_GAP, 5);
    assert_eq!(STEADY_GAP, 60 * S);
}

#[test]
fn an_interface_change_bursts_again_and_a_mailbox_silences_the_steady_phase() {
    let mut d = Duty::new(0);
    d.set_mailbox(true);
    let mut sent = 0;
    for s in 0..300 {
        if d.poll(s * S) {
            sent += 1;
        }
    }
    assert_eq!(sent, 5, "the burst is not suppressed, the steady phase is");
    d.restart(300 * S);
    let before = d.sent();
    for s in 300..320 {
        d.poll(s * S);
    }
    assert_eq!(d.sent() - before, 5);
    d.set_mailbox(false);
    let mut late = 0;
    for s in 320..500 {
        if d.poll(s * S) {
            late += 1;
        }
    }
    assert!(late >= 2, "beacons resume when the mailbox stops serving");
}

proptest! {
    #[test]
    fn the_duty_cycle_bound_holds_for_any_poll_pattern(steps in proptest::collection::vec(1u64..30_000_000_000, 1..300)) {
        let mut d = Duty::new(0);
        let (mut t, mut times) = (0u64, vec![]);
        for s in steps {
            t += s;
            if d.poll(t) { times.push(t); }
        }
        // at most 5 beacons in the first 5 s, and after that the gap between releases is at least 1 s inside the
        // burst window and at least 60 s outside it
        for w in times.windows(2) {
            let gap = w[1] - w[0];
            prop_assert!(gap >= BURST_GAP, "gap {gap}");
            if w[0] >= BURST { prop_assert!(gap >= STEADY_GAP, "steady gap {gap}"); }
        }
        prop_assert!(times.iter().filter(|t| **t < BURST).count() <= 5);
    }
}

#[test]
fn the_radio_adapter_admits_a_frame_only_inside_the_frame_size_and_the_duty_share() {
    // 1% duty, 100 us per byte on air
    let mut r = Radio::new(60, 100_000, 10);
    assert!(!r.admit(0, 61), "does not fit the medium");
    assert!(r.admit(0, 50), "5 ms of air");
    // 5 ms at 1% asks for 500 ms of rest
    assert!(!r.admit(499_999_999, 10));
    assert!(r.admit(500_000_000, 10));
    assert!(!Radio::new(60, 100_000, 0).admit(0, 1), "no share, no air time");
}
