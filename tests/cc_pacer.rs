//! Tests of the pacer's byte budget: each packet is charged its own size. Part of the `transport_cc` test target.
#![allow(clippy::unwrap_used, clippy::cast_possible_truncation)]

use proptest::prelude::*;
use vinc_transport::recovery::{BURST_PACKETS, MS, Pacer, burst_budget};

use crate::MSS;

fn gap(mtu: u64, srtt: u64, cwnd: u64) -> u64 {
    mtu * srtt * 4 / (5 * cwnd)
}

/// Packets a tenth of the path's datagram size go out a hundred to a burst, and the burst waits the ten gaps its
/// bytes are worth. The packet count paused after the tenth, charging each of them a whole datagram.
#[test]
fn small_packets_are_charged_their_own_bytes() {
    let (srtt, cwnd) = (100 * MS, 120_000u64);
    let size = (MSS / 10) as u32;
    let mut p = Pacer::new();
    for i in 0..99 {
        assert_eq!(p.next_release(1000), 1000, "packet {i} waits");
        p.on_sent(1000, size, MSS, srtt, cwnd, true);
    }
    assert_eq!(p.next_release(1000), 1000, "the burst ended before its budget");
    p.on_sent(1000, size, MSS, srtt, cwnd, true);
    assert_eq!(p.next_release(1000), 1000 + 10 * gap(MSS, srtt, cwnd));
}

/// A packet larger than the path's datagram size, as a relay carrier's inner packets are, is charged the datagrams it
/// is worth: four packets of three datagrams end the burst and wait twelve gaps.
#[test]
fn a_packet_larger_than_the_datagram_is_charged_the_datagrams_it_is_worth() {
    let (srtt, cwnd) = (100 * MS, 120_000u64);
    let mut p = Pacer::new();
    for i in 0..3 {
        p.on_sent(1000, 3 * MSS as u32, MSS, srtt, cwnd, true);
        assert_eq!(p.next_release(1000), 1000, "packet {i} ended the burst");
    }
    p.on_sent(1000, 3 * MSS as u32, MSS, srtt, cwnd, true);
    assert_eq!(p.next_release(1000), 1000 + 12 * gap(MSS, srtt, cwnd));
}

/// A part of a datagram is charged by its bytes at the same rate: thirteen packets of 1,200 bytes on a path of
/// 1,452 end the burst at 15,600 bytes and wait ten gaps of 1,452 and the remaining 1,080 bytes.
#[test]
fn the_remainder_of_a_burst_is_charged_by_its_bytes() {
    let (mtu, srtt, cwnd) = (1452u64, 80 * MS, 90_000u64);
    let mut p = Pacer::new();
    for _ in 0..12 {
        p.on_sent(1000, 1200, mtu, srtt, cwnd, true);
    }
    assert_eq!(p.next_release(1000), 1000);
    p.on_sent(1000, 1200, mtu, srtt, cwnd, true);
    let want = 10 * gap(mtu, srtt, cwnd) + 1080 * srtt * 4 / (5 * cwnd);
    assert_eq!(p.next_release(1000), 1000 + want);
}

/// A packet of no bytes is charged one, so a run of them still ends a burst.
#[test]
fn an_empty_packet_is_charged_one_byte() {
    let mut p = Pacer::new();
    for _ in 0..burst_budget(MSS) {
        p.on_sent(1000, 0, MSS, 100 * MS, 120_000, true);
    }
    assert!(p.next_release(1000) > 1000);
}

proptest! {
    /// Whatever the packets weigh, a sender its window limits waits after each burst the time its bytes take at
    /// 1.25 x cwnd per round trip, short of it by at most a nanosecond a datagram (the gap of each whole datagram is
    /// rounded down), and no burst carries more than its budget and one packet.
    #[test]
    fn each_burst_waits_the_time_its_bytes_take(
        sizes in proptest::collection::vec(1u32..=3 * MSS as u32, 1..400),
        mtu in prop_oneof![Just(1200u64), Just(1452), Just(65_535)],
        srtt in 1u64..=500 * MS,
        cwnd in 2400u64..=10_000_000,
    ) {
        let mut p = Pacer::new();
        let (mut now, mut spent) = (0u64, 0u64);
        for size in sizes {
            now = p.next_release(now);
            spent += u64::from(size);
            p.on_sent(now, size, mtu, srtt, cwnd, true);
            if spent >= burst_budget(mtu) {
                let exact = u128::from(spent) * u128::from(srtt) * 4 / (5 * u128::from(cwnd));
                let waited = u128::from(p.next_release(now) - now);
                prop_assert!(waited <= exact && exact - waited <= u128::from(spent / mtu) + 1,
                    "burst of {} bytes waited {} against {}", spent, waited, exact);
                prop_assert!(spent < burst_budget(mtu) + u64::from(size));
                spent = 0;
            } else {
                prop_assert_eq!(p.next_release(now), now, "a burst of {} bytes paused", spent);
            }
        }
    }
}

/// Full-size packets wait exactly the ten gaps the packet count gave them.
#[test]
fn full_size_packets_pause_as_the_packet_count_did() {
    let (srtt, cwnd) = (37 * MS + 13, 77_777u64);
    for mtu in [1200u64, 1452, 8952, 65_535] {
        let mut p = Pacer::new();
        for _ in 0..BURST_PACKETS {
            p.on_sent(5000, mtu as u32, mtu, srtt, cwnd, true);
        }
        assert_eq!(p.next_release(5000), 5000 + 10 * gap(mtu, srtt, cwnd), "mtu {mtu}");
    }
}
