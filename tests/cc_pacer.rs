//! Tests of the pacer's charge for a packet larger than the path's datagram size: as many tokens as the datagrams it
//! is worth, as the reference model's pacer charges it. Part of the `transport_cc` test target.
#![allow(clippy::unwrap_used, clippy::cast_possible_truncation)]

use proptest::prelude::*;
use vinc_transport::recovery::{BURST_PACKETS, MS, Pacer, packet_cost};

use crate::MSS;

fn gap(mtu: u64, srtt: u64, cwnd: u64) -> u64 {
    mtu * srtt * 4 / (5 * cwnd)
}

/// A packet costs one token up to the datagram size, and one more for every datagram it is worth past it.
#[test]
fn a_packet_costs_the_datagrams_it_is_worth() {
    assert_eq!(packet_cost(0, MSS), 1);
    assert_eq!(packet_cost(40, MSS), 1);
    assert_eq!(packet_cost(MSS as u32, MSS), 1);
    assert_eq!(packet_cost(MSS as u32 + 1, MSS), 2);
    assert_eq!(packet_cost(3 * MSS as u32, MSS), 3);
    assert_eq!(packet_cost(u32::MAX, 0), u64::from(u32::MAX));
    assert_eq!(packet_cost(u32::MAX, u64::MAX), u64::from(u32::MAX).div_ceil(65_535));
}

/// Four inner packets of three datagrams each, as a relay carrier forwards them, end the burst at the fourth and wait
/// the twelve gaps they are worth. Charged a token each, they left with no pause at all.
#[test]
fn relay_sized_packets_are_charged_the_datagrams_they_are_worth() {
    let (srtt, cwnd) = (100 * MS, 120_000u64);
    let mut p = Pacer::new();
    for i in 0..3 {
        p.on_sent(1000, 3 * MSS as u32, MSS, srtt, cwnd, true);
        assert_eq!(p.next_release(1000), 1000, "packet {i} ended the burst");
    }
    p.on_sent(1000, 3 * MSS as u32, MSS, srtt, cwnd, true);
    assert_eq!(p.next_release(1000), 1000 + 12 * gap(MSS, srtt, cwnd));
}

/// Nine full packets and one of three datagrams: the burst ends at the tenth packet and waits the twelve gaps it was
/// charged, not ten.
#[test]
fn a_large_packet_that_ends_a_burst_adds_its_datagrams_to_the_pause() {
    let (mtu, srtt, cwnd) = (1452u64, 80 * MS, 90_000u64);
    let mut p = Pacer::new();
    for _ in 0..9 {
        p.on_sent(1000, mtu as u32, mtu, srtt, cwnd, true);
    }
    assert_eq!(p.next_release(1000), 1000);
    p.on_sent(1000, 3 * mtu as u32, mtu, srtt, cwnd, true);
    assert_eq!(p.next_release(1000), 1000 + 12 * gap(mtu, srtt, cwnd));
}

/// Packets of a datagram or less are charged a token each, whatever they weigh: ten small packets pause ten gaps.
#[test]
fn packets_of_a_datagram_or_less_take_one_token_each() {
    let (srtt, cwnd) = (100 * MS, 120_000u64);
    for size in [1u32, 120, 1199, 1200] {
        let mut p = Pacer::new();
        for _ in 0..BURST_PACKETS {
            p.on_sent(1000, size, MSS, srtt, cwnd, true);
        }
        assert_eq!(p.next_release(1000), 1000 + 10 * gap(MSS, srtt, cwnd), "size {size}");
    }
}

proptest! {
    /// Whatever the packets weigh, a sender its window limits that waits for the release pauses after each burst one
    /// gap for every token the burst was charged, and only at the packet that takes the last token or more.
    #[test]
    fn each_burst_waits_a_gap_for_every_token_it_was_charged(
        sizes in proptest::collection::vec(1u32..=4 * MSS as u32, 1..200),
        mtu in prop_oneof![Just(1200u64), Just(1452), Just(65_535)],
        srtt in 1u64..=500 * MS,
        cwnd in 2400u64..=10_000_000,
    ) {
        let g = mtu * srtt * 4 / (5 * cwnd);
        let mut p = Pacer::new();
        let (mut now, mut charged) = (0u64, 0u64);
        for size in sizes {
            now = p.next_release(now);
            charged += packet_cost(size, mtu);
            p.on_sent(now, size, mtu, srtt, cwnd, true);
            if charged >= u64::from(BURST_PACKETS) {
                prop_assert_eq!(p.next_release(now), now + g * charged, "a burst charged {} tokens", charged);
                charged = 0;
            } else {
                prop_assert_eq!(p.next_release(now), now, "a burst charged {} tokens paused", charged);
            }
        }
    }
}
