//! Address discovery, home relay selection and the reachability classes.
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

use std::net::SocketAddr;

use connect_common::ed;
use vinc_connect::client::netcheck::{HOME_TRIES, HomeStep, Netcheck, Observed, classify, is_shared};
use vinc_connect::record::Reach;

const S: u64 = 1_000_000_000;

fn a(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

fn obs<'a>(local: &'a [SocketAddr], refl: &'a [SocketAddr], mapped: &'a [SocketAddr]) -> Observed<'a> {
    Observed {
        local,
        reflexive: refl,
        mapped,
        udp_heard: false,
        since_probe: 0,
        watchdog: 8 * S,
    }
}

#[test]
fn the_home_is_the_lowest_round_trip_and_a_tie_goes_to_the_relay_that_answered_first() {
    let mut n = Netcheck::<3>::new();
    for (i, nonce) in [[1u8; 8], [2; 8], [3; 8]].into_iter().enumerate() {
        n.probe_sent(0, i, nonce, true);
    }
    assert_eq!(n.home(), None);
    assert_eq!(n.answered(50, 0, [1; 8], a("1.2.3.4:5")), Some(50));
    assert_eq!(n.home(), Some(0));
    assert_eq!(n.answered(30, 1, [2; 8], a("1.2.3.4:5")), Some(30));
    assert_eq!(n.home(), Some(1));
    assert_eq!(n.answered(30, 2, [3; 8], a("1.2.3.4:5")), Some(30));
    assert_eq!(
        n.home(),
        Some(1),
        "an equal round trip does not move the home from the relay that answered first"
    );
    assert_eq!(n.best_rtt(), 30);
}

#[test]
fn an_address_that_several_relays_report_is_listed_once() {
    let mut n = Netcheck::<3>::default();
    n.probe_sent(0, 0, [1; 8], true);
    n.probe_sent(0, 1, [2; 8], true);
    n.probe_sent(0, 2, [3; 8], true);
    assert!(n.answered(50, 0, [1; 8], a("1.2.3.4:5")).is_some());
    assert!(n.answered(30, 1, [2; 8], a("1.2.3.4:5")).is_some());
    assert!(n.answered(40, 2, [3; 8], a("9.9.9.9:7")).is_some());
    let mut out = [a("0.0.0.0:0"); 8];
    let got = n.reflexive_into(&mut out);
    assert_eq!(
        &out[..got],
        &[a("1.2.3.4:5"), a("9.9.9.9:7")],
        "one place per address, in relay order"
    );
    // a short buffer takes the distinct addresses that fit
    let mut one = [a("0.0.0.0:0"); 1];
    assert_eq!(n.reflexive_into(&mut one), 1);
    assert_eq!(one[0], a("1.2.3.4:5"));
}

#[test]
fn a_home_taken_by_the_fallback_moves_to_the_first_relay_that_answers() {
    let mut n = Netcheck::<3>::new();
    for _ in 0..HOME_TRIES {
        n.home_missing(Some(0));
    }
    assert_eq!(n.home(), Some(0), "the lowest id, never measured");
    n.probe_sent(0, 2, [3; 8], true);
    assert_eq!(n.answered(900, 2, [3; 8], a("1.2.3.4:5")), Some(900));
    assert_eq!(n.home(), Some(2), "a relay measured at 900 beats one never measured");
}

#[test]
fn the_home_follows_the_last_measurements_and_an_equal_round_trip_goes_to_the_relay_that_answered_first() {
    let mut n = Netcheck::<2>::new();
    let answer = |n: &mut Netcheck<2>, now: u64, sent: u64, relay: usize, nonce: u8| {
        n.probe_sent(sent, relay, [nonce; 8], true);
        n.answered(now, relay, [nonce; 8], a("1.2.3.4:5"));
    };
    answer(&mut n, 50, 0, 0, 1);
    answer(&mut n, 30, 0, 1, 2);
    assert_eq!(n.home(), Some(1));
    // Relay 1 now measures 50 as well: equal to relay 0, which answered first, so the home goes back to it.
    answer(&mut n, 1_050, 1_000, 1, 3);
    assert_eq!(n.rtt(1), Some(50));
    assert_eq!(n.home(), Some(0));
    // Answers kept across a link change still count as candidates.
    n.restart();
    answer(&mut n, 2_020, 2_000, 1, 4);
    assert_eq!(n.home(), Some(1), "relay 1 measures 20, relay 0 still stands at 50");
}

#[test]
fn a_wrong_nonce_or_a_second_answer_is_ignored() {
    let mut n = Netcheck::<2>::new();
    n.probe_sent(0, 0, [9; 8], true);
    assert_eq!(n.answered(10, 0, [8; 8], a("1.2.3.4:5")), None);
    assert_eq!(
        n.answered(10, 1, [9; 8], a("1.2.3.4:5")),
        None,
        "the nonce belongs to relay 0"
    );
    assert_eq!(n.answered(10, 0, [9; 8], a("1.2.3.4:5")), Some(10));
    assert_eq!(n.answered(11, 0, [9; 8], a("1.2.3.4:5")), None, "answered at most once");
    assert_eq!(n.reflexive_of(0), Some(a("1.2.3.4:5")));
}

#[test]
fn a_homeless_node_takes_the_first_relay_after_three_rounds() {
    let mut n = Netcheck::<2>::new();
    for _ in 0..HOME_TRIES - 1 {
        assert_eq!(n.home_missing(Some(1)), HomeStep::Again);
    }
    assert_eq!(n.home_missing(Some(1)), HomeStep::Fallback(1));
    assert_eq!(n.home(), Some(1));
    assert_eq!(n.home_missing(Some(1)), HomeStep::Done);
}

#[test]
fn the_rounds_without_a_home_are_not_forgotten_when_the_link_changes() {
    let mut n = Netcheck::<2>::new();
    for _ in 0..HOME_TRIES - 1 {
        assert_eq!(n.home_missing(Some(1)), HomeStep::Again);
    }
    n.restart();
    assert_eq!(
        n.home_missing(Some(1)),
        HomeStep::Fallback(1),
        "the third round, however the link moved"
    );
}

#[test]
fn classes_from_observation() {
    let local = [a("192.168.1.5:4433")];
    // public: the reflexive address is the local one (IPv4 and IPv6)
    assert_eq!(classify(&obs(&local, &[local[0]], &[])), Some(Reach::Public));
    let l6 = [a("[2001:db8::5]:4433")];
    assert_eq!(classify(&obs(&l6, &[l6[0]], &[])), Some(Reach::Public));
    // port mapped
    let ext = a("203.0.113.9:6000");
    assert_eq!(classify(&obs(&local, &[ext], &[ext])), Some(Reach::PortMapped));
    // behind NAT: one answer, or equal answers from several relays
    assert_eq!(classify(&obs(&local, &[ext], &[])), Some(Reach::Nat));
    assert_eq!(classify(&obs(&local, &[ext, ext], &[])), Some(Reach::Nat));
    // symmetric: two relays saw different ports
    assert_eq!(
        classify(&obs(&local, &[ext, a("203.0.113.9:6001")], &[])),
        Some(Reach::Cgnat)
    );
    // shared range
    assert_eq!(classify(&obs(&local, &[a("100.64.0.1:1")], &[])), Some(Reach::Cgnat));
    assert_eq!(
        classify(&obs(&local, &[a("100.127.255.255:1")], &[])),
        Some(Reach::Cgnat)
    );
    assert_eq!(classify(&obs(&local, &[a("100.128.0.0:1")], &[])), Some(Reach::Nat));
    assert_eq!(classify(&obs(&local, &[a("100.63.255.255:1")], &[])), Some(Reach::Nat));
    assert!(is_shared(&"100.64.0.0".parse().unwrap()));
    assert!(!is_shared(&"2001:db8::1".parse().unwrap()));
}

#[test]
fn udp_blocked_needs_silence_for_the_whole_watchdog_and_no_udp_ever() {
    let local = [a("192.168.1.5:4433")];
    let mut o = obs(&local, &[], &[]);
    assert_eq!(classify(&o), None, "nothing observed yet");
    o.since_probe = 8 * S - 1;
    assert_eq!(classify(&o), None);
    o.since_probe = 8 * S;
    assert_eq!(classify(&o), Some(Reach::UdpBlocked));
    o.udp_heard = true;
    assert_eq!(classify(&o), None, "UDP was heard: not blocked, just unanswered so far");
}

#[test]
fn restart_forgets_answers_but_keeps_the_home() {
    let mut n = Netcheck::<1>::new();
    n.probe_sent(0, 0, [1; 8], true);
    n.answered(5, 0, [1; 8], a("1.2.3.4:5"));
    n.restart();
    assert_eq!(n.reflexive_of(0), None);
    assert_eq!(n.home(), Some(0));
    assert_eq!(n.first_probe(), None);
    let _ = ed(1);
}

#[test]
fn a_relay_that_fails_three_times_in_a_row_loses_the_home_to_the_next_healthy_one() {
    let mut n = Netcheck::<3>::new();
    for i in 0..3 {
        n.probe_sent(0, i, [i as u8; 8], true);
        assert!(
            n.answered(
                10 * (i as u64 + 1),
                i,
                [i as u8; 8],
                format!("198.51.100.{}:4000", i + 1).parse().unwrap()
            )
            .is_some()
        );
    }
    assert_eq!(n.home(), Some(0), "the lowest round trip");
    // A probe sent while the last one is unanswered is a failure; the first of a round is only sent.
    for round in 0..3u8 {
        n.probe_sent(1_000, 0, [50 + round; 8], true);
    }
    assert!(!n.unhealthy(0), "two failures are not yet three");
    assert_eq!(n.failover(|_| true, |_| false), None);
    n.probe_sent(1_000, 0, [60; 8], true);
    assert!(n.unhealthy(0));
    assert_eq!(
        n.failover(|_| true, |_| false),
        Some(1),
        "the relay that answered, with the lowest round trip"
    );
    assert_eq!(n.home(), Some(1));
    // A carrier that opens makes a relay healthy again; an answer too.
    n.healthy(0);
    assert!(!n.unhealthy(0));
    // Carrier dial failures count the same, and a node that never heard UDP expects no answers to its probes.
    let mut d = Netcheck::<2>::new();
    d.probe_sent(0, 0, [1; 8], false);
    d.probe_sent(1, 0, [2; 8], false);
    d.probe_sent(2, 0, [3; 8], false);
    assert!(!d.unhealthy(0), "unanswered probes of a UDP-dark node are not failures");
    d.failed(0);
    d.failed(0);
    d.failed(0);
    assert!(d.unhealthy(0));
    assert_eq!(d.failover(|i| i < 2, |_| true), None, "no home yet, nothing to move");
    d.home_missing(Some(0));
    d.home_missing(Some(0));
    d.home_missing(Some(0));
    assert_eq!(d.home(), Some(0));
    assert_eq!(
        d.failover(|i| i < 2, |_| false),
        None,
        "a relay that merely has not failed is no target: the home stays"
    );
    for _ in 0..9 {
        d.failed(0);
        d.failed(1);
        assert_eq!(d.failover(|i| i < 2, |_| false), None);
        assert_eq!(d.home(), Some(0), "nothing reachable: the home does not cycle");
    }
    let mut c = Netcheck::<2>::new();
    c.home_missing(Some(0));
    c.home_missing(Some(0));
    c.home_missing(Some(0));
    for _ in 0..3 {
        c.failed(0);
    }
    assert_eq!(
        c.failover(|i| i < 2, |i| i == 1),
        Some(1),
        "with no round trip known the next relay by position whose carrier is open"
    );
    // The only relay has nowhere to go.
    let mut one = Netcheck::<1>::new();
    one.home_missing(Some(0));
    one.home_missing(Some(0));
    one.home_missing(Some(0));
    for _ in 0..3 {
        one.failed(0);
    }
    assert_eq!(one.failover(|_| true, |_| true), None);
}

/// Probe every relay of `n` once and answer them with the round trips of `rtts`.
fn answer_all<const R: usize>(n: &mut Netcheck<R>, at: u64, rtts: [u64; R]) {
    for (i, rtt) in rtts.into_iter().enumerate() {
        let nonce = [(at as u8).wrapping_add(i as u8); 8];
        n.probe_sent(at, i, nonce, true);
        assert!(n.answered(at + rtt, i, nonce, a("198.51.100.1:4000")).is_some());
    }
}

#[test]
fn a_pinned_relay_is_home_over_a_lower_round_trip_once_it_answers() {
    let mut n = Netcheck::<3>::new();
    n.pin(2);
    assert_eq!(n.pinned(), Some(2));
    n.probe_sent(0, 0, [1; 8], true);
    assert!(n.answered(10, 0, [1; 8], a("1.2.3.4:5")).is_some());
    assert_eq!(
        n.home(),
        Some(0),
        "until the pinned relay answers, the lowest round trip is home"
    );
    n.probe_sent(0, 2, [3; 8], true);
    assert!(n.answered(90, 2, [3; 8], a("1.2.3.4:5")).is_some());
    assert_eq!(
        n.home(),
        Some(2),
        "the pinned relay answered: it is home with a higher round trip"
    );
    n.probe_sent(100, 1, [2; 8], true);
    assert!(n.answered(101, 1, [2; 8], a("1.2.3.4:5")).is_some());
    assert_eq!(
        n.home(),
        Some(2),
        "a lower round trip elsewhere does not move a pinned home"
    );
    // a position past the table is no pin
    let mut m = Netcheck::<2>::new();
    m.pin(2);
    assert_eq!(m.pinned(), None);
}

#[test]
fn an_unhealthy_pinned_home_fails_over_and_its_next_answer_brings_the_home_back() {
    let mut n = Netcheck::<3>::new();
    n.pin(1);
    answer_all(&mut n, 0, [10, 50, 30]);
    assert_eq!(n.home(), Some(1));
    for k in 0..4u8 {
        n.probe_sent(1_000, 1, [200 + k; 8], true);
    }
    assert!(n.unhealthy(1));
    assert_eq!(
        n.failover(|_| true, |_| false),
        Some(0),
        "the lowest round trip that works"
    );
    // answers from the others while the pin is still out keep the round-trip rule
    n.probe_sent(2_000, 2, [7; 8], true);
    assert!(n.answered(2_005, 2, [7; 8], a("1.2.3.4:5")).is_some());
    assert_eq!(n.home(), Some(2));
    n.probe_sent(3_000, 1, [9; 8], true);
    assert!(n.answered(3_080, 1, [9; 8], a("1.2.3.4:5")).is_some());
    assert!(!n.unhealthy(1));
    assert_eq!(n.home(), Some(1), "the pinned relay answered again: it is home again");
}

#[test]
fn a_pinned_home_holds_through_round_trips_that_move_an_unpinned_one() {
    let mut pinned = Netcheck::<3>::new();
    let mut plain = Netcheck::<3>::new();
    pinned.pin(0);
    for (at, rtts) in [(0, [40, 20, 30]), (1_000, [40, 10, 30]), (2_000, [5, 10, 30])] {
        answer_all(&mut plain, at, rtts);
        answer_all(&mut pinned, at, rtts);
        assert_eq!(pinned.home(), Some(0));
    }
    assert_eq!(
        plain.home(),
        Some(0),
        "the plain rule took relay 0 only for its strictly lower round trip"
    );
}
