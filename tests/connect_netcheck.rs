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
fn the_home_is_the_lowest_round_trip_and_changes_only_for_a_strictly_lower_one() {
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
    assert_eq!(n.home(), Some(1), "an equal round trip does not move the home");
    assert_eq!(n.best_rtt(), 30);
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
