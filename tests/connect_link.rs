//! The client carrier state machine at its boundary numbers: retry, watchdog, keepalive, check, lease, stale send
//! and the restart defer.
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

use pinc_connect::client::link::{Act, Ctx, Link, Pulse, Shared, State, check_wait, dial_wait, lease_keep, rule};

const S: u64 = 1_000_000_000;

fn ctx() -> Ctx {
    Ctx {
        home: true,
        rtt: 0,
        udp_any: false,
        rides: false,
        queued: false,
    }
}

fn open_link(now: u64) -> (Link, Shared) {
    let mut l = Link::new();
    let mut sh = Shared::default();
    assert_eq!(l.want_dial(now, &mut sh, &ctx()), Some(Act::Dial));
    l.opened(now);
    (l, sh)
}

#[test]
fn dial_retries_at_one_second_then_two_and_stays() {
    let mut l = Link::new();
    let mut sh = Shared::default();
    let c = ctx();
    let mut now = 0;
    assert_eq!(l.want_dial(now, &mut sh, &c), Some(Act::Dial));
    let mut waits = vec![];
    for _ in 0..4 {
        l.closed(now);
        assert_eq!(l.state(), State::Down);
        let at = l.next_deadline(now, &sh, &c).unwrap();
        waits.push(at - now);
        assert_eq!(l.tick(at - 1, &mut sh, &c), None, "not before the wait");
        now = at;
        assert_eq!(l.tick(now, &mut sh, &c), Some(Act::Dial));
    }
    assert_eq!(waits, vec![S, 2 * S, 2 * S, 2 * S]);
    l.opened(now);
    l.closed(now);
    assert_eq!(
        l.next_deadline(now, &sh, &c),
        Some(now + S),
        "a stream that opened resets the wait to 1 s"
    );
}

#[test]
fn watchdog_is_max_8s_or_8_rtt_capped_at_30s() {
    assert_eq!(dial_wait(0), 8 * S);
    assert_eq!(dial_wait(S), 8 * S);
    assert_eq!(dial_wait(S + 1), 8 * S + 8);
    assert_eq!(dial_wait(2 * S), 16 * S);
    assert_eq!(dial_wait(3750 * 1_000_000), 30 * S);
    assert_eq!(dial_wait(10 * S), 30 * S);
    let mut l = Link::new();
    let mut sh = Shared::default();
    let c = ctx();
    l.want_dial(100, &mut sh, &c);
    // The watchdog fires strictly after the wait.
    assert_eq!(l.tick(100 + 8 * S, &mut sh, &c), None);
    assert_eq!(l.next_deadline(100, &sh, &c), Some(100 + 8 * S + 1));
    assert_eq!(l.tick(100 + 8 * S + 1, &mut sh, &c), Some(Act::Close));
    assert_eq!(l.state(), State::Down);
    // and dials again at once
    assert_eq!(l.tick(100 + 8 * S + 1, &mut sh, &c), Some(Act::Dial));
}

#[test]
fn keepalive_silence_30s_on_a_phone_65s_otherwise() {
    for (phone, silence) in [(true, 30 * S), (false, 65 * S)] {
        let (mut l, mut sh) = open_link(0);
        sh.phone = phone;
        let c = ctx();
        assert_eq!(l.tick(silence - 1, &mut sh, &c), None, "phone={phone}");
        assert_eq!(l.next_deadline(0, &sh, &c), Some(silence));
        assert_eq!(l.tick(silence, &mut sh, &c), Some(Act::Check));
    }
}

#[test]
fn a_recent_silent_death_keeps_the_short_check_for_ten_minutes() {
    let (mut l, mut sh) = open_link(0);
    let c = ctx();
    sh.keep_fail = Some(0);
    let _ = &mut l;
    // 600 s - 1 after the death the home check is still 30 s
    let mut l2 = Link::new();
    l2.want_dial(0, &mut sh, &c);
    l2.opened(600 * S - 1 - 30 * S);
    assert_eq!(l2.next_deadline(0, &sh, &c), Some(600 * S - 1));
    // at 600 s the memory has expired: 65 s
    let mut l3 = Link::new();
    l3.want_dial(0, &mut sh, &c);
    l3.opened(600 * S);
    assert_eq!(l3.next_deadline(600 * S, &sh, &c), Some(665 * S));
}

#[test]
fn only_the_home_or_a_riding_carrier_is_checked() {
    let (mut l, mut sh) = open_link(0);
    let mut c = ctx();
    c.home = false;
    assert_eq!(l.tick(100 * S, &mut sh, &c), None);
    assert_eq!(l.next_deadline(0, &sh, &c), None);
    c.rides = true;
    assert_eq!(l.tick(65 * S, &mut sh, &c), Some(Act::Check));
}

#[test]
fn an_unanswered_ping_resets_after_max_3s_3_rtt() {
    assert_eq!(check_wait(0), 3 * S);
    assert_eq!(check_wait(S), 3 * S);
    assert_eq!(check_wait(S + 1), 3 * S + 3);
    let (mut l, mut sh) = open_link(0);
    let mut c = ctx();
    c.rtt = 2 * S;
    assert_eq!(l.check(65 * S, &c, false), Some(Act::Ping));
    assert_eq!(l.next_deadline(65 * S, &sh, &c), Some(71 * S));
    assert_eq!(l.tick(71 * S - 1, &mut sh, &c), None);
    assert_eq!(l.tick(71 * S, &mut sh, &c), Some(Act::Close));
    assert_eq!(sh.keep_fail, Some(71 * S));
    assert_eq!(l.state(), State::Down);
    // any rx answers the check
    let (mut l, mut sh) = open_link(0);
    l.check(65 * S, &ctx(), false);
    l.heard(66 * S);
    assert_eq!(l.tick(100 * S, &mut sh, &ctx()), None);
}

#[test]
fn a_ridden_check_falls_back_to_a_real_ping() {
    let (mut l, mut sh) = open_link(0);
    let c = ctx();
    assert_eq!(
        l.check(65 * S, &c, true),
        None,
        "no PING is written when a session packet carries the check"
    );
    assert_eq!(
        l.tick(68 * S, &mut sh, &c),
        Some(Act::Ping),
        "the ridden check expired: a real PING follows"
    );
    assert_eq!(l.state(), State::Open, "a ridden check does not reset");
    assert_eq!(sh.keep_fail, None);
    assert_eq!(l.tick(71 * S, &mut sh, &c), Some(Act::Close));
}

#[test]
fn lease_keepalive_gap_formula() {
    let f = |h: u64| lease_keep(h * S) / S;
    assert_eq!(f(15), 15);
    assert_eq!(f(16), 15);
    assert_eq!(f(20), 17); // (15+20)/2 = 17.5 vs 17.5 = 7/8*20: equal
    assert_eq!(lease_keep(20 * S), 17_500_000_000);
    assert_eq!(f(30), 22);
    assert_eq!(f(60), 37);
    assert_eq!(f(120), 67);
    for h in 15..400u64 {
        let g = lease_keep(h * S);
        assert!(g >= rule::LEASE_FLOOR);
        assert!(g <= h * S, "the gap never exceeds the shortest dead gap: h={h}");
    }
}

#[test]
fn lease_hi_only_falls_and_only_from_a_non_ridden_gap_of_15s_or_more() {
    let mut sh = Shared::default();
    let c = ctx();
    // a death after an idle gap of 40 s sets the lease
    let mut l = Link::new();
    l.want_dial(0, &mut sh, &c);
    l.opened(0);
    sh.lease_hi = u64::MAX / 2;
    assert_eq!(l.check(40 * S, &c, false), Some(Act::Ping));
    assert_eq!(l.tick(43 * S, &mut sh, &c), Some(Act::Close));
    assert_eq!(sh.lease_hi, 40 * S);
    // a shorter gap lowers it, a longer one does not raise it
    for (gap, want) in [(30u64, 30u64), (50, 30), (14, 30)] {
        let mut l = Link::new();
        l.want_dial(0, &mut sh, &c);
        l.opened(0);
        l.check(gap * S, &c, false);
        l.tick(gap * S + 3 * S, &mut sh, &c);
        assert_eq!(sh.lease_hi, want * S, "gap {gap}");
    }
    // a ridden check never teaches the lease; the real ping that follows it measures its own gap (23 s here)
    let mut l = Link::new();
    l.want_dial(0, &mut sh, &c);
    l.opened(0);
    l.check(20 * S, &c, true);
    l.tick(22 * S, &mut sh, &c);
    assert_eq!(sh.lease_hi, 30 * S, "an unexpired ridden check changes nothing");
    assert_eq!(l.tick(23 * S, &mut sh, &c), Some(Act::Ping));
    assert_eq!(sh.lease_hi, 30 * S, "the ridden check itself taught nothing");
    l.tick(26 * S, &mut sh, &c);
    assert_eq!(sh.lease_hi, 23 * S);
}

#[test]
fn lease_does_not_apply_once_udp_was_heard() {
    let mut sh = Shared {
        lease_hi: 20 * S,
        ..Shared::default()
    };
    let mut l = Link::new();
    let mut c = ctx();
    l.want_dial(0, &mut sh, &c);
    l.opened(0);
    c.udp_any = true;
    assert_eq!(l.next_deadline(0, &sh, &c), Some(65 * S));
    assert_eq!(l.before_send(100 * S, &sh, &c), None);
    c.udp_any = false;
    // with the lease the keepalive gap is 17.5 s
    assert_eq!(l.next_deadline(0, &sh, &c), Some(17_500_000_000));
    assert_eq!(l.tick(17_500_000_000 - 1, &mut sh, &c), None);
    assert_eq!(l.tick(17_500_000_000, &mut sh, &c), Some(Act::Ping));
}

#[test]
fn stale_send_resets_a_carrier_idle_both_ways_for_the_lease() {
    let sh = Shared {
        lease_hi: 30 * S,
        ..Shared::default()
    };
    let c = ctx();
    let mut l = Link::new();
    let mut shm = sh;
    l.want_dial(0, &mut shm, &c);
    l.opened(0);
    assert_eq!(l.before_send(30 * S - 1, &sh, &c), None);
    // written at 20 s: idle one way only
    l.wrote(20 * S);
    assert_eq!(l.before_send(30 * S, &sh, &c), None);
    // heard at 25 s too
    l.heard(25 * S);
    assert_eq!(l.before_send(50 * S - 1, &sh, &c), None);
    assert_eq!(l.before_send(55 * S, &sh, &c), Some(Act::Close));
    assert_eq!(l.state(), State::Down);
    assert_eq!(l.tick(55 * S, &mut shm, &c), Some(Act::Dial), "it redials at once");
}

#[test]
fn restart_defers_the_home_dial_600ms_unless_a_frame_waits() {
    let mut sh = Shared {
        restarted: true,
        ..Shared::default()
    };
    let mut l = Link::new();
    let c = ctx();
    let t0 = 5 * S;
    assert_eq!(l.want_dial(t0, &mut sh, &c), None);
    assert_eq!(l.next_deadline(t0, &sh, &c), Some(t0 + rule::DEFER));
    assert_eq!(l.tick(t0 + rule::DEFER - 1, &mut sh, &c), None);
    assert_eq!(l.tick(t0 + rule::DEFER, &mut sh, &c), Some(Act::Dial));
    // a frame to send cancels the wait
    let mut sh = Shared {
        restarted: true,
        ..Shared::default()
    };
    let mut l = Link::new();
    assert_eq!(l.want_dial(t0, &mut sh, &c), None);
    let queued = Ctx { queued: true, ..c };
    assert_eq!(l.want_dial(t0 + 100, &mut sh, &queued), Some(Act::Dial));
    // a relay that is not home is not deferred when a frame waits, and not dialed otherwise
    let mut sh = Shared {
        restarted: true,
        ..Shared::default()
    };
    let mut l = Link::new();
    let other = Ctx { home: false, ..c };
    assert_eq!(l.want_dial(t0, &mut sh, &other), None);
    assert_eq!(l.next_deadline(t0, &sh, &other), None);
}

#[test]
fn pulse_starts_a_check_on_an_open_carrier_and_reports_a_closed_one() {
    let (mut l, _sh) = open_link(0);
    assert_eq!(l.pulse(1, &ctx()), Pulse::Ping);
    assert_eq!(l.pulse(2, &ctx()), Pulse::Waiting, "a check is already outstanding");
    l.heard(3);
    assert_eq!(l.pulse(4, &ctx()), Pulse::Ping, "the answer cleared it");
    assert_eq!(Link::new().pulse(0, &ctx()), Pulse::Closed);
}

#[test]
fn the_first_silent_death_after_an_idle_gap_sets_the_lease_from_unknown() {
    let (mut l, mut sh) = open_link(0);
    assert_eq!(sh.lease_hi, 0);
    assert_eq!(l.check(40 * S, &ctx(), false), Some(Act::Ping));
    assert_eq!(l.tick(43 * S, &mut sh, &ctx()), Some(Act::Close));
    assert_eq!(sh.lease_hi, 40 * S);
    // a gap under the floor teaches nothing
    let (mut l, mut sh) = open_link(0);
    l.check(14 * S, &ctx(), false);
    l.tick(17 * S, &mut sh, &ctx());
    assert_eq!(sh.lease_hi, 0);
}

#[test]
fn keep_learn_halves_the_silence_a_dead_carrier_endured_down_to_the_floor() {
    let learn = |sh: &mut Shared, silent: u64| {
        let mut l = Link::new();
        let mut c = ctx();
        c.udp_any = true;
        l.want_dial(0, sh, &c);
        l.opened(0);
        assert_eq!(l.tick(silent, sh, &c), Some(Act::Check));
        assert_eq!(l.check(silent, &c, false), Some(Act::Ping));
        assert_eq!(l.tick(silent + 3 * S, sh, &c), Some(Act::Close));
    };
    // off: nothing is learned
    let mut sh = Shared::default();
    learn(&mut sh, 65 * S);
    assert_eq!(sh.keep_iv, 0);
    // on: half of the silence, then half of the smaller of the two
    let mut sh = Shared {
        keep_learn: true,
        ..Shared::default()
    };
    learn(&mut sh, 65 * S);
    assert_eq!(sh.keep_iv, u64::midpoint(65 * S, 3 * S));
    let first = sh.keep_iv;
    learn(&mut sh, 30 * S);
    assert_eq!(sh.keep_iv, (33 * S).min(first) / 2);
    // never below 15 s
    for _ in 0..4 {
        learn(&mut sh, 20 * S);
    }
    assert_eq!(sh.keep_iv, 15 * S);
    // the learned interval caps every keepalive wait, home or not
    let (l, _) = open_link(0);
    let c = ctx();
    assert_eq!(l.next_deadline(0, &sh, &c), Some(15 * S));
    let other = Ctx {
        home: false,
        rides: true,
        ..c
    };
    assert_eq!(l.next_deadline(0, &sh, &other), Some(15 * S));
}

/// A clock reading older than the last stamp of the carrier (the host's clock is only read, never trusted to rise)
/// is no idle gap: the send does not reset the carrier. (The gap was once computed with a plain subtraction, which
/// underflowed.)
#[test]
fn a_send_at_an_earlier_instant_than_the_last_stamp_resets_nothing() {
    let sh = Shared {
        lease_hi: 20 * S,
        ..Shared::default()
    };
    let c = ctx();
    let mut shm = sh;
    let mut l = Link::new();
    l.want_dial(100 * S, &mut shm, &c);
    l.opened(100 * S);
    l.wrote(120 * S);
    l.heard(130 * S);
    for now in [0, 1, 50 * S, 100 * S, 119 * S, 125 * S, 129 * S] {
        assert_eq!(l.before_send(now, &sh, &c), None, "now = {now}");
    }
    assert_eq!(l.state(), State::Open);
    // and the gap still counts from the later stamp
    assert_eq!(l.before_send(150 * S - 1, &sh, &c), None);
    assert_eq!(l.before_send(150 * S, &sh, &c), Some(Act::Close));
}

/// A frame queued during the restart defer cancels the wait, so the carrier can dial at once: the deadline the link
/// reports is not later than the instant `tick` acts. (It reported the end of the defer while `tick` dialed at once.)
#[test]
fn a_queued_frame_during_the_restart_defer_makes_the_deadline_now() {
    let mut sh = Shared {
        restarted: true,
        ..Shared::default()
    };
    let mut c = ctx();
    let mut l = Link::new();
    assert_eq!(l.tick(0, &mut sh, &c), None, "the home carrier waits out the defer");
    assert_eq!(l.next_deadline(0, &sh, &c), Some(rule::DEFER));
    c.queued = true;
    let d = l.next_deadline(10 * 1_000_000, &sh, &c).unwrap();
    assert!(
        d <= 10 * 1_000_000,
        "a frame is waiting: the carrier dials now, not at {d}"
    );
    assert_eq!(l.tick(d.max(10 * 1_000_000), &mut sh, &c), Some(Act::Dial));
}
