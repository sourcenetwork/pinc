//! Timers that stay due, on the real `pinc-core` endpoint (and the transport connections inside it): after
//! `handle_timeout(t)` runs at `t = poll_timeout()` and the host drains `poll_transmit` with nothing else in between,
//! `poll_timeout()` is `None` or later than `t`.
//!
//! Where the rule comes from: `Connection::poll_timeout`, "The next time `handle_timeout` must run"
//! (crates/pinc-transport/src/conn/timer.rs:29); timer.rs:3, "a timer is reported only while it can still act (a stale
//! deadline would make a driver spin)"; `recovery::deadline_after`, "the timer that fires at `t` is next due after
//! `t`". The endpoint's `poll_timeout` is the earliest of its own timers and its sessions'.
//!
//! The two known cases are kept out by construction: the clock of the generated runs starts at 10 s and runs for at
//! most a few hours (so no probe deadline saturates at `u64::MAX`), and the key roll keeps the endpoint's default of
//! 2^21 packets (so no REKEY request waits to be written).

mod core_harness;
mod timers_due_conn;
mod timers_due_harness;

use core_harness::big_stack;
use ephyra::check_generator;
use timers_due_conn::CCase;
use timers_due_harness::{Case, in_support, run};

#[test]
fn no_timer_stays_due_after_it_ran() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(60)
            .name("no_timer_stays_due_after_it_ran");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run(&c)).assert_passed();
    });
}

/// The same with the known cause of `repro_transport2.rs` let through (a host whose peer sleeps), so the search finds
/// the others.
#[test]
fn no_timer_stays_due_after_it_ran_apart_from_the_known_cause() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(60)
            .name("no_timer_stays_due_after_it_ran_apart_from_the_known_cause");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| {
            timers_due_harness::run_with(&c, 10 * core_harness::SEC, true)
        })
        .assert_passed();
    });
}

#[test]
fn the_timer_case_generator_stays_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    check_generator(&cfg, ephyra::any::<Case>(), in_support).assert_passed();
}

/// A pair that connects and idles out, with the rule checked at every step.
#[test]
fn an_idle_pair_keeps_the_timer_rule() {
    big_stack(|| {
        run(&Case {
            seed: 1,
            split: true,
            room: true,
            delay_ms: 10,
            jitter_ms: 0,
            ops: Vec::new(),
        });
    });
}

/// The same rule on a bare pair of transport connections, with the clock starting either at 1000 s or up to 120 s
/// before `u64::MAX` (the timers that saturate there: timer.rs:46,64,66, life.rs, path_timers.rs:38). The known probe
/// deadline at `u64::MAX` (repro_transport.rs) ends a case without a verdict.
#[test]
fn no_connection_timer_stays_due_after_it_ran() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(80)
            .name("no_connection_timer_stays_due_after_it_ran");
        ephyra::check(&config, ephyra::any::<CCase>(), |c: CCase| timers_due_conn::run(&c)).assert_passed();
    });
}

/// The same with the class of the known causes let through (a timer blocked while the in-flight ring is full).
#[test]
fn no_connection_timer_stays_due_after_it_ran_apart_from_a_full_ring() {
    big_stack(|| {
        let config = ephyra::Config::default()
            .tests(80)
            .name("no_connection_timer_stays_due_after_it_ran_apart_from_a_full_ring");
        ephyra::check(&config, ephyra::any::<CCase>(), |c: CCase| {
            let _ = timers_due_conn::run_with(&c, true);
        })
        .assert_passed();
    });
}

#[test]
fn the_connection_case_generator_stays_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    check_generator(&cfg, ephyra::any::<CCase>(), timers_due_conn::in_support).assert_passed();
}

/// The drivers run what they claim: a quiet pair of connections connects and exchanges datagrams, and so does a pair
/// of endpoints.
#[test]
fn the_drivers_connect_a_quiet_pair() {
    big_stack(|| {
        let s = timers_due_conn::run_summary(&CCase {
            end: 0,
            delay_ms: 10,
            flight_split: false,
            ops: vec![timers_due_conn::COp::Write { from: 0, len: 100_000 }],
        });
        assert!(s.connected, "{s:?}");
        assert!(s.datagrams > 70, "{s:?}");
        assert_eq!(s.ops, 1, "{s:?}");
        let w = timers_due_harness::world(
            &Case {
                seed: 1,
                split: true,
                room: true,
                delay_ms: 10,
                jitter_ms: 0,
                ops: Vec::new(),
            },
            10 * core_harness::SEC,
        );
        assert!(w.net.hosts[w.a].opened.contains(&w.sa));
        assert!(w.sb.is_some());
    });
}
