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
mod timers_due_harness;

use core_harness::big_stack;
use ephyra::check_generator;
use timers_due_harness::{Case, in_support, run};

#[test]
fn no_timer_stays_due_after_it_ran() {
    big_stack(|| {
        let config = ephyra::Config::default().tests(60).name("no_timer_stays_due_after_it_ran");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run(&c)).assert_passed();
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
