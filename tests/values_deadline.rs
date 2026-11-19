//! What ends a fetch whose provider stops answering: its deadline, or the provider answering again; the fetch has no
//! timer of its own for a first answer. A provider whose session closed is dialled again, with the stall rule's
//! backoff, for as long as the fetch runs. A provider that is connected and sends nothing is waited for with no timer
//! at all, so a fetch that gives no deadline waits for as long as that provider's session stays up. A second provider
//! that holds the value ends the fetch whatever the first does.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::doc_markdown,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use values_support::*;
use pinc_values::trace::{FailReason, Trace};

/// How many times the stall rule dialled a provider again.
fn redials(sim: &Sim) -> usize {
    sim.rec
        .traces
        .iter()
        .filter(|(_, t)| matches!(t, Trace::StallRedial { .. }))
        .count()
}

/// Ten minutes: long against every timer of the fetch (the stall wait is at most 40 s).
const LONG: u64 = 600 * SEC;

#[test]
fn a_fetch_whose_only_provider_is_gone_dials_it_again_and_ends_at_its_deadline() {
    let store = PStore::random(71, 4 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 1000)], ClientStore::new());
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(20 * SEC));
    sim.run_until(SEC, |_| false);
    let had = sim.store.covered();
    assert!(had > 0, "nothing arrived in the first second");
    sim.cut(0);
    assert!(
        !sim.run_until(20 * SEC, |s| s.fetch.is_done()),
        "the fetch ended before its deadline"
    );
    assert!(redials(&sim) > 0, "the provider that went away was not dialled again");
    assert!(
        sim.run_until(21 * SEC, |s| s.fetch.is_done()),
        "the deadline did not end the fetch"
    );
    assert!(
        sim.now <= 20 * SEC + 1,
        "the fetch ended at {} ns, past its deadline",
        sim.now
    );
    assert_eq!(sim.rec.failed(), Some(FailReason::Deadline));
    assert_eq!(sim.store.covered(), had, "what was verified before the cut is kept");
}

#[test]
fn with_no_deadline_a_fetch_whose_only_provider_is_gone_keeps_dialling_and_ends_when_it_is_back() {
    let store = PStore::random(72, 4 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 1000)], ClientStore::new());
    sim.start();
    sim.run_until(SEC, |_| false);
    sim.cut(0);
    assert!(
        !sim.run_until(LONG, |s| s.fetch.is_done()),
        "the fetch ended on its own"
    );
    assert_eq!(sim.rec.failed(), None, "a fetch with no deadline failed");
    assert!(
        sim.fetch.poll_timeout().is_some(),
        "no timer is armed to dial the provider again"
    );
    // the stall wait starts at 4 s and doubles: never more than one dial every 4 s
    let n = redials(&sim);
    assert!((1..=150).contains(&n), "{n} dials in ten minutes");
    sim.revive(0);
    sim.run(700);
    assert!(
        sim.rec.complete(),
        "the fetch did not finish once its provider was back"
    );
}

#[test]
fn a_fetch_whose_only_provider_is_connected_and_silent_ends_at_its_deadline() {
    let store = PStore::random(73, 4 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 1000).stall_after(0)], ClientStore::new());
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(20 * SEC));
    assert!(
        !sim.run_until(20 * SEC, |s| s.fetch.is_done()),
        "the fetch ended before its deadline"
    );
    assert!(
        sim.run_until(21 * SEC, |s| s.fetch.is_done()),
        "the deadline did not end the fetch"
    );
    assert!(
        sim.now <= 20 * SEC + 1,
        "the fetch ended at {} ns, past its deadline",
        sim.now
    );
    assert_eq!(sim.rec.failed(), Some(FailReason::Deadline));
    assert_eq!(redials(&sim), 0, "the stall rule starts at the first verified granule");
}

/// The case the application's deadline is for: nothing of the fetch runs, and nothing ends it.
#[test]
fn with_no_deadline_a_fetch_whose_only_provider_is_connected_and_silent_waits_with_no_timer() {
    let store = PStore::random(74, 4 << 20);
    let mut sim = Sim::new(vec![ProvCfg::new(store, 1000).stall_after(0)], ClientStore::new());
    sim.start();
    assert!(
        !sim.run_until(LONG, |s| s.fetch.is_done()),
        "the fetch ended on its own"
    );
    assert_eq!(sim.rec.failed(), None, "a fetch with no deadline failed");
    assert_eq!(sim.store.covered(), 0);
    assert_eq!(
        redials(&sim),
        0,
        "a provider that never sent a granule was dialled again"
    );
    assert_eq!(sim.fetch.poll_timeout(), None, "a timer of the fetch is armed");
    assert_eq!(sim.sess.open_streams(), 1, "the fetch holds more than its one request");
}

#[test]
fn a_connected_and_silent_provider_does_not_hold_a_fetch_that_has_another() {
    let store = PStore::random(75, 4 << 20);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 1000).stall_after(0),
            ProvCfg::new(store.clone(), 1000),
        ],
        ClientStore::new(),
    );
    sim.start();
    sim.run(30);
    assert!(sim.rec.complete(), "the second provider did not finish the fetch");
    assert_eq!(sim.store.covered(), store.len());
}
