//! The time rules of the fetch at the deadline: what `on_timeout` does once the deadline has passed, which failure is
//! reported, and the stall wait never leaving the caps the proofs state (`ValuesTime*.tla`, `Vinc/ValuesTime*.lean`).
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::doc_markdown,
    clippy::assert_is_empty,
    clippy::single_range_in_vec_init,
    clippy::cast_possible_wrap,
    clippy::manual_is_multiple_of,
    clippy::similar_names,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use values_support::*;
use vinc_values::fetch::Io;
use vinc_values::trace::{Event, FailReason, Trace};

fn silent_sim(seed: u64, after: u64) -> Sim {
    let store = PStore::random(seed, 2 << 20);
    Sim::new(
        vec![ProvCfg::new(store, 1000).latency(10 * MS).stall_after(after)],
        ClientStore::new(),
    )
}

fn count(sim: &Sim, f: impl Fn(&Trace) -> bool) -> usize {
    sim.rec.traces.iter().filter(|(_, t)| f(t)).count()
}

/// A call after the deadline only winds the fetch down: the stall redial that is also due is not run (it would hang up
/// and dial sessions of a fetch that fails in the same call).
#[test]
fn a_late_call_fails_with_the_deadline_without_a_redial() {
    let mut sim = silent_sim(61, 400_000);
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(30 * SEC));
    assert!(sim.run_until(20 * SEC, |s| s.fetch.timers().lastp != 0 && s.now > 2 * SEC));
    let t = sim.fetch.timers();
    assert!(t.running && t.lastp != 0);
    let (dials, redials) = (
        count(&sim, |t| matches!(t, Trace::Dial(_))),
        count(&sim, |t| matches!(t, Trace::StallRedial { .. })),
    );
    // The host calls late: the stall wait and the deadline are both long past.
    let now = 100 * SEC;
    sim.now = now;
    sim.sess.now = now;
    {
        let mut io = Io {
            session: &mut sim.sess,
            store: &mut sim.store,
            out: &mut sim.rec,
        };
        sim.fetch.on_timeout(&mut io, now);
    }
    assert!(sim.fetch.is_done());
    assert_eq!(sim.rec.failed(), Some(FailReason::Deadline));
    assert_eq!(count(&sim, |t| matches!(t, Trace::StallRedial { .. })), redials);
    assert_eq!(count(&sim, |t| matches!(t, Trace::Dial(_))), dials);
    assert!(sim.sess.dials.is_empty());
}

/// Whatever the stall state, the fetch is done at the first timer call past the deadline, and `poll_timeout` offers it.
#[test]
fn the_fetch_is_done_the_instant_after_the_deadline() {
    for (seed, after, deadline) in [(62, 0, 9 * SEC), (63, 400_000, 25 * SEC), (64, 100_000, 3 * SEC)] {
        let mut sim = silent_sim(seed, after);
        let ps = sim.all_providers();
        sim.start_with(&[], &ps, Some(deadline));
        let done = sim.run_until(60 * SEC, |s| s.fetch.is_done());
        assert!(done, "seed {seed}: the fetch outlived its deadline");
        assert_eq!(sim.rec.failed(), Some(FailReason::Deadline), "seed {seed}");
        assert!(sim.now > deadline, "seed {seed}: failed at {} ms", sim.now / MS);
        let failed_at = sim
            .rec
            .events
            .iter()
            .find(|(_, e)| matches!(e, Event::Failed(_)))
            .unwrap()
            .0;
        assert_eq!(
            failed_at,
            deadline + 1,
            "seed {seed}: the timer is armed at deadline + 1"
        );
        assert_eq!(sim.fetch.poll_timeout(), None);
    }
}

/// A deadline that is exactly now is not past; the fetch is not failed by the call at the deadline itself.
#[test]
fn the_call_at_the_deadline_does_not_fail() {
    let mut sim = silent_sim(65, 0);
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(7 * SEC));
    sim.run_until(7 * SEC, |_| false);
    assert!(sim.fetch.is_running(), "running at the deadline");
    assert!(sim.fetch.poll_timeout().is_some_and(|t| t <= 7 * SEC + 1));
}

/// A deadline of u64::MAX never expires: the timer saturates and `now > deadline` is never true.
#[test]
fn a_deadline_of_u64_max_never_fires() {
    let mut sim = silent_sim(66, 0);
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(u64::MAX));
    sim.run_until(200 * SEC, |_| false);
    assert!(sim.fetch.is_running());
    assert_eq!(sim.rec.failed(), None);
}

/// The failure reported is the one of the first terminal cause: a fetch that has ended reports nothing more, even if
/// the deadline passes later.
#[test]
fn one_terminal_event_whichever_cause_comes_first() {
    // Every provider lies, then the deadline passes.
    let honest = PStore::random(67, 100_000);
    let mut sim = Sim::new(
        vec![ProvCfg::new(honest.lying(Lie::FlipByte(77)), 1000)],
        ClientStore::new(),
    );
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(60 * SEC));
    sim.run_until(120 * SEC, |_| false);
    let fails: Vec<_> = sim
        .rec
        .events
        .iter()
        .filter(|(_, e)| matches!(e, Event::Failed(_) | Event::Complete))
        .collect();
    assert_eq!(fails.len(), 1);
    assert_eq!(sim.rec.failed(), Some(FailReason::EveryProviderLied));
    // A store that refuses writes, then the deadline.
    let mut cs = ClientStore::new();
    cs.fail_writes = true;
    let mut sim = Sim::new(vec![ProvCfg::new(PStore::random(68, 100_000), 1000)], cs);
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(60 * SEC));
    sim.run_until(120 * SEC, |_| false);
    assert_eq!(sim.rec.failed(), Some(FailReason::Store));
    assert_eq!(
        sim.rec
            .events
            .iter()
            .filter(|(_, e)| matches!(e, Event::Failed(_)))
            .count(),
        1
    );
    // A fetch that completes before the deadline reports Complete, not a failure.
    let mut sim = Sim::uniform(2, 100_000, 4000);
    let ps = sim.all_providers();
    sim.start_with(&[], &ps, Some(60 * SEC));
    sim.run_until(120 * SEC, |_| false);
    assert!(sim.rec.complete());
    assert_eq!(sim.rec.failed(), None);
}

/// The stall wait, from the redial schedule alone, stays within 4 s, 8 s, 16 s, 16 s, ... and a late wake never
/// shortens it.
#[test]
fn the_stall_wait_never_falls_below_the_first_wait_and_follows_the_caps() {
    let mut sim = silent_sim(69, 400_000);
    sim.start();
    let mut seen = 0usize;
    sim.run_until(300 * SEC, |s| {
        let t = s.fetch.timers();
        assert!(
            t.sw >= vinc_values::knobs::STALL_WAIT,
            "sw {} ms fell below the first wait",
            t.sw / MS
        );
        assert!(t.sw <= vinc_values::knobs::STALL_RTT_CAP.max(vinc_values::knobs::LIVE_CAP));
        seen += 1;
        false
    });
    assert!(seen > 10);
}
