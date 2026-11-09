//! System-level regressions of the multi-provider fetch found by the model check of `ValuesSys.tla`: each is a
//! fetch that never ended although an answering provider was reachable the whole time.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    reason = "tests assert freely"
)]

mod values_support;

use values_support::*;

/// A provider whose request stream is refused once (no stream room) while another provider's stream is open: its
/// retry must still go out. The silent first provider never finishes, so only the answering provider can end it.
#[test]
fn a_refused_open_is_retried_while_another_providers_stream_is_open() {
    let store = PStore::random(41, 8 * GROUP as usize);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 1000).stall_after(0),
            ProvCfg::new(store.clone(), 4000),
        ],
        ClientStore::new(),
    );
    sim.sess.max_open = 1;
    sim.start();
    // Both sessions are up at 20 ms; the second open is refused. Room appears before the 200 ms retry.
    sim.run_until(100 * MS, |_| false);
    sim.sess.max_open = usize::MAX;
    sim.run(120);
    assert!(sim.rec.complete(), "failed: {:?}", sim.rec.failed());
    sim.store.assert_verified_is_true(store.content());
    assert_eq!(sim.store.covered(), 8 * GROUP);
}

/// An idle provider that loses its session while it waits to steal must steal after it is back: the re-check timer
/// must survive the missing session.
#[test]
fn an_idle_provider_that_reconnects_still_steals_from_a_silent_one() {
    let store = PStore::random(42, 3 << 20);
    let mut sim = Sim::new(
        vec![
            ProvCfg::new(store.clone(), 1000).stall_after(0),
            ProvCfg::new(store.clone(), 8000),
        ],
        ClientStore::new(),
    );
    sim.start();
    // The answering provider finishes its share and waits for the silent one to turn idle; its session drops and
    // returns before that.
    sim.run_until(500 * MS, |_| false);
    sim.cut(1);
    sim.revive(1);
    sim.run(300);
    assert!(sim.rec.complete(), "failed: {:?}", sim.rec.failed());
    sim.store.assert_verified_is_true(store.content());
    assert_eq!(sim.store.covered(), 3 << 20);
}
