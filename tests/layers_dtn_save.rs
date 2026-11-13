//! A partial bundle's record grows by appends: each verified byte is written about once, a record of any number of
//! runs is saved and restored, and a restored partial keeps the parity it had verified.
//!
//! The partial was saved by rewriting the whole record every 256 KiB of verified bytes, which costs the square of a
//! bundle's size, and a record of more than 65,535 runs (a data-only reception of that many blocks) was never saved
//! at all, so a crash lost the whole partial.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use vinc_node::{Body, DtnPlan, Enabled, NodeEvent, NodeTrace};
use vinc_sim::{MS, NodeId as SimId, SEC, Time};
use vinc_tests::{LayerApps, NCmd, SplitMix64};

/// A source and a destination with `budget` bytes each, in contact from 6 s on; the source makes a bundle of `len`
/// random bytes at `plan` at 2 s. An offer waits 10 minutes for its acknowledgement, longer than any transfer here,
/// so a holder still offers after a long one.
fn world(seed: u64, len: usize, budget: u64, plan: DtnPlan) -> (LWorld, SimId, SimId, Vec<u8>) {
    let mut w = LWorld::build_with(seed, 1, 2, 0, true, move |tag| {
        let mut apps = LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        );
        apps.dtn.budget = budget;
        apps.dtn.policy.retry_ms = 600_000;
        apps.dtn.policy.max_sends = 60;
        apps
    });
    let (src, dst) = (w.members[0], w.members[1]);
    let dst_id = w.id(dst);
    w.apps(src).dtn.windows = Some(vec![(dst_id, 6_000, 4_000_000)]);
    let keys = w.apps(dst).dtn.keys();
    let mut payload = vec![0u8; len];
    SplitMix64::new(seed).fill(&mut payload);
    w.sim.command(
        secs(2),
        src,
        NCmd::DtnSend {
            to: Box::new(keys),
            payload: payload.clone(),
            plan,
        },
    );
    (w, src, dst, payload)
}

fn plan(k: u8, m: u8, slice_log: u8) -> DtnPlan {
    DtnPlan {
        lifetime_ms: 3_600_000,
        copies: 2,
        k,
        m,
        slice_log,
    }
}

fn received(w: &LWorld, dst: SimId) -> Vec<Vec<u8>> {
    w.node_events(dst)
        .into_iter()
        .filter_map(|(_, e)| match e {
            NodeEvent::DtnReceived { payload, .. } => Some(payload),
            _ => None,
        })
        .collect()
}

fn traced(w: &LWorld, n: SimId, f: impl Fn(&NodeTrace) -> bool) -> usize {
    w.sim
        .node(n)
        .traces
        .iter()
        .filter(|(_, item)| matches!(&item.body, Body::Node(t) if f(t)))
        .count()
}

/// Receive `len` bytes and return the record bytes the destination wrote.
fn record_bytes(seed: u64, len: usize, budget: u64) -> u64 {
    let (mut w, _, dst, payload) = world(seed, len, budget, plan(4, 2, 2));
    w.run(secs(3_000));
    assert_eq!(received(&w, dst), vec![payload], "the bundle is received intact");
    let written = w.apps(dst).dtn.record_bytes;
    eprintln!(
        "a {} MiB reception wrote {written} record bytes ({:.2} per payload byte)",
        len >> 20,
        written as f64 / len as f64
    );
    written
}

#[test]
fn a_reception_writes_each_verified_byte_about_once() {
    big(|| {
        let len = 4 << 20;
        let written = record_bytes(61, len, 16 << 20);
        assert!(
            written < len as u64 * 9 / 8,
            "the record grows by appends, not a rewrite per save: {written} bytes for {len}"
        );
    });
}

/// The reception Theo measured: a bundle as large as the default 64 MiB ledger budget allows (40 MiB of payload is
/// about 60 MiB sealed at k = 4, m = 2).
#[test]
fn a_reception_at_the_default_budget_writes_each_verified_byte_about_once() {
    big(|| {
        let len = 40 << 20;
        let written = record_bytes(62, len, 64 << 20);
        assert!(written < len as u64 * 9 / 8, "{written} bytes for {len}");
    });
}

/// Run `w` in steps of `step` from `t` until `done`, failing past `limit`; returns the time reached.
fn run_until(w: &mut LWorld, mut t: Time, step: Time, limit: Time, done: impl Fn(&mut LWorld) -> bool) -> Time {
    while !done(w) {
        t += step;
        assert!(t < limit, "the condition was not reached by {} s", limit / SEC);
        w.run(t);
    }
    t
}

/// Crash `n` just after `t` and restart it a second later.
fn crash_restart(w: &mut LWorld, n: SimId, t: Time) {
    w.sim.crash(t + MS, n);
    w.sim.restart(t + SEC, n);
}

#[test]
fn a_partial_of_more_than_65535_runs_is_saved_and_restored() {
    big(|| {
        // k = 1 at 1 KiB slices: every data slice is a block, and a data-only reception holds one run per block.
        let blocks = 65_600;
        let (mut w, _, dst, payload) = world(63, blocks << 10, 256 << 20, plan(1, 1, 0));
        let runs = 65_536u64;
        let t = run_until(&mut w, secs(2), secs(5), secs(3_000), |w| {
            w.apps(dst)
                .dtn
                .records
                .values()
                .next()
                .is_some_and(|r| r.len() as u64 > runs * (16 + 1024))
        });
        crash_restart(&mut w, dst, t);
        w.run(secs(3_500));
        let restored = w.sim.node(dst).restored;
        assert_eq!(restored.partial, 1, "the partial came back: {restored:?}");
        assert_eq!(restored.dropped, 0, "{restored:?}");
        assert_eq!(received(&w, dst), vec![payload], "and the bundle completes intact");
    });
}

#[test]
fn a_restored_partial_keeps_the_parity_it_had_verified() {
    big(|| {
        let (mut w, src, dst, payload) = world(64, 4 << 20, 16 << 20, plan(4, 2, 2));
        w.run(secs(4));
        // Block 1 is symbols 6..12: data 6..10, parity 10 and 11. Data symbol 7 fails its proof, so the ask that
        // follows it (8..11) carries parity symbol 10.
        let bundles = &mut w.apps(src).dtn.bundles;
        let (sealed, _) = bundles.values_mut().next().unwrap();
        sealed[7 * 4096] ^= 0x01;
        let t = run_until(&mut w, secs(4), 10 * MS, secs(200), |w| {
            traced(w, dst, |t| matches!(t, NodeTrace::DtnSymbols { first: 8, .. })) > 0
        });
        let saved = w.apps(dst).dtn.record_bytes;
        let t = run_until(&mut w, t, 10 * MS, secs(200), |w| w.apps(dst).dtn.record_bytes > saved);
        assert_eq!(
            received(&w, dst),
            Vec::<Vec<u8>>::new(),
            "the crash comes before the bundle is whole"
        );
        crash_restart(&mut w, dst, t);
        w.run(secs(900));
        let restored = w.sim.node(dst).restored;
        assert_eq!((restored.partial, restored.dropped), (1, 0), "{restored:?}");
        assert_eq!(received(&w, dst), vec![payload], "the bundle is opened intact");
        // The restarted node's traces start at the restart. Without parity symbol 10, block 1 would hold 6, 8 and 9
        // only: it would ask 7 again, lose it, and ask 10.
        let asked_again = traced(&w, dst, |t| {
            matches!(t, NodeTrace::DtnParity { .. } | NodeTrace::DtnLost { .. })
        });
        assert_eq!(
            asked_again, 0,
            "the restored partial held its parity symbol: none is asked again"
        );
    });
}
