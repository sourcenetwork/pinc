//! The delay-tolerant layer after a restart, and on its own timers: a holder that restarts mid transfer hands its
//! bundle over after all, a receiver that restarts keeps the symbols it had verified, and a bundle ends at its expiry
//! to the millisecond, not at the next sweep.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use vinc_node::{DtnPlan, Enabled, NodeEvent};
use vinc_tests::{LayerApps, NCmd, SplitMix64};

fn dtn_on(tag: u8) -> LayerApps {
    let mut apps = LayerApps::new(
        tag,
        Enabled {
            dtn: true,
            ..Enabled::NONE
        },
    );
    // A peer that restarts is silent for a while: the holder keeps trying through it.
    apps.dtn.policy.max_sends = 60;
    apps
}

fn plan(lifetime_s: u64) -> DtnPlan {
    DtnPlan {
        lifetime_ms: lifetime_s * 1000,
        copies: 4,
        k: 4,
        m: 2,
        slice_log: 2,
    }
}

fn payload(seed: u64, len: usize) -> Vec<u8> {
    let mut v = vec![0; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

fn received(w: &LWorld, n: vinc_sim::NodeId) -> Vec<Vec<u8>> {
    w.node_events(n)
        .into_iter()
        .filter_map(|(_, e)| match e {
            NodeEvent::DtnReceived { payload, .. } => Some(payload),
            _ => None,
        })
        .collect()
}

fn dump(w: &LWorld, a: vinc_sim::NodeId, c: vinc_sim::NodeId) {
    for (name, n) in [("holder", a), ("destination", c)] {
        for (at, t) in &w.sim.node(n).traces {
            let line = format!("{:?}", t.body);
            if line.contains("Dtn")
                || line.contains("LayerUp")
                || line.contains("LayerDown")
                || line.contains("LayerDial")
            {
                eprintln!("{name} {:.3}s {line}", *at as f64 / 1e9);
            }
        }
    }
}

#[test]
fn a_large_bundle_crosses_a_direct_link_without_any_fault() {
    big(|| {
        for (seed, len) in [(421u64, 400usize << 10), (422, 3000)] {
            let mut w = LWorld::build_with(seed, 2, 3, 1_000_000, true, dtn_on);
            let (a, c) = (w.members[0], w.members[2]);
            let keys = w.apps(c).dtn.keys();
            let body = payload(seed, len);
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: body.clone(),
                    plan: plan(600),
                },
            );
            w.run(secs(120));
            dump(&w, a, c);
            assert_eq!(
                received(&w, c),
                vec![body],
                "seed {seed}: {len} bytes delivered once, intact"
            );
        }
    });
}

#[test]
fn a_holder_that_restarts_mid_transfer_hands_its_bundle_over_after_all() {
    big(|| {
        for seed in [431u64, 432] {
            let mut w = LWorld::build_with(seed, 2, 3, 1_000_000, true, dtn_on);
            let (a, c) = (w.members[0], w.members[2]);
            let keys = w.apps(c).dtn.keys();
            let body = payload(seed, 400 << 10);
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: body.clone(),
                    plan: plan(600),
                },
            );
            w.sim.crash(secs(33), a);
            w.sim.restart(secs(35), a);
            w.run(secs(200));
            dump(&w, a, c);
            let restored = w.sim.node(a).restored;
            assert_eq!(
                restored.held, 1,
                "seed {seed}: the holder found its bundle again: {restored:?}"
            );
            assert_eq!(restored.dropped, 0, "seed {seed}: {restored:?}");
            assert!(
                received(&w, c).len() <= 1 && received(&w, c).iter().all(|p| *p == body),
                "seed {seed}: delivered at most once, intact"
            );
            assert_eq!(
                received(&w, c).len(),
                1,
                "seed {seed}: the bundle reached its destination"
            );
        }
    });
}

#[test]
fn a_receiver_that_restarts_keeps_the_symbols_it_had_verified() {
    big(|| {
        for seed in [441u64, 442] {
            let mut w = LWorld::build_with(seed, 2, 3, 1_000_000, true, dtn_on);
            let (a, c) = (w.members[0], w.members[2]);
            let keys = w.apps(c).dtn.keys();
            let body = payload(seed, 400 << 10);
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: body.clone(),
                    plan: plan(600),
                },
            );
            w.sim.crash(secs(33), c);
            w.sim.restart(secs(35), c);
            w.run(secs(200));
            dump(&w, a, c);
            let restored = w.sim.node(c).restored;
            assert_eq!(
                restored.partial, 1,
                "seed {seed}: the partial bundle came back: {restored:?}"
            );
            assert_eq!(received(&w, c), vec![body], "seed {seed}: delivered once, intact");
        }
    });
}

#[test]
fn a_bundle_expires_at_its_deadline_and_not_at_a_sweep() {
    big(|| {
        for seed in [451u64, 452, 453] {
            let mut w = LWorld::build(seed, 2, 3, |tag| {
                let mut apps = dtn_on(tag);
                apps.dtn.windows = Some(vec![]);
                apps
            });
            let (a, c) = (w.members[0], w.members[2]);
            let keys = w.apps(c).dtn.keys();
            w.sim.command(
                secs(30),
                a,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: payload(seed, 2000),
                    plan: plan(60),
                },
            );
            w.run(secs(100));
            let at: Vec<u64> = w
                .node_events(a)
                .into_iter()
                .filter_map(|(t, e)| matches!(e, NodeEvent::DtnExpired { .. }).then_some(t))
                .collect();
            assert_eq!(at.len(), 1, "seed {seed}: one expiry");
            // Created at 30 s with 60 s to live.
            let late = at[0].saturating_sub(secs(90));
            assert!(
                at[0] >= secs(90) && late < 10_000_000,
                "seed {seed}: expired {late} ns after its deadline"
            );
        }
    });
}
