//! A holder whose symbols fail their proofs is refused after at most `m + 1` failed asks per block, and the partial
//! bundle stays for a holder that can prove them.
//!
//! The source is the bundle's only holder: 64 KiB at 4 KiB slices, `k = 4` and `m = 2`, so four blocks of six
//! symbols. With every symbol of its copy corrupt, each offer costs exactly `m + 1` lost symbols of block 0 before the
//! block is stuck and the bundle refused. With only block 1 corrupt, block 0 is kept, block 1 is stuck after `m + 1`
//! lost symbols, and the partial is saved; once the source's copy is whole again its next offer resumes the partial,
//! asks nothing of block 0 again, and the bundle is opened intact.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use vinc_node::{Body, DtnPlan, Enabled, NodeEvent, NodeTrace};
use vinc_sim::{NodeId as SimId, Time};
use vinc_tests::{LayerApps, NCmd, SplitMix64};

/// The bytes of one symbol at `slice_log` 2.
const SLICE: usize = 4096;
/// Symbols per erasure block, `k + m`.
const PER: u64 = 6;
/// Parity symbols per block.
const M: usize = 2;

/// A source and a destination in contact from 6 s on, the source holding a 64 KiB bundle from 2 s on; returns the
/// world, the source, the destination and the payload.
fn world(seed: u64) -> (LWorld, SimId, SimId, Vec<u8>) {
    let mut w = LWorld::build_with(seed, 1, 2, 0, true, |tag| {
        let mut apps = LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        );
        apps.dtn.policy.max_sends = 60;
        apps
    });
    let (src, dst) = (w.members[0], w.members[1]);
    let dst_id = w.id(dst);
    w.apps(src).dtn.windows = Some(vec![(dst_id, 6_000, 300_000)]);
    let keys = w.apps(dst).dtn.keys();
    let mut payload = vec![0u8; 64 << 10];
    SplitMix64::new(seed).fill(&mut payload);
    w.sim.command(
        secs(2),
        src,
        NCmd::DtnSend {
            to: Box::new(keys),
            payload: payload.clone(),
            plan: DtnPlan {
                lifetime_ms: 300_000,
                copies: 2,
                k: 4,
                m: 2,
                slice_log: 2,
            },
        },
    );
    w.run(secs(4));
    (w, src, dst, payload)
}

/// Flip a byte of each of `symbols` in the source's copy; returns the copy as it was.
fn corrupt(w: &mut LWorld, src: SimId, symbols: std::ops::Range<u64>) -> Vec<u8> {
    let bundles = &mut w.apps(src).dtn.bundles;
    assert_eq!(bundles.len(), 1, "the source holds the one bundle");
    let (sealed, _) = bundles.values_mut().next().unwrap();
    let whole = sealed.clone();
    for s in symbols.take_while(|s| (*s as usize) * SLICE < whole.len()) {
        sealed[s as usize * SLICE] ^= 0x01;
    }
    whole
}

/// What the destination traced, in order: lost symbols, kept runs and refusals.
#[derive(Debug, PartialEq, Eq)]
enum Seen {
    Lost(u64),
    Kept(u64),
    Refused(u64),
}

fn seen(w: &LWorld, dst: SimId, after: Time) -> Vec<Seen> {
    w.sim
        .node(dst)
        .traces
        .iter()
        .filter(|(at, _)| *at > after)
        .filter_map(|(_, item)| match item.body {
            Body::Node(NodeTrace::DtnLost { symbol, .. }) => Some(Seen::Lost(symbol)),
            Body::Node(NodeTrace::DtnSymbols { first, .. }) => Some(Seen::Kept(first)),
            Body::Node(NodeTrace::DtnRefused { reason, .. }) => Some(Seen::Refused(reason)),
            _ => None,
        })
        .collect()
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

/// The bad-proof refusal code on the wire.
const BAD_PROOF: u64 = 4;

#[test]
fn a_holder_whose_every_symbol_is_corrupt_is_refused_after_m_plus_one_asks() {
    big(|| {
        let (mut w, src, dst, _) = world(301);
        let _ = corrupt(&mut w, src, 0..u64::MAX);
        w.run(secs(40));
        let seen = seen(&w, dst, 0);
        let offers: Vec<&[Seen]> = seen.split_inclusive(|s| matches!(s, Seen::Refused(_))).collect();
        assert!(offers.len() >= 2, "the source offers again after a refusal: {seen:?}");
        for offer in offers.iter().filter(|o| matches!(o.last(), Some(Seen::Refused(_)))) {
            let lost: Vec<u64> = offer
                .iter()
                .filter_map(|s| match s {
                    Seen::Lost(x) => Some(*x),
                    _ => None,
                })
                .collect();
            assert_eq!(
                lost,
                (0..=M as u64).collect::<Vec<_>>(),
                "each offer loses exactly m + 1 symbols of block 0, one per ask, then is refused: {offer:?}"
            );
            assert_eq!(offer.last(), Some(&Seen::Refused(BAD_PROOF)));
            assert!(!offer.iter().any(|s| matches!(s, Seen::Kept(_))), "nothing verifies");
        }
        assert_eq!(received(&w, dst), Vec::<Vec<u8>>::new(), "nothing is received");
    });
}

#[test]
fn a_stuck_holder_then_an_honest_one_completes_from_the_kept_partial() {
    big(|| {
        let (mut w, src, dst, payload) = world(302);
        let whole = corrupt(&mut w, src, PER..2 * PER);
        let mut t = 4;
        while !seen(&w, dst, 0).iter().any(|s| matches!(s, Seen::Refused(_))) {
            t += 1;
            assert!(t < 60, "the destination refuses the stuck holder");
            w.run(secs(t));
        }
        let first = seen(&w, dst, 0);
        let lost: Vec<u64> = first
            .iter()
            .filter_map(|s| match s {
                Seen::Lost(x) => Some(*x),
                _ => None,
            })
            .collect();
        assert_eq!(
            lost,
            (PER..=PER + M as u64).collect::<Vec<_>>(),
            "block 1 is stuck after m + 1 lost symbols: {first:?}"
        );
        assert!(first.contains(&Seen::Kept(0)), "block 0 verified: {first:?}");
        assert_eq!(
            w.apps(dst).dtn.records.len(),
            1,
            "the refused transfer's partial is saved"
        );
        // The source's copy is whole again: its next offer is an honest holder's.
        let refused_at = secs(t);
        w.apps(src).dtn.bundles.values_mut().next().unwrap().0 = whole;
        w.run(secs(120));
        assert_eq!(received(&w, dst), vec![payload], "the bundle is opened intact");
        let second = seen(&w, dst, refused_at);
        assert!(
            second.iter().all(|s| match s {
                Seen::Kept(x) => *x >= PER,
                Seen::Lost(_) | Seen::Refused(_) => false,
            }),
            "the honest holder is asked nothing of block 0 again, loses nothing and is not refused: {second:?}"
        );
    });
}
