//! A bundle of more erasure blocks than any interval cap is received, and refused by no one.
//!
//! Reed-Solomon parity sits between the data of consecutive erasure blocks, so a data-only reception holds one
//! disjoint run per block. With `k = 1` every data slice is its own block, so a 300-slice payload makes 300 blocks
//! on a tiny bundle. The reception counts held symbols per block and has no cap on runs, so the destination receives
//! it intact and nobody records a refusal; a reception capped at 256 disjoint ranges would overflow on it.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use pinc_node::{Body, DtnPlan, Enabled, NodeEvent, NodeTrace};
use pinc_tests::{LayerApps, NCmd, SplitMix64};

#[test]
fn a_bundle_of_three_hundred_blocks_is_received_and_refused_by_no_one() {
    big(|| {
        // One hub and two members with delay-tolerant delivery on; traces kept so a refusal would be readable.
        let mut w = LWorld::build_with(77, 1, 2, 0, true, |tag| {
            LayerApps::new(
                tag,
                Enabled {
                    dtn: true,
                    ..Enabled::NONE
                },
            )
        });
        let (src, dst) = (w.members[0], w.members[1]);
        let keys = w.apps(dst).dtn.keys();
        // 300 data slices at k = 1 is 300 erasure blocks. slice_log 0: 1008 plain bytes a slice, a tiny payload.
        let mut payload = vec![0u8; 300 * 1008];
        SplitMix64::new(1).fill(&mut payload);
        let expected = payload.clone();
        w.sim.command(
            secs(2),
            src,
            NCmd::DtnSend {
                to: Box::new(keys),
                payload,
                plan: DtnPlan {
                    lifetime_ms: 120_000,
                    copies: 2,
                    k: 1,
                    m: 1,
                    slice_log: 0,
                },
            },
        );
        w.run(secs(40));

        let got: Vec<Vec<u8>> = w
            .node_events(dst)
            .into_iter()
            .filter_map(|(_, e)| match e {
                NodeEvent::DtnReceived { payload, .. } => Some(payload),
                _ => None,
            })
            .collect();
        assert_eq!(
            got,
            vec![expected],
            "a 300-block bundle must be received once and intact"
        );
        let reasons: Vec<u64> = [src, dst]
            .into_iter()
            .flat_map(|n| w.sim.node(n).traces.clone())
            .filter_map(|(_, item)| match item.body {
                Body::Node(NodeTrace::DtnRefused { reason, .. }) => Some(reason),
                _ => None,
            })
            .collect();
        assert!(
            reasons.is_empty(),
            "an honest bundle is refused by no one; saw {reasons:?}"
        );
    });
}
