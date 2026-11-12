//! A bundle of more erasure blocks than the old cap is received once the reception's interval cap is raised.
//!
//! Reed-Solomon parity sits between the data of consecutive erasure blocks, so a data-only reception records one
//! verified range per block. A bundle of 200 blocks (here `k = 1`, so one block per data slice) needs 200 disjoint
//! ranges: more than the old `INTERVALS = 64`, fewer than the raised 256. With the raised cap the destination
//! receives and opens it; on master it overflows (`DtnError::ReceptionFull`) and is refused, so nothing is received.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use vinc_node::{DtnPlan, Enabled, NodeEvent};
use vinc_tests::{LayerApps, NCmd, SplitMix64};

#[test]
fn a_bundle_of_two_hundred_blocks_is_received_after_the_cap_is_raised() {
    big(|| {
        let mut w = LWorld::build(88, 1, 2, |tag| {
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
        // 200 data slices at k = 1 is 200 erasure blocks: over the old 64-range cap, under the raised 256.
        let mut payload = vec![0u8; 200 * 1008];
        SplitMix64::new(3).fill(&mut payload);
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
            "a 200-block bundle must be received once and intact with the raised interval cap"
        );
    });
}
