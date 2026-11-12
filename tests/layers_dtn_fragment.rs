//! A bundle that overflows a receiver's verified-range set is refused as "too fragmented", not as a bad proof.
//!
//! The reception keeps at most `INTERVALS = 64` disjoint verified ranges. Reed-Solomon parity sits between the data
//! of consecutive erasure blocks, so a data-only reception records one range per block; a bundle of more than 64
//! blocks overflows the set. With `k = 1` every data slice is its own block, so a 65-slice payload makes 65 blocks
//! on a tiny bundle. The receiver must refuse it with the `Fragmented` reason (wire code 9), never `BadProof` (4):
//! the data is honest, and a holder that reads "bad proof" has reason to distrust a copy that is actually fine.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use vinc_node::{Body, DtnPlan, Enabled, NodeTrace};
use vinc_tests::{LayerApps, NCmd, SplitMix64};

/// The wire code of a `Fragmented` refusal, and of a `BadProof` refusal, as `dtn_wire::Refusal` numbers them.
const FRAGMENTED: u64 = 9;
const BAD_PROOF: u64 = 4;

#[test]
fn a_bundle_of_too_many_blocks_is_refused_as_fragmented_not_a_bad_proof() {
    big(|| {
        // One hub and two members with delay-tolerant delivery on; traces kept so the refusal reason is readable.
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
        // 65 data slices at k = 1 is 65 erasure blocks, one over the 64-range cap. slice_log 0: 1008 plain bytes a
        // slice, so the payload is tiny.
        let mut payload = vec![0u8; 65 * 1008];
        SplitMix64::new(1).fill(&mut payload);
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

        // The refusal reasons the two nodes recorded (the receiver when it refuses, the holder when it reads the
        // REFUSE frame).
        let reasons: Vec<u64> = [src, dst]
            .into_iter()
            .flat_map(|n| w.sim.node(n).traces.clone())
            .filter_map(|(_, item)| match item.body {
                Body::Node(NodeTrace::DtnRefused { reason, .. }) => Some(reason),
                _ => None,
            })
            .collect();

        assert!(
            reasons.contains(&FRAGMENTED),
            "an overflowing reception must refuse as Fragmented ({FRAGMENTED}); saw {reasons:?}"
        );
        assert!(
            !reasons.contains(&BAD_PROOF),
            "an honest bundle must never be refused as a bad proof ({BAD_PROOF}); saw {reasons:?}"
        );
    });
}
