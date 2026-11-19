//! A data slice no live holder can prove is rebuilt from its erasure block's parity.
//!
//! The source is the bundle's only holder, and its stored copy of one data slice is corrupt before the destination
//! comes into contact: that slice has no holder that can prove it. The destination asks for data; the corrupt slice
//! fails its proof against the signed root, so the destination asks for one parity symbol of that block in its
//! place, and finish rebuilds the slice from any `k` of the block's symbols. The bundle is opened intact, asking for
//! exactly one parity symbol (4 KiB). A receiver that asked for data only would refuse the bundle as a bad proof
//! and never receive it.
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

/// The bytes of one symbol at `slice_log` 2.
const SLICE: u64 = 4096;

#[test]
fn a_data_slice_with_no_live_holder_is_rebuilt_from_parity() {
    big(|| {
        let mut w = LWorld::build_with(93, 1, 2, 0, true, |tag| {
            LayerApps::new(
                tag,
                Enabled {
                    dtn: true,
                    ..Enabled::NONE
                },
            )
        });
        let (src, dst) = (w.members[0], w.members[1]);
        // The source is in contact with the destination only from 6 s on, after its copy has been corrupted.
        let dst_id = w.id(dst);
        w.apps(src).dtn.windows = Some(vec![(dst_id, 6_000, 120_000)]);
        let keys = w.apps(dst).dtn.keys();
        let mut payload = vec![0u8; 64 << 10];
        SplitMix64::new(5).fill(&mut payload);
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
                    k: 4,
                    m: 2,
                    slice_log: 2,
                },
            },
        );
        w.run(secs(4));
        // Block 1 is symbols 6..12 (k + m = 6 a block): data 6..10, parity 10 and 11. Corrupt data symbol 7, inside
        // the run [6, 10) the destination asks for: 6 verifies, 7 fails, and 8, 9 and parity 10 are asked in its place.
        let bundles = &mut w.apps(src).dtn.bundles;
        assert_eq!(bundles.len(), 1, "the source holds the one bundle");
        let (sealed, _) = bundles.values_mut().next().unwrap();
        sealed[(7 * SLICE) as usize] ^= 0x01;
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
            "the bundle must be rebuilt from parity and received intact"
        );
        let traces = w.sim.node(dst).traces.clone();
        let parity: u64 = traces
            .iter()
            .filter_map(|(_, item)| match item.body {
                Body::Node(NodeTrace::DtnParity { symbols, .. }) => Some(symbols),
                _ => None,
            })
            .sum();
        assert_eq!(
            parity * SLICE,
            SLICE,
            "exactly one parity symbol stands in for the one lost data symbol"
        );
        let refused = traces
            .iter()
            .filter(|(_, item)| matches!(item.body, Body::Node(NodeTrace::DtnRefused { .. })))
            .count();
        assert_eq!(
            refused, 0,
            "a slice parity can stand in for is no reason to refuse the bundle"
        );
    });
}
