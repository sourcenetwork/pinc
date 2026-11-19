//! Fine-sliced bundles of many erasure blocks are received whole, asking for data only.
//!
//! Reed-Solomon parity sits between the data of consecutive erasure blocks, so a data-only reception holds one
//! disjoint run of symbols per block. The reception counts held symbols per block, with no cap on runs: a 1 MiB
//! bundle at 4 KiB slices (`slice_log` 2, 65 blocks) and a 4 MiB one (258 blocks) are both received and opened. A
//! reception capped at 256 disjoint verified ranges would overflow on the 4 MiB bundle. Nothing is lost on
//! the way, so the receiver asks for no parity symbol at all: the bytes fetched are the data bytes.
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

/// Send `len` random bytes at 4 KiB slices (k = 4, m = 2) from one member to another; returns the payloads the
/// destination received, the parity symbols it asked for, and the payload sent.
fn send(seed: u64, len: usize) -> (Vec<Vec<u8>>, u64, Vec<u8>) {
    let mut w = LWorld::build_with(seed, 1, 2, 0, true, |tag| {
        let mut apps = LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        );
        apps.dtn.budget = 16 << 20;
        apps
    });
    let (src, dst) = (w.members[0], w.members[1]);
    let keys = w.apps(dst).dtn.keys();
    let mut payload = vec![0u8; len];
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
    w.run(secs(90));
    let got = w
        .node_events(dst)
        .into_iter()
        .filter_map(|(_, e)| match e {
            NodeEvent::DtnReceived { payload, .. } => Some(payload),
            _ => None,
        })
        .collect();
    let parity = w
        .sim
        .node(dst)
        .traces
        .iter()
        .filter_map(|(_, item)| match item.body {
            Body::Node(NodeTrace::DtnParity { symbols, .. }) => Some(symbols),
            _ => None,
        })
        .sum();
    (got, parity, payload)
}

#[test]
fn a_one_mib_bundle_at_four_kib_slices_is_received_whole_with_no_parity() {
    big(|| {
        let (got, parity, sent) = send(88, 1 << 20);
        assert_eq!(got, vec![sent], "a 65-block bundle must be received once and intact");
        assert_eq!(parity, 0, "with no loss the receiver asks for no parity symbol");
    });
}

#[test]
fn a_four_mib_bundle_of_more_blocks_than_any_range_cap_is_received_whole_with_no_parity() {
    big(|| {
        let (got, parity, sent) = send(89, 4 << 20);
        assert_eq!(got, vec![sent], "a 258-block bundle must be received once and intact");
        assert_eq!(parity, 0, "with no loss the receiver asks for no parity symbol");
    });
}
