//! Receiving a value copies no stream bytes: the verifier reads a response where the endpoint received it, so the
//! heap bytes the nodes request while a large value arrives stay far below the value's size.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

mod layers_common;

use layers_common::{LWorld, big, secs};
use pinc_node::{Enabled, NodeEvent};
use pinc_sim::Loss;
use pinc_tests::{LayerApps, NCmd, SplitMix64, meter_endpoint_calls, take_metered_allocs, take_metered_bytes};

pinc_tests::install_counting_allocator!();

fn values_on(tag: u8) -> LayerApps {
    LayerApps::new(
        tag,
        Enabled {
            values: true,
            ..Enabled::NONE
        },
    )
}

#[test]
fn the_receive_path_requests_a_fraction_of_the_value_size_from_the_heap() {
    big(|| {
        for (seed, loss) in [(251u64, Loss::None), (252, Loss::Bernoulli(0.02))] {
            let mut w = LWorld::build_lossy(seed, 2, 3, 0, false, loss, values_on);
            let m = w.members.clone();
            let mut value = vec![0u8; 8 << 20];
            SplitMix64::new(seed).fill(&mut value);
            let root = w.provide(m[1], value.clone());
            // The store's own writes are not what is measured.
            w.apps(m[0]).values.reserve(&root, value.len());
            w.run(secs(29));
            let providers = vec![w.id(m[1])];
            w.sim.command(
                secs(30),
                m[0],
                NCmd::ValuesFetch {
                    root,
                    length: value.len() as u64,
                    ranges: vec![],
                    providers,
                },
            );
            meter_endpoint_calls(true);
            let _ = (take_metered_allocs(), take_metered_bytes());
            w.run(secs(120));
            meter_endpoint_calls(false);
            let bytes = take_metered_bytes();
            let done = w
                .sim
                .events(m[0])
                .iter()
                .any(|(_, e)| matches!(e, pinc_tests::NEv::Node(NodeEvent::ValueComplete { .. })));
            assert!(done, "seed {seed}: the fetch completed");
            eprintln!(
                "seed {seed} {loss:?}: {bytes} heap bytes requested for {} value bytes",
                value.len()
            );
            assert!(
                bytes < (value.len() as u64) / 4,
                "seed {seed}: {bytes} heap bytes were requested while {} bytes arrived",
                value.len()
            );
        }
    });
}
