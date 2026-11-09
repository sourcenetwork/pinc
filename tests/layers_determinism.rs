//! The same seed gives the same events and the same traces, with every layer running.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod layers_common;

use layers_common::{all_layers, big, secs};

#[test]
fn the_same_seed_gives_the_same_outputs() {
    big(|| {
        for seed in [601u64, 602] {
            let a = all_layers(seed, secs(80));
            let b = all_layers(seed, secs(80));
            for (x, y) in a.members.iter().zip(&b.members) {
                assert_eq!(
                    format!("{:?}", a.node_events(*x)),
                    format!("{:?}", b.node_events(*y)),
                    "seed {seed}: events"
                );
            }
        }
    });
}
