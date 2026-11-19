//! A protocol id with two owners is refused when the node is built, with an error that names it; ids with one owner
//! each build as before.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

mod node_script;

use node_script::node_with;
use pinc_node::{DTN_ALPN, Enabled, HUB_ALPN, NoApps, SETS_ALPN, VALUES_ALPN};
use pinc_tests::LayerApps;

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn a_hub_protocol_id_that_is_a_layers_is_refused_and_named() {
    big(|| {
        for id in [VALUES_ALPN, SETS_ALPN, DTN_ALPN] {
            let name = String::from_utf8_lossy(id).into_owned();
            // Whether the layer runs or not, its sessions would be told from the hub's by the id alone.
            for enabled in [Enabled::NONE, Enabled::ALL] {
                let Err(e) = node_with(false, &[], id, LayerApps::new(1, enabled)) else {
                    panic!("a node was built whose hub protocol id {name} is also a layer's");
                };
                assert!(e.to_string().contains(&name), "the error names the id {name}: {e}");
            }
        }
    });
}

#[test]
fn distinct_protocol_ids_build() {
    big(|| {
        assert!(node_with(false, &[], HUB_ALPN, NoApps::default()).is_ok());
        assert!(node_with(false, &[], b"app/other", LayerApps::new(1, Enabled::ALL)).is_ok());
        assert!(node_with(true, &[], HUB_ALPN, LayerApps::new(1, Enabled::ALL)).is_ok());
    });
}
