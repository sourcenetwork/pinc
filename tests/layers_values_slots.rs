//! A provider that refuses a request and a full server that refuses one as busy give the stream, and with it the
//! provider the stream held, back. Each test ends with no provider in use on any node.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod layers_common;

use layers_common::{LWorld, big, completes, data, ids, secs, values_on};
use vinc_node::trace::Body;
use vinc_sim::NodeId as SimId;
use vinc_tests::NCmd;
use vinc_values::knobs::code;
use vinc_values::trace::Trace;

/// The providers in use on node `n`.
fn in_use(w: &LWorld, n: SimId) -> usize {
    w.sim.node(n).node.values_stats().providers_in_use
}

fn fetch(root: [u8; 32], length: usize, providers: Vec<[u8; 32]>) -> NCmd {
    NCmd::ValuesFetch {
        root,
        length: length as u64,
        ranges: vec![],
        providers,
    }
}

/// How many requests the server of node `n` refused with `want`.
fn refused(w: &LWorld, n: SimId, want: u64) -> usize {
    w.sim
        .node(n)
        .traces
        .iter()
        .filter(|(_, t)| matches!(&t.body, Body::Values(0, Trace::Refused { code, .. }) if *code == want))
        .count()
}

#[test]
fn a_provider_that_refuses_a_request_gives_its_stream_back() {
    // Node 2 holds the bytes but never registered the root, so it refuses every request. Once the fetch is cancelled
    // nothing may be in use on either node.
    big(|| {
        let seed = 311u64;
        let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, true, values_on);
        let m = w.members.clone();
        let value = data(seed, 256 << 10);
        let root = w.apps(m[2]).values.provide(value.clone());
        let ask = fetch(root, value.len(), ids(&w, &m[2..3]));
        w.sim.command(secs(30), m[0], ask);
        w.run(secs(40));
        assert!(
            refused(&w, m[2], code::UNAVAILABLE) >= 1,
            "the provider refused no request"
        );
        w.sim.command(secs(41), m[0], NCmd::ValuesCancel(1));
        w.run(secs(50));
        assert_eq!(w.sim.node(m[0]).node.values_running(), 0, "the fetch ended");
        assert_eq!(in_use(&w, m[0]), 0, "the fetching node holds a provider");
        assert_eq!(in_use(&w, m[2]), 0, "the refusing node holds a provider");
    });
}

#[test]
fn the_request_a_full_server_refuses_as_busy_gives_its_provider_back() {
    // Ten requesters ask one provider for eight values each over slow links: a session carries a few requests at
    // once, and together they are more than the server's 32 slots, so some are refused as busy. Once every fetch is
    // cancelled nothing is in use on any node, the refused requests' provider numbers included. The fetches are
    // cancelled, not awaited, because a refused request keeps its stream slot on both ends (vinc#675); the test waits
    // for them once that is fixed.
    big(|| {
        let seed = 341u64;
        let mut w = LWorld::build_with(seed, 2, 11, 1_000_000, true, values_on);
        let m = w.members.clone();
        let values: Vec<Vec<u8>> = (0..8).map(|k| data(seed + k, 256 << 10)).collect();
        let roots: Vec<[u8; 32]> = values.iter().map(|v| w.provide(m[0], v.clone())).collect();
        let providers = ids(&w, &m[0..1]);
        for requester in &m[1..] {
            for (root, value) in roots.iter().zip(&values) {
                let ask = fetch(*root, value.len(), providers.clone());
                w.sim.command(secs(30), *requester, ask);
            }
        }
        w.run(secs(60));
        assert!(
            refused(&w, m[0], code::BUSY) >= 1,
            "the server refused no request as busy"
        );
        for requester in &m[1..] {
            for id in 1..=8 {
                w.sim.command(secs(61), *requester, NCmd::ValuesCancel(id));
            }
        }
        w.run(secs(70));
        for (k, requester) in m[1..].iter().enumerate() {
            assert_eq!(
                w.sim.node(*requester).node.values_running(),
                0,
                "requester {k}: a fetch still runs"
            );
            assert_eq!(in_use(&w, *requester), 0, "requester {k} holds a provider");
        }
        assert_eq!(in_use(&w, m[0]), 0, "the provider holds a requester");
    });
}

#[test]
fn a_request_the_provider_resets_gives_its_provider_back_when_the_fetch_completes() {
    // Node 1 serves the value and node 2 does not hold it, so it refuses every request. The fetch completes from node
    // 1 with no cancel and no stall redial: only the resets give the refused streams' uses of node 2's number back.
    big(|| {
        let seed = 312u64;
        let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, true, values_on);
        let m = w.members.clone();
        let value = data(seed, 1 << 20);
        let root = w.provide(m[1], value.clone());
        w.sim
            .command(secs(30), m[0], fetch(root, value.len(), ids(&w, &m[1..3])));
        w.run(secs(36));
        assert_eq!(completes(&w, m[0]), 1, "the fetch did not complete");
        assert!(refused(&w, m[2], code::UNAVAILABLE) >= 1, "node 2 refused no request");
        assert_eq!(in_use(&w, m[0]), 0, "the fetching node holds a provider");
    });
}

#[test]
fn a_session_that_closes_under_a_fetch_gives_its_provider_back_when_the_fetch_completes() {
    // Nodes 1 and 2 serve the value; node 2 leaves while it sends, so its session closes under the fetch, which
    // completes from node 1 with no cancel and no stall redial: only the closed session gives node 2's streams back.
    big(|| {
        let seed = 313u64;
        let mut w = LWorld::build_with(seed, 2, 3, 8_000_000, true, values_on);
        let m = w.members.clone();
        let value = data(seed, 4 << 20);
        let root = w.provide(m[1], value.clone());
        assert_eq!(w.provide(m[2], value.clone()), root);
        w.sim
            .command(secs(30), m[0], fetch(root, value.len(), ids(&w, &m[1..3])));
        w.sim.command(secs(31), m[2], NCmd::Leave);
        w.run(secs(40));
        assert_eq!(completes(&w, m[0]), 1, "the fetch did not complete");
        assert_eq!(in_use(&w, m[0]), 0, "the fetching node holds a provider");
    });
}
