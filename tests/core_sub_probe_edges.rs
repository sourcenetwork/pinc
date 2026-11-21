//! The quiet-parent probe (`QUIET_PROBE`, #693) at its edges: what ends a probing dial, how fast a ride is, which
//! addresses a lapse dials, and the bounds of the probe window.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

use pinc_core::{Answer, Command, Event, Query};
use pinc_tests::*;

/// Every entry `SessionAt` lists on node `n`, as its counters.
fn listed(net: &CoreNet, n: usize) -> Vec<pinc_core::SessionStats> {
    (0..)
        .map_while(|i| match net.nodes[n].ep.query(Query::SessionAt(i)) {
            Answer::Stats(st) => Some(st),
            _ => None,
        })
        .collect()
}

/// A dial that probes is listed by `SessionAt` (so a revoke finds it), and closing it ends it: it is reported failed
/// and no handshake ever leaves for its peer, not even once the probe window would have passed.
#[test]
fn a_probing_dial_is_listed_and_closing_it_sends_no_handshake() {
    big_stack(|| {
        let (mut net, a, b) = silent_parent();
        let marker = net.captured.len();
        let (child, _) = dial(&mut net, a, b, ALPN_B);
        let entry = listed(&net, a).into_iter().find(|st| st.session == child);
        let entry = entry.expect("a probing dial is not listed by SessionAt");
        assert!(!entry.established && entry.path.is_none());
        assert_eq!(entry.node, Some(net.nodes[b].node));
        let now = net.now;
        net.nodes[a]
            .cmd(
                now,
                Command::Close {
                    session: child,
                    error: 0,
                },
            )
            .unwrap();
        assert!(!listed(&net, a).iter().any(|st| st.session == child), "the closed dial is still listed");
        net.run_for(5 * SEC_NS);
        assert!(net.nodes[a].saw(|e| matches!(e, Event::ConnectFailed { session: Some(s), .. } if *s == child)));
        assert!(!net.nodes[a].saw(|e| matches!(e, Event::Connected { session, .. } if *session == child)));
        assert!(!handshake_since(&net, marker), "a handshake left for the peer of a closed dial");
    });
}
