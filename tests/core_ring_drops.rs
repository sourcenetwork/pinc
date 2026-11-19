//! The two host rings (extension frames, reach-out bodies) count what they lose in the node statistics.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use pinc_core::{Command, Role};
use pinc_tests::*;
use pinc_transport::frame::ext;

const FAST: u64 = 5 * MS_NS;

#[test]
fn a_full_extension_ring_counts_each_frame_it_gives_up() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
        // The host of b never reads them: the ring of 8 gives up the oldest for each of the 3 that come after.
        for i in 0..11u8 {
            let t = net.now;
            net.nodes[a]
                .cmd(
                    t,
                    Command::SendExtension {
                        session: sa,
                        ty: ext::PROOF_REQ,
                        body: &[i; 4],
                    },
                )
                .unwrap();
            net.run_for(200 * MS_NS);
        }
        let ns = net.nodes[b].ep.node_stats();
        assert_eq!(ns.ext_dropped, 3);
        assert_eq!(ns.reach_dropped, 0);
    });
}

#[test]
fn a_full_reach_ring_counts_each_body_it_gives_up_and_a_refresh_loses_none() {
    big_stack(|| {
        let mut net = CoreNet::new(FAST);
        let b = net.add(9);
        let mut sessions = Vec::new();
        for tag in 1..=5u8 {
            let a = net.add(tag);
            let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
            sessions.push((a, sa));
        }
        // The ring holds 4 bodies: the fifth session's body takes the place of the oldest.
        for (n, (a, sa)) in sessions.iter().enumerate() {
            let t = net.now;
            net.nodes[*a]
                .cmd(
                    t,
                    Command::SendExtension {
                        session: *sa,
                        ty: ext::REACH_OUT,
                        body: &[n as u8; 3],
                    },
                )
                .unwrap();
            net.run_for(200 * MS_NS);
        }
        assert_eq!(net.nodes[b].ep.node_stats().reach_dropped, 1);
        // A session that sends a newer body replaces its own: nothing is lost.
        let (a, sa) = sessions[4];
        let t = net.now;
        net.nodes[a]
            .cmd(
                t,
                Command::SendExtension {
                    session: sa,
                    ty: ext::REACH_OUT,
                    body: &[7; 3],
                },
            )
            .unwrap();
        net.run_for(200 * MS_NS);
        assert_eq!(net.nodes[b].ep.node_stats().reach_dropped, 1);
        assert_eq!(net.nodes[b].ep.node_stats().ext_dropped, 0);
    });
}
