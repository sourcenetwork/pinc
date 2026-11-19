//! Local discovery in the simulator: a signed beacon heard on the link makes its sender a candidate path, and the
//! handshake proves the node; a forged beacon makes no candidate.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_sim_common;

use std::net::SocketAddr;

use connect_sim_common::*;
use pinc_sim::LanConfig;
use pinc_tests::{Cmd, ip4};

#[test]
fn a_local_beacon_becomes_a_candidate_path_that_the_handshake_verifies() {
    big(|| {
        let mut w = World::new(61);
        let lan = w.sim.add_lan(LanConfig::default());
        let sa = SocketAddr::new(ip4(192, 168, 1, 2), 4433);
        let sb = SocketAddr::new(ip4(192, 168, 1, 3), 4433);
        // No relay, no record, no hint: the beacon is the only way to find the neighbour.
        let a = w.client_in(&client_spec(0xa1, sa, &[]), lan);
        let b = w.client_in(&client_spec(0xb1, sb, &[]), lan);
        w.run(secs(2));
        let beacons = w.client(a).beacons.clone();
        assert!(!beacons.is_empty(), "the node beaconed in its opening burst");
        // A beacon whose signature is damaged is not a candidate.
        let mut forged = beacons[0].clone();
        let last = forged.len() - 1;
        forged[last] ^= 0x01;
        w.sim.command(secs(2), b, Cmd::Beacon(forged));
        w.dial(secs(2), b, a, vec![]);
        w.run(secs(8));
        assert!(w.connected(b).is_none(), "a forged beacon steered nothing");
        // The real one is.
        w.sim.command(secs(8), b, Cmd::Beacon(beacons[0].clone()));
        w.dial(secs(8), b, a, vec![]);
        w.run(secs(14));
        assert!(w.connected(b).is_some(), "{}", w.dump(b));
        assert!(w.incoming(a).is_some());
        // The beacon schedule: one per second for the first 5 s.
        assert!(w.client(a).beacons.len() >= 5, "{}", w.client(a).beacons.len());
    });
}
