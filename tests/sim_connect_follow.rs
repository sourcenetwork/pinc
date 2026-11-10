//! What the connectivity layer does after the session layer reports trouble or change, in the simulator: the reaction
//! to a path that stopped answering, an address change, the punch timer rules and the broadcast mark.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_sim_common;

use connect_sim_common::*;
use vinc_core::Event;
use vinc_sim::{LanConfig, LinkConfig, MS, Time};
use vinc_tests::{Cmd, Ev};

fn reach_out(e: &Ev) -> bool {
    matches!(e, Ev::Ep(Event::ReachOut { .. }))
}

/// Reach-out messages `n` received between `from` and `to`.
fn reach_outs(w: &World, n: vinc_sim::NodeId, from: Time, to: Time) -> usize {
    w.sim
        .events(n)
        .iter()
        .filter(|(t, e)| *t >= from && *t < to && reach_out(e))
        .count()
}

/// A on a LAN with a 100 ms round trip, B on another, one relay; both have started and found their home.
fn pair(seed: u64) -> (World, vinc_sim::NodeId, vinc_sim::NodeId, vinc_sim::NodeId) {
    let (w, a, b, r, _) = pair_lans(seed);
    (w, a, b, r)
}

fn pair_lans(
    seed: u64,
) -> (
    World,
    vinc_sim::NodeId,
    vinc_sim::NodeId,
    vinc_sim::NodeId,
    [vinc_sim::LanId; 2],
) {
    let mut w = World::new(seed);
    let (r, rs) = w.relay(1, relay_ip(10));
    let lan = w.sim.add_lan(LanConfig {
        up: LinkConfig {
            delay: 25 * MS,
            ..LinkConfig::default()
        },
        down: LinkConfig {
            delay: 25 * MS,
            ..LinkConfig::default()
        },
        ..LanConfig::default()
    });
    let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
    let lan_b = w.sim.add_lan(LanConfig::default());
    let b = w.client_in(&client_spec(0xb1, priv_addr(2), &[rs]), lan_b);
    w.run(secs(20));
    (w, a, b, r, [lan, lan_b])
}

