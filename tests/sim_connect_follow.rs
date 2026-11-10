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

#[test]
fn a_path_that_stops_answering_brings_the_relay_path_and_a_punch_two_seconds_later() {
    big(|| {
        let (mut w, a, b, _r, lans) = pair_lans(95);
        let baddr = w.client(b).addr;
        w.dial(secs(20), a, b, vec![baddr]);
        w.run(secs(30));
        let sa = w.connected(a).unwrap();
        // The direct path between A and B goes dark; A keeps sending.
        w.sim.partition_lans(secs(40), secs(300), &[lans[0]], &[lans[1]], true);
        for t in 41..70 {
            w.sim.command(
                secs(t),
                a,
                Cmd::Datagrams {
                    session: sa,
                    count: 1,
                    len: 100,
                },
            );
        }
        w.run(secs(78));
        assert_eq!(reach_outs(&w, b, secs(30), secs(40)), 0);
        assert!(
            reach_outs(&w, b, secs(41), secs(78)) > 0,
            "after falling back to the relay path the punch ran again\n{}",
            w.dump(b)
        );
    });
}

