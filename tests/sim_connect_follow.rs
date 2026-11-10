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

#[test]
fn a_carrier_that_comes_back_makes_the_sessions_riding_it_ping_at_once() {
    use vinc_connect::client::Notice;
    use vinc_core::is_relay_addr;
    use vinc_sim::{NatConfig, NatKind, PortPolicy, SEC};
    big(|| {
        let mut w = World::new(97);
        let (_r, rs) = w.relay(1, relay_ip(10));
        // A is behind a middlebox that forgets idle TCP flows after 20 s: its carrier dies silently now and then.
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            ..LanConfig::default()
        });
        let nat = w.sim.add_nat_in(
            NatConfig {
                kind: NatKind::PortRestricted,
                ext_ip: ext(1),
                mapping_timeout: 120 * SEC,
                tcp_timeout: 20 * SEC,
                refresh_on_inbound: true,
                port_base: 20_000,
                ports: PortPolicy::Sequential,
                no_punch: false,
            },
            lan,
        );
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), nat);
        let b = w.client_public(&client_spec(0xb1, priv_addr(2), &[rs]));
        w.run(secs(10));
        w.dial(secs(10), a, b, vec![]);
        w.run(secs(40));
        assert!(w.connected(a).is_some(), "{}", w.dump(a));
        w.run(secs(400));
        let ups: Vec<Time> = w
            .notices(a)
            .into_iter()
            .filter(|(_, n)| matches!(n, Notice::CarrierUp(0)))
            .map(|(t, _)| t)
            .collect();
        assert!(ups.len() >= 2, "the carrier re-opened: {ups:?}");
        let pinged = ups.iter().skip(1).any(|up| {
            w.client(a)
                .tx_log
                .iter()
                .any(|(t, to, _)| *t >= *up && *t < *up + 50 * MS && is_relay_addr(to))
        });
        assert!(pinged, "no session packet left when a carrier came back: {ups:?}");
    });
}
