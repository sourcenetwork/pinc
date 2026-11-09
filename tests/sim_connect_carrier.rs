//! Carriers in the simulator: UDP blocked, the TCP to WebSocket fallback, lookups over the carrier, middlebox idle
//! timeouts and the lease, relay failover.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing, clippy::too_many_lines)]

mod connect_sim_common;

use connect_sim_common::*;
use vinc_connect::client::{Kind, Notice};
use vinc_connect::record::Reach;
use vinc_sim::{LanConfig, SEC, StreamPolicy};

#[test]
fn udp_blocked_forces_a_carrier_that_falls_back_from_tcp_to_websocket_and_still_dials() {
    big(|| {
        let mut w = World::new(21);
        let (_r, rs) = w.relay(1, relay_ip(10));
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            stream: Some(StreamPolicy {
                ports: None,
                tls_only: true,
                reject: true,
            }),
            ..LanConfig::default()
        });
        let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
        let b = w.client_public(&client_spec(0xb1, priv_addr(2), &[rs]));
        w.run(secs(12));
        let kinds: Vec<Kind> = w.client(a).opened.iter().map(|(_, _, k)| *k).collect();
        assert_eq!(kinds.first(), Some(&Kind::Tcp), "TCP is tried first");
        assert!(kinds.contains(&Kind::Ws), "then WebSocket: {kinds:?}");
        assert_eq!(w.client(a).conn.class(), Some(Reach::UdpBlocked), "{}", w.dump(a));
        assert!(w.notices(a).iter().any(|(_, n)| matches!(n, Notice::CarrierUp(0))), "{}", w.dump(a));
        assert!(!w.client(a).conn.udp_heard());
        // The lookup goes over the carrier, and the session works through the relay.
        w.dial(secs(12), a, b, vec![]);
        w.run(secs(30));
        let sa = w.connected(a).expect("a connected through the carrier");
        let sb = w.incoming(b).unwrap();
        w.sim.command(secs(30), a, vinc_tests::Cmd::Send { session: sa, data: b"through ws".to_vec() });
        w.run(secs(35));
        assert_eq!(w.client(b).host.received(sb), b"through ws");
        assert!(w.relay_node(_r).dns_carrier >= 1 && w.relay_node(_r).dns_udp == 0, "the lookup rode the carrier");
        assert!(w.relay_node(_r).carriers_ws >= 1, "the relay saw a WebSocket carrier");
        let _ = SEC;
    });
}

#[test]
fn a_node_that_hears_udp_looks_peers_up_over_udp() {
    big(|| {
        let mut w = World::new(22);
        let (r, rs) = w.relay(1, relay_ip(10));
        let nat_a = w.nat(vinc_sim::NatKind::FullCone, ext(1), 120 * SEC, 7200 * SEC);
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), nat_a);
        let b = w.client_public(&client_spec(0xb1, priv_addr(2), &[rs]));
        w.run(secs(5));
        w.dial(secs(5), a, b, vec![]);
        w.run(secs(10));
        assert!(w.relay_node(r).dns_udp >= 1 && w.relay_node(r).dns_carrier == 0);
        assert!(w.connected(a).is_some());
    });
}

/// A UDP-dark node behind a NAT that forgets an idle TCP flow after `tcp_timeout`.
fn dark_world(seed: u64, tcp_timeout: u64) -> (World, vinc_sim::NodeId, vinc_sim::NodeId, vinc_sim::NodeId) {
    use vinc_sim::{NatConfig, NatKind, PortPolicy};
    let mut w = World::new(seed);
    let (r1, rs1) = w.relay(1, relay_ip(10));
    let (r2, rs2) = w.relay(2, relay_ip(20));
    let lan = w.sim.add_lan(LanConfig {
        udp_block: true,
        ..LanConfig::default()
    });
    let nat = w.sim.add_nat_in(
        NatConfig {
            kind: NatKind::PortRestricted,
            ext_ip: ext(1),
            mapping_timeout: 120 * SEC,
            tcp_timeout,
            refresh_on_inbound: true,
            port_base: 20_000,
            ports: PortPolicy::Sequential,
            no_punch: false,
        },
        lan,
    );
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs1, rs2]), nat);
    (w, a, r1, r2)
}

#[test]
fn the_lease_converges_below_the_middlebox_timeout_then_a_stale_send_resets_a_carrier_that_idled_out() {
    use vinc_connect::client::link::lease_keep;
    big(|| {
        let (mut w, a, _r1, r2) = dark_world(31, 20 * SEC);
        // Learning, second by second: the lease is set by each silent death and only ever falls.
        let mut seen: Vec<(u64, u64)> = Vec::new();
        for t in 1..200 {
            w.run(secs(t));
            let l = w.client(a).conn.shared().lease_hi / SEC;
            if seen.last().is_none_or(|(_, p)| *p != l) {
                seen.push((t, l));
            }
        }
        // The first death comes after the 65 s keepalive (a gap of 61 s since the last write); the next check comes
        // 30 s later (a recent death keeps the home check short); then the lease keepalive of 22.5 s is still too
        // long for a 20 s timeout; 22 s is the gap that finally survives.
        let leases: Vec<u64> = seen.iter().map(|(_, l)| *l).collect();
        assert_eq!(leases, [0, 61, 30, 22], "{seen:?}");
        let lease = w.client(a).conn.shared().lease_hi;
        assert!(lease > 20 * SEC, "a lease at or below the real timeout would have been learned from a survivor");
        assert!(lease_keep(lease) < 20 * SEC, "the keepalive gap {} must undercut the timeout", lease_keep(lease));
        let downs = |w: &World| {
            w.notices(a)
                .into_iter()
                .filter(|(_, n)| matches!(n, Notice::CarrierDown(0)))
                .count()
        };
        assert_eq!(downs(&w), 3);
        // From then on the carrier lives: no further death for ten minutes.
        w.run(secs(800));
        assert_eq!(downs(&w), 3, "the carrier died again");
        assert_eq!(w.client(a).conn.shared().lease_hi, lease);
        assert!(w.client(a).conn.carrier_state(0) == vinc_connect::client::link::State::Open);

        // STALE_SEND: the second relay's carrier is neither home nor ridden, so nothing keeps it alive. A send onto
        // it after it idled for longer than the lease resets it first and goes out on the new one.
        let peer = w.client(a).host.me;
        let packet = vec![0x40u8; 64];
        w.sim.command(secs(800), a, vinc_tests::Cmd::Raw { relay: 1, peer, data: packet.clone() });
        w.run(secs(830));
        let opened = |w: &World| w.relay_node(r2).carriers_opened.len();
        assert_eq!(opened(&w), 1, "the first send dialed the carrier");
        w.sim.command(secs(900), a, vinc_tests::Cmd::Raw { relay: 1, peer, data: packet });
        w.run(secs(910));
        assert_eq!(opened(&w), 2, "the stale carrier was reset and dialed again");
        let downs1 = w
            .notices(a)
            .into_iter()
            .filter(|(t, n)| matches!(n, Notice::CarrierDown(1)) && *t >= secs(900) && *t < secs(901))
            .count();
        assert_eq!(downs1, 1, "the reset happened at the send");
        let routed = w
            .relay_node(r2)
            .traces
            .iter()
            .filter(|(_, t)| matches!(t, vinc_connect::relay::Trace::Routed { .. }))
            .count();
        assert_eq!(routed, 2, "both packets reached the relay, the second on the new carrier");
    });
}
