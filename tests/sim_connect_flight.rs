//! The first-flight rules in the simulator: `B8` (a late-starting node sends a hub its first flight on the direct
//! address only), `THIN_HS0` (a hub Initial resent under 4 s goes by relay paths only), `THIN_HS` (one path per try on
//! a slow uplink, rotating).
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
use vinc_core::is_relay_addr;
use vinc_sim::{LanConfig, LinkConfig, MS, SEC, StreamPolicy, Time};
use vinc_tests::Cmd;

/// A hub (relay) the client dials from inside a LAN that drops UDP, so the direct flight is always lost.
fn blocked_hub(seed: u64, one_way: Time) -> (World, vinc_sim::NodeId, vinc_sim::NodeId, SocketAddr) {
    let mut w = World::new(seed);
    let (r, rs) = w.relay(1, relay_ip(10));
    let lan = w.sim.add_lan(LanConfig {
        udp_block: true,
        up: LinkConfig {
            delay: one_way / 2,
            ..LinkConfig::default()
        },
        down: LinkConfig {
            delay: one_way / 2,
            ..LinkConfig::default()
        },
        ..LanConfig::default()
    });
    let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
    (w, a, r, rs.udp.unwrap())
}

fn flights(w: &World, a: vinc_sim::NodeId, from: Time, to: Time) -> Vec<(Time, bool)> {
    w.client(a)
        .tx_log
        .iter()
        .filter(|(t, _, len)| *t >= from && *t < to && *len >= 1000)
        .map(|(t, r, _)| (*t, is_relay_addr(r)))
        .collect()
}

#[test]
fn a_late_start_dial_to_a_hub_flies_direct_first_and_the_relay_copy_joins_at_the_first_resend() {
    big(|| {
        let (mut w, a, r, udp) = blocked_hub(71, 10 * MS);
        w.run(secs(15));
        let hub = w.relay_node(r).id();
        // The node started at 0 and dials at 15 s: a late start (more than 10 s).
        w.sim.command(
            secs(15),
            a,
            Cmd::Dial {
                node: hub,
                hints: vec![udp],
                role: vinc_core::Role::Hub,
            },
        );
        w.run(secs(15) + 250 * MS);
        let f = flights(&w, a, secs(15), secs(16));
        assert!(
            !f.is_empty() && f.iter().all(|(_, relay)| !relay),
            "only the direct address before the resend: {f:?}"
        );
        w.run(secs(15) + 400 * MS);
        let f = flights(&w, a, secs(15) + 290 * MS, secs(16));
        assert!(
            f.iter().any(|(t, relay)| *relay && *t >= secs(15) + 300 * MS),
            "the relay copy joined at 300 ms: {f:?}"
        );
        w.run(secs(20));
        assert!(
            w.connected(a).is_some(),
            "the hub session came up through the relay copy\n{}",
            w.dump(a)
        );
        assert!(
            w.relay_node(r).relay.stats().local > 0,
            "the hub's endpoint was reached through the carrier"
        );
        let _ = (SEC, LinkConfig::default(), StreamPolicy::default());
    });
}

#[test]
fn a_hub_initial_resent_under_four_seconds_goes_by_the_relay_path_only() {
    big(|| {
        // 1.6 s round trip: the answer through the carrier takes long enough for several tries.
        let (mut w, a, r, udp) = blocked_hub(72, 800 * MS);
        w.run(secs(40));
        let hub = w.relay_node(r).id();
        let t0 = secs(40);
        w.sim.command(
            t0,
            a,
            Cmd::Dial {
                node: hub,
                hints: vec![udp],
                role: vinc_core::Role::Hub,
            },
        );
        w.run(t0 + secs(30));
        let f = flights(&w, a, t0, t0 + secs(30));
        let first = f.first().copied().unwrap();
        assert!(!first.1, "the first try goes to the direct address: {f:?}");
        // The first resend (300 ms) goes by the relay path only, and the direct address stays quiet until the
        // session is established through it.
        let second = f.get(1).copied().unwrap();
        assert!(second.1 && second.0 == t0 + 300 * MS, "the resend is relay-only: {f:?}");
        let est = w
            .when(a, |e| {
                matches!(e, vinc_tests::Ev::Ep(vinc_core::Event::Connected { .. }))
            })
            .unwrap();
        assert!(
            f.iter()
                .filter(|(t, _)| *t > t0 + 100 * MS && *t <= est)
                .all(|(_, relay)| *relay),
            "no direct flight under 4 s: {f:?}"
        );
        assert!(w.connected(a).is_some(), "{}", w.dump(a));
    });
}

/// A client on a slow link (`one_way` each way) with a working UDP path to a relay, and a peer on a normal link.
fn slow_world(seed: u64, one_way: Time) -> (World, vinc_sim::NodeId, vinc_sim::NodeId, vinc_sim::NodeId) {
    let mut w = World::new(seed);
    let (r, rs) = w.relay(1, relay_ip(10));
    let lan = w.sim.add_lan(LanConfig {
        up: LinkConfig {
            delay: one_way / 2,
            ..LinkConfig::default()
        },
        down: LinkConfig {
            delay: one_way / 2,
            ..LinkConfig::default()
        },
        ..LanConfig::default()
    });
    let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
    let b = w.client_public(&client_spec(0xb1, priv_addr(2), &[rs]));
    (w, a, b, r)
}

#[test]
fn on_a_slow_uplink_each_try_goes_out_on_one_path_rotating_by_try() {
    big(|| {
        let (mut w, a, b, _r) = slow_world(73, 300 * MS);
        w.run(secs(20));
        assert!(w.client(a).conn.home().is_some());
        let bh1: SocketAddr = "203.0.113.201:4433".parse().unwrap();
        let bh2: SocketAddr = "203.0.113.202:4433".parse().unwrap();
        let t0 = secs(20);
        w.dial(t0, a, b, vec![bh1, bh2]);
        w.run(t0 + secs(2));
        let all: Vec<_> = w
            .client(a)
            .tx_log
            .iter()
            .filter(|(t, _, l)| *t >= t0 && *l >= 1000)
            .map(|(t, r, _)| (*t - t0, *r))
            .collect();
        // Try 1 goes to the second candidate only, try 2 to the third (the relay path) only: one path per try.
        let dest: Vec<SocketAddr> = all.iter().map(|(_, r)| *r).collect();
        assert_eq!(dest[0], bh2, "{all:?}");
        assert!(is_relay_addr(&dest[1]) && dest.len() == 2, "{all:?}");
        assert!(w.connected(a).is_some());
        let sa = w.connected(a).unwrap();
        let st = w.client(a).session_stats(sa).unwrap();
        assert!(
            st.route.is_some_and(|(_, r)| r != bh1 && r != bh2) && st.path_validated,
            "the session left the black holes for a path that answered: {:?}",
            st.route
        );
        let _ = b;
    });
}

#[test]
fn a_direct_first_hub_session_that_came_up_at_once_gets_its_relay_path_two_seconds_after_creation() {
    big(|| {
        let mut w = World::new(74);
        let (r, rs) = w.relay(1, relay_ip(10));
        let a = w.client_public(&client_spec(0xa1, priv_addr(1), &[rs]));
        w.run(secs(15));
        let hub = w.relay_node(r).id();
        let t0 = secs(15);
        w.sim.command(
            t0,
            a,
            Cmd::Dial {
                node: hub,
                hints: vec![rs.udp.unwrap()],
                role: vinc_core::Role::Hub,
            },
        );
        w.run(t0 + secs(5));
        let est = w
            .when(a, |e| {
                matches!(e, vinc_tests::Ev::Ep(vinc_core::Event::Connected { .. }))
            })
            .unwrap();
        assert!(
            est < t0 + 300 * MS,
            "the direct flight was answered before the first resend"
        );
        let relay_tx: Vec<Time> = w
            .client(a)
            .tx_log
            .iter()
            .filter(|(t, to, _)| *t >= t0 && is_relay_addr(to))
            .map(|(t, _, _)| *t - t0)
            .collect();
        assert!(
            relay_tx
                .first()
                .is_some_and(|t| *t >= 2 * SEC && *t < 2 * SEC + 200 * MS),
            "the relay path joins at 2 s, not before: {relay_tx:?}"
        );
    });
}

#[test]
fn a_dial_to_a_relay_opens_the_carrier_to_that_relay() {
    big(|| {
        let mut w = World::new(92);
        let (_r0, rs0) = w.relay(1, relay_ip(10));
        let (r1, rs1) = w.relay(2, relay_ip(11));
        let a = w.client_public(&client_spec(0xa1, priv_addr(1), &[rs0, rs1]));
        w.run(secs(4));
        let up = |w: &World| {
            w.notices(a)
                .iter()
                .any(|(_, n)| matches!(n, vinc_connect::client::Notice::CarrierUp(1)))
        };
        assert!(!up(&w), "the carrier to the second relay is not open before the dial");
        let hub = w.relay_node(r1).id();
        w.sim.command(
            secs(4),
            a,
            Cmd::Dial {
                node: hub,
                hints: vec![rs1.udp.unwrap()],
                role: vinc_core::Role::Hub,
            },
        );
        w.run(secs(8));
        assert!(
            up(&w),
            "the first flight to a relay also goes through its own relay, which opens its carrier"
        );
    });
}
