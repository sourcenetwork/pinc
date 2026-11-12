//! Carriers in the simulator: UDP blocked, the TCP to WebSocket fallback, lookups over the carrier, middlebox idle
//! timeouts and the lease, relay failover.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_sim_common;

use connect_sim_common::*;
use vinc_connect::client::{Kind, Notice};
use vinc_connect::record::Reach;
use vinc_sim::{LanConfig, SEC, StreamPolicy};

#[test]
fn udp_blocked_forces_a_carrier_that_falls_back_from_tcp_to_websocket_and_still_dials() {
    big(|| {
        let mut w = World::new(21);
        let (r, rs) = w.relay(1, relay_ip(10));
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
        assert!(
            w.notices(a).iter().any(|(_, n)| matches!(n, Notice::CarrierUp(0))),
            "{}",
            w.dump(a)
        );
        assert!(!w.client(a).conn.udp_heard());
        // The lookup goes over the carrier, and the session works through the relay.
        w.dial(secs(12), a, b, vec![]);
        w.run(secs(30));
        let sa = w.connected(a).expect("a connected through the carrier");
        let sb = w.incoming(b).unwrap();
        w.sim.command(
            secs(30),
            a,
            vinc_tests::Cmd::Send {
                session: sa,
                data: b"through ws".to_vec(),
            },
        );
        w.run(secs(35));
        assert_eq!(w.client(b).host.received(sb), b"through ws");
        assert!(
            w.relay_node(r).dns_carrier >= 1 && w.relay_node(r).dns_udp == 0,
            "the lookup rode the carrier"
        );
        assert!(w.relay_node(r).carriers_ws >= 1, "the relay saw a WebSocket carrier");
        let _ = SEC;
    });
}

#[test]
fn a_node_whose_relays_take_no_udp_is_blocked_at_once_and_can_be_found() {
    big(|| {
        let mut w = World::new(23);
        let (_, rs) = w.relay(1, relay_ip(10));
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            ..LanConfig::default()
        });
        // A browser: no relay has a UDP address for it, so it sends no probe and waits for no answer.
        let carrier_only = vinc_tests::RelaySpec { udp: None, ..rs };
        let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[carrier_only]), lan);
        let b = w.client_public(&client_spec(0xb1, priv_addr(2), &[rs]));
        w.run(secs(5));
        assert_eq!(w.client(a).conn.class(), Some(Reach::UdpBlocked), "{}", w.dump(a));
        // With a class it publishes its record, so a peer that only knows its id finds it through the relay.
        w.dial(secs(5), b, a, vec![]);
        w.run(secs(20));
        assert!(w.connected(b).is_some(), "{}", w.dump(b));
        assert!(w.incoming(a).is_some(), "{}", w.dump(a));
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
        assert!(
            lease > 20 * SEC,
            "a lease at or below the real timeout would have been learned from a survivor"
        );
        assert!(
            lease_keep(lease) < 20 * SEC,
            "the keepalive gap {} must undercut the timeout",
            lease_keep(lease)
        );
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
        assert_eq!(
            w.client(a).conn.carrier_state(0),
            vinc_connect::client::link::State::Open
        );

        // STALE_SEND: the second relay's carrier is neither home nor ridden, so nothing keeps it alive. A send onto
        // it after it idled for longer than the lease resets it first and goes out on the new one.
        let peer = w.client(a).host.me;
        let packet = vec![0x40u8; 64];
        w.sim.command(
            secs(800),
            a,
            vinc_tests::Cmd::Raw {
                relay: 1,
                peer,
                data: packet.clone(),
            },
        );
        w.run(secs(830));
        let opened = |w: &World| w.relay_node(r2).carriers_opened.len();
        assert_eq!(opened(&w), 1, "the first send dialed the carrier");
        w.sim.command(
            secs(900),
            a,
            vinc_tests::Cmd::Raw {
                relay: 1,
                peer,
                data: packet,
            },
        );
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
        assert_eq!(
            routed, 2,
            "both packets reached the relay, the second on the new carrier"
        );
    });
}

#[test]
fn a_carrier_nobody_rides_is_checked_while_the_node_has_a_session() {
    big(|| {
        let mut w = World::new(42);
        let (_r1, rs1) = w.relay(1, relay_ip(10));
        let (_r2, rs2) = w.relay(2, relay_ip(20));
        let a = w.client_public(&client_spec(0xa1, priv_addr(1), &[rs1, rs2]));
        let b = w.client_public(&client_spec(0xb1, priv_addr(2), &[rs1, rs2]));
        w.run(secs(6));
        // No session yet: the carrier of the relay that is not the home is not kept checked.
        assert!(!w.client(a).conn.is_kept_checked(1), "{}", w.dump(a));
        // A session on a direct path, riding no relay: every carrier is kept checked from now on.
        let baddr = w.client(b).addr;
        w.dial(secs(6), a, b, vec![baddr]);
        w.run(secs(20));
        let s = w.connected(a).expect("connected");
        assert!(
            w.client(a)
                .session_stats(s)
                .is_some_and(|st| st.route.is_some_and(|(_, r)| !vinc_core::is_relay_addr(&r))),
            "the session runs on the direct path: {}",
            w.dump(a)
        );
        assert!(
            w.client(a).conn.is_kept_checked(0) && w.client(a).conn.is_kept_checked(1),
            "{}",
            w.dump(a)
        );
    });
}

/// A dial of a UDP-dark node whose carrier died silently (its NAT forgot the idle TCP flow after 20 s) at 30 s: when
/// the dial is connected, or `None` by 100 s.
fn dial_over_a_silently_dead_carrier(seed: u64) -> Option<u64> {
    use vinc_sim::{NatConfig, NatKind, PortPolicy};
    let mut w = World::new(seed);
    let (_r1, rs1) = w.relay(1, relay_ip(10));
    let (_r2, rs2) = w.relay(2, relay_ip(20));
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
    let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs1, rs2]), nat);
    let b = w.client_public(&client_spec(0xb1, priv_addr(9), &[rs1, rs2]));
    w.run(secs(30));
    // The address is a hint, so the dial is not held for a lookup; the node is UDP-dark, so only the relay carries it.
    let baddr = w.client(b).addr;
    w.dial(secs(30), a, b, vec![baddr]);
    w.run(secs(100));
    w.sim
        .events(a)
        .iter()
        .find_map(|(t, e)| matches!(e, vinc_tests::Ev::Ep(vinc_core::Event::Connected { .. })).then_some(*t))
}

#[test]
fn a_dial_at_its_third_try_checks_its_carriers_and_replaces_one_that_died_silently() {
    big(|| {
        let at = dial_over_a_silently_dead_carrier(32);
        assert!(
            at.is_some_and(|t| t < secs(45)),
            "the dial waited for the carrier keepalive: {at:?}"
        );
    });
}

#[test]
fn the_home_moves_to_the_second_relay_when_the_first_dies() {
    big(|| {
        use vinc_sim::NatKind;
        let mut w = World::new(41);
        let (r1, rs1) = w.relay(1, relay_ip(10));
        let (r2, rs2) = w.relay(2, relay_ip(20));
        let na = w.nat(NatKind::Symmetric, ext(1), 120 * SEC, 7200 * SEC);
        let nb = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs1, rs2]), na);
        let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[rs1, rs2]), nb);
        w.run(secs(6));
        w.dial(secs(6), a, b, vec![]);
        w.run(secs(15));
        assert!(w.connected(a).is_some(), "connected over the first relay");
        assert_eq!(w.relay_node(r1).relay.record_count(), 2);
        // The first relay dies. Each carrier dial that never opens counts against it; the third failure moves the
        // home to the second relay, whose carrier opens and takes the record.
        w.sim.crash(secs(20), r1);
        w.run(secs(120));
        for n in [a, b] {
            let homes: Vec<usize> = w
                .notices(n)
                .iter()
                .filter_map(|(_, x)| if let Notice::Home(h) = x { Some(*h) } else { None })
                .collect();
            assert_eq!(homes, [0, 1], "the home moved once, to the second relay");
            assert_eq!(
                w.client(n).conn.carrier_state(1),
                vinc_connect::client::link::State::Open
            );
            assert_eq!(w.client(n).conn.home(), Some(1));
        }
        assert_eq!(
            w.relay_node(r2).relay.record_count(),
            2,
            "both records were republished at the second relay"
        );
    });
}

#[test]
fn a_dial_through_the_second_relay_while_the_first_is_dead() {
    big(|| {
        use vinc_sim::NatKind;
        let mut w = World::new(42);
        let (r1, rs1) = w.relay(1, relay_ip(10));
        let (_r2, rs2) = w.relay(2, relay_ip(20));
        w.sim.crash(0, r1);
        let na = w.nat(NatKind::Symmetric, ext(1), 120 * SEC, 7200 * SEC);
        let nb = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs1, rs2]), na);
        let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[rs1, rs2]), nb);
        w.run(secs(60));
        w.dial(secs(60), a, b, vec![]);
        w.run(secs(75));
        let sa = w.connected(a).expect("connected");
        let sb = w.incoming(b).unwrap();
        w.sim.command(
            secs(75),
            a,
            vinc_tests::Cmd::Send {
                session: sa,
                data: b"via two".to_vec(),
            },
        );
        w.run(secs(80));
        assert_eq!(w.client(b).host.received(sb), b"via two");
    });
}

#[test]
fn an_answer_of_no_record_ends_the_wait_of_a_pending_dial() {
    use vinc_connect::relay::Trace;
    big(|| {
        let mut w = World::new(91);
        let (r, rs) = w.relay(1, relay_ip(10));
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            ..LanConfig::default()
        });
        let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
        w.run(secs(15));
        let ghost = vinc_tests::Client::new(&client_spec(0xee, priv_addr(9), &[])).host.me;
        w.sim.command(
            secs(15),
            a,
            vinc_tests::Cmd::Dial {
                node: ghost,
                hints: vec![],
                role: vinc_core::Role::Other,
            },
        );
        w.run(secs(100));
        let lookups = w
            .relay_node(r)
            .traces
            .iter()
            .filter(|(_, t)| matches!(t, Trace::LookupServed { peer, found: false } if *peer == ghost))
            .count();
        assert!(
            (1..=2).contains(&lookups),
            "one answer of no record ends the wait; it is not asked again: {lookups}"
        );
        assert_eq!(w.client(a).conn.lookups_outstanding(), 0);
    });
}

#[test]
fn a_pending_dial_that_ended_drops_its_lookup() {
    big(|| {
        // The relay is down, so the lookup of the dial can never be sent or answered.
        let mut w = World::new(92);
        let (r, rs) = w.relay(1, relay_ip(10));
        w.sim.crash(0, r);
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            ..LanConfig::default()
        });
        let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
        w.run(secs(15));
        let ghost = vinc_tests::Client::new(&client_spec(0xee, priv_addr(9), &[])).host.me;
        w.sim.command(
            secs(15),
            a,
            vinc_tests::Cmd::Dial {
                node: ghost,
                hints: vec![],
                role: vinc_core::Role::Other,
            },
        );
        w.run(secs(20));
        assert_eq!(
            w.client(a).conn.lookups_outstanding(),
            1,
            "the lookup waits for a carrier"
        );
        w.run(secs(120));
        let ended = w.when(a, |e| {
            matches!(e, vinc_tests::Ev::Ep(vinc_core::Event::ConnectFailed { .. }))
        });
        assert!(ended.is_some(), "the dial ended: {}", w.dump(a));
        assert_eq!(
            w.client(a).conn.lookups_outstanding(),
            0,
            "DIAL_PRUNE dropped the lookup of the ended dial"
        );
    });
}

#[test]
fn a_dial_waiting_for_its_peers_address_does_not_resend_its_flight() {
    big(|| {
        // The relay is down, so the lookup of the dial stays unanswered for as long as the dial lives.
        let mut w = World::new(93);
        let (r, rs) = w.relay(1, relay_ip(10));
        w.sim.crash(0, r);
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            ..LanConfig::default()
        });
        let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
        w.run(secs(15));
        let ghost = vinc_tests::Client::new(&client_spec(0xee, priv_addr(9), &[])).host.me;
        w.sim.command(
            secs(15),
            a,
            vinc_tests::Cmd::Dial {
                node: ghost,
                hints: vec![],
                role: vinc_core::Role::Other,
            },
        );
        w.run(secs(30));
        assert_eq!(
            w.client(a).conn.lookups_outstanding(),
            1,
            "the dial still waits for the lookup"
        );
        let session = w.client(a).dialed[0];
        let resends = w
            .client(a)
            .session_stats(session)
            .map(|st| st.transport.handshake_retransmits);
        assert_eq!(resends, Some(0), "the flight was resent while the lookup was pending");
    });
}

#[test]
fn keep_learn_shortens_the_keepalive_after_silent_deaths_until_the_carrier_stops_dying() {
    big(|| {
        let deaths = |learn: bool| {
            let mut w = World::new(95);
            let (_r, rs) = w.relay(1, relay_ip(10));
            // UDP works (so the lease rules stay out), but the NAT forgets an idle TCP flow after 20 s.
            let nat = w.nat(vinc_sim::NatKind::PortRestricted, ext(1), 120 * SEC, 20 * SEC);
            let mut s = client_spec(0xa1, priv_addr(1), &[rs]);
            s.keep_learn = learn;
            let a = w.client_behind(&s, nat);
            w.run(secs(900));
            let downs = w
                .notices(a)
                .into_iter()
                .filter(|(_, n)| matches!(n, Notice::CarrierDown(0)))
                .map(|(t, _)| t / SEC)
                .collect::<Vec<_>>();
            (downs, w.client(a).conn.shared().keep_iv / SEC)
        };
        let (off, iv_off) = deaths(false);
        let (on, iv_on) = deaths(true);
        assert_eq!(iv_off, 0);
        // The check after a recent death is 30 s, longer than the NAT's 20 s: without learning the carrier dies again
        // and again.
        assert!(off.len() >= 15, "{off:?}");
        // Learning halves the silence each death endured; the interval ends under 20 s and the deaths stop.
        assert!((15..20).contains(&iv_on), "{iv_on}");
        assert!(on.len() <= 4 && on.last().is_some_and(|t| *t < 300), "{on:?}");
    });
}
