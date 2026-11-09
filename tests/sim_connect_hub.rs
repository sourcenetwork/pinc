//! The hub tunnel and CARRIER_PULSE in the simulator: a member whose carrier is not open still sends and receives
//! through its hub's UDP session, and a quiet hub session on the hub's own carrier is kept alive by the carrier
//! PING and PONG.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_sim_common;

use connect_sim_common::*;
use vinc_connect::client::link::State;
use vinc_sim::{NatKind, SEC};
use vinc_tests::Cmd;

#[test]
fn a_member_with_no_carrier_sends_and_receives_through_the_hub_tunnel() {
    big(|| {
        let mut w = World::new(81);
        let (r, rs) = w.relay(1, relay_ip(10));
        // A knows the relay's UDP address only: its carrier never opens.
        let mut udp_only = rs;
        udp_only.tcp = None;
        udp_only.ws = None;
        let na = w.nat(NatKind::FullCone, ext(1), 120 * SEC, 7200 * SEC);
        let nb = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[udp_only]), na);
        let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[rs]), nb);
        let hub = w.relay_node(r).id();
        // The hub session first: it is what the tunnel rides on.
        w.sim.command(
            secs(1),
            a,
            Cmd::Dial {
                node: hub,
                hints: vec![rs.udp.unwrap()],
                role: vinc_core::Role::Hub,
            },
        );
        w.run(secs(5));
        assert!(w.connected(a).is_some(), "the hub session is up\n{}", w.dump(a));
        assert!(w.client(a).conn.carrier_state(0) != State::Open, "A has no carrier");

        let hub_session = w.connected(a).unwrap();
        w.dial(secs(6), a, b, vec![]);
        w.run(secs(20));
        let sa = w
            .client(a)
            .dialed
            .iter()
            .copied()
            .find(|s| *s != hub_session)
            .expect("the second dial");
        let sb = w.incoming(b).expect("B has the session");
        assert!(w.client(a).conn.carrier_state(0) != State::Open, "still no carrier");
        w.sim.command(
            secs(20),
            a,
            Cmd::Send {
                session: sa,
                data: b"up the tunnel".to_vec(),
            },
        );
        w.run(secs(25));
        assert_eq!(w.client(b).host.received(sb), b"up the tunnel");
        w.sim.command(
            secs(25),
            b,
            Cmd::Send {
                session: sb,
                data: b"down the tunnel".to_vec(),
            },
        );
        w.run(secs(30));
        assert_eq!(w.client(a).host.received(sa), b"down the tunnel");
        let stats = w.relay_node(r).relay.stats();
        assert!(
            stats.tunnel > 0,
            "the relay tunnelled packets down A's UDP session: {stats:?}"
        );
        assert!(
            stats.carrier > 0,
            "and delivered A's tunnelled packets to B's carrier: {stats:?}"
        );
    });
}

#[test]
fn a_quiet_hub_session_on_its_own_carrier_is_kept_alive_by_the_carrier_ping_and_pong() {
    use vinc_connect::relay::Trace;
    use vinc_sim::LanConfig;
    big(|| {
        let mut w = World::new(82);
        let (r, rs) = w.relay(1, relay_ip(10));
        let lan = w.sim.add_lan(LanConfig {
            udp_block: true,
            ..LanConfig::default()
        });
        let a = w.client_in(&client_spec(0xa1, priv_addr(1), &[rs]), lan);
        w.run(secs(10));
        let hub = w.relay_node(r).id();
        w.sim.command(
            secs(10),
            a,
            Cmd::Dial {
                node: hub,
                hints: vec![],
                role: vinc_core::Role::Hub,
            },
        );
        w.run(secs(20));
        let s = w.connected(a).expect("the hub session is up through the carrier");
        w.run(secs(30));
        let sent_before = w.client(a).tx_log.len();
        // Ten minutes with no application data.
        w.run(secs(620));
        let a_id = w.client(a).host.me;
        let pulses = w
            .relay_node(r)
            .traces
            .iter()
            .filter(|(_, t)| matches!(t, Trace::Pulse { node } if *node == a_id))
            .count();
        assert!(pulses >= 8, "a carrier PING roughly every minute: {pulses}");
        let st = w.client(a).session_stats(s).expect("the session is still there");
        assert!(st.established);
        // The session sent no keepalive PING of its own. What it still transmits is the access re-check, one small
        // packet a minute; without the carrier pulse each minute would add a PING from each side.
        let after = w.client(a).tx_log.len() - sent_before;
        assert!(after <= 12, "the endpoint transmitted {after} datagrams in ten minutes");
        let relay_after = w.relay_node(r).tx_log.iter().filter(|(t, _, _)| *t > secs(30)).count();
        assert!(
            relay_after <= 14,
            "the hub endpoint transmitted {relay_after} datagrams in ten minutes"
        );
        assert!(w.client(a).conn.carrier_state(0) == State::Open);
    });
}

#[test]
fn frames_queued_back_to_back_share_one_carrier_record_and_a_handshake_packet_never_does() {
    big(|| {
        let mut w = World::new(83);
        let (r, rs) = w.relay(1, relay_ip(10));
        let na = w.nat(NatKind::Symmetric, ext(1), 120 * SEC, 7200 * SEC);
        let nb = w.nat(NatKind::Symmetric, ext(2), 120 * SEC, 7200 * SEC);
        let a = w.client_behind(&client_spec(0xa1, priv_addr(1), &[rs]), na);
        let b = w.client_behind(&client_spec(0xb1, priv_addr(2), &[rs]), nb);
        w.run(secs(6));
        let records0 = w.relay_node(r).records;
        w.dial(secs(6), a, b, vec![]);
        w.run(secs(7));
        let sa = w.connected(a).expect("connected");
        let handshake_packets = w.client(a).tx_log.iter().filter(|(_, r, l)| *l >= 1000 && vinc_core::is_relay_addr(r)).count();
        assert!(handshake_packets >= 1);
        // The records the relay got while the handshake ran: one per handshake packet, none merged.
        let hs_records = w.relay_node(r).records - records0;
        assert!(hs_records >= handshake_packets as u64, "{hs_records} records for {handshake_packets} long packets");

        // A burst of full-size datagrams in one step leaves in fewer records than packets.
        w.run(secs(10));
        let (tx0, rec0) = (w.client(a).tx_log.len(), w.relay_node(r).records);
        w.sim.command(secs(10), a, Cmd::Datagrams { session: sa, count: 8, len: 1000 });
        w.run(secs(12));
        let packets = w.client(a).tx_log.len() - tx0;
        let records = (w.relay_node(r).records - rec0) as usize;
        assert!(packets >= 8, "{packets}");
        assert!(records < packets, "{packets} packets in {records} carrier records");
    });
}
