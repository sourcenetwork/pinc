//! A record due for publishing waits for the home carrier: the layer must not report a deadline it cannot act on.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_common;
mod connect_rig;

use std::net::SocketAddr;

use connect_common::{Rec, SEC, big_stack};
use connect_rig::Rig;
use pinc_connect::client::link::State;
use pinc_connect::client::netcheck::HOME_RETRY_NS;
use pinc_connect::relay::datagram::Datagram;
use pinc_crypto::Software;
use pinc_security::Env;
use pinc_tests::Host;

#[test]
fn a_record_due_while_the_home_carrier_is_not_open_is_no_deadline() {
    big_stack(|| {
        let mut host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut rig = Rig::new(&identity, prekey);
        let mut now = 1000 * SEC;
        let Rig {
            conn,
            relay,
            sink,
            drbg,
            udp,
            ..
        } = &mut rig;

        // Address discovery and the home relay, as the rig's bring-up does; the carrier never opens.
        let mut env = Env {
            provider: &Software,
            now,
            drbg,
        };
        conn.probe_all(now, &mut env);
        let mut buf = vec![0u8; 2048];
        let (to, n) = conn.poll_udp(&mut buf).expect("a probe");
        assert_eq!(to, *udp);
        let src: SocketAddr = "198.51.100.5:20000".parse().unwrap();
        relay.datagram(now, src, None, &buf[..n], sink).unwrap();
        let reply = sink
            .effects()
            .into_iter()
            .find_map(|r| if let Rec::Udp(_, b) = r { Some(b) } else { None })
            .expect("the relay answers");
        assert!(conn.handle_udp(now, *udp, &reply));
        assert_eq!(conn.home(), Some(0));

        // The carrier is being dialed, never answered: every tick leaves a deadline in the future.
        for _ in 0..20 {
            now += SEC / 10;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.drive(now, &mut *host.ep, &mut env, Some(now / 1_000_000));
            while conn.poll_io().is_some() {}
            if let Some(d) = conn.next_deadline(now) {
                assert!(d > now, "a deadline {d} that has passed at {now}");
            }
        }
    });
}

#[test]
fn a_relay_datagram_from_the_address_its_session_runs_over_is_taken() {
    use pinc_connect::relay::datagram::Datagram;
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut rig = Rig::new(&identity, prekey);
        let other: SocketAddr = "[fd00::1]:4433".parse().unwrap();
        let src = pinc_crypto::NodeId {
            alg: pinc_crypto::IdentityAlg::Ed25519,
            bytes: [7; 32],
        };
        let mut buf = [0u8; 256];
        let n = Datagram::Spl {
            src,
            flag: 0,
            packet: &[0x41; 40],
        }
        .encode(&mut buf)
        .unwrap();
        // A relay datagram from an address the relay was not configured with is not the layer's.
        assert!(!rig.conn.handle_udp(1000 * SEC, other, &buf[..n]));
        // Once a session of the relay is known to run over that address, a tunnelled packet from it is.
        rig.conn.relay_seen_at(0, other);
        assert!(rig.conn.handle_udp(1000 * SEC, other, &buf[..n]));
        // Its other datagrams are still about the configured address only.
        let n = Datagram::Qad { nonce: [1; 8] }.encode(&mut buf).unwrap();
        assert!(!rig.conn.handle_udp(1000 * SEC, other, &buf[..n]));
    });
}

#[test]
fn a_relay_reached_over_udp_only_costs_no_dial_loop() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut rig = Rig::with_tcp(&identity, prekey, None);
        let mut now = 1000 * SEC;
        let Rig {
            conn,
            relay,
            sink,
            drbg,
            udp,
            ..
        } = &mut rig;
        let mut env = Env {
            provider: &Software,
            now,
            drbg,
        };
        conn.probe_all(now, &mut env);
        let mut buf = vec![0u8; 2048];
        let (to, n) = conn.poll_udp(&mut buf).expect("a probe");
        assert_eq!(to, *udp);
        let src: SocketAddr = "198.51.100.5:20000".parse().unwrap();
        relay.datagram(now, src, None, &buf[..n], sink).unwrap();
        let reply = sink
            .effects()
            .into_iter()
            .find_map(|r| if let Rec::Udp(_, b) = r { Some(b) } else { None })
            .expect("the relay answers");
        assert!(conn.handle_udp(now, *udp, &reply));
        assert_eq!(conn.home(), Some(0));
        // A relay with no TCP or WebSocket address has no stream to open or close, however long the node waits.
        for _ in 0..400 {
            now += SEC / 10;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.tick(now, &mut env, Some(now / 1_000_000));
            assert!(
                conn.poll_io().is_none(),
                "a stream request for a relay with no carrier at {now}"
            );
        }
        // A node that resumes does not dial it either, and its link stays where it was.
        conn.resume(now);
        assert!(conn.poll_io().is_none(), "a stream request for a relay with no carrier");
        assert_eq!(
            conn.carrier_state(0),
            State::Down,
            "the link of a relay with no carrier moved"
        );
    });
}

/// The probes the layer queued for the relay since the last call.
fn probes(rig: &mut Rig) -> usize {
    let mut buf = vec![0u8; 2048];
    let mut n = 0;
    while let Some((_, len)) = rig.conn.poll_udp(&mut buf) {
        n += usize::from(matches!(Datagram::decode(&buf[..len]), Ok(Datagram::Qad { .. })));
    }
    n
}

fn tick_at(rig: &mut Rig, now: u64) {
    let Rig { conn, drbg, .. } = rig;
    let mut env = Env {
        provider: &Software,
        now,
        drbg,
    };
    conn.tick(now, &mut env, Some(now / 1_000_000));
}

#[test]
fn a_client_at_the_clocks_last_instant_probes_once() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut rig = Rig::new(&identity, prekey);
        tick_at(&mut rig, u64::MAX);
        let first = probes(&mut rig);
        tick_at(&mut rig, u64::MAX);
        assert!(first <= 1, "{first} probes in one tick");
        assert_eq!(
            probes(&mut rig),
            0,
            "the client probed again at the clock's last instant"
        );
    });
}

#[test]
fn a_probe_due_exactly_at_the_clocks_last_instant_is_a_deadline() {
    big_stack(|| {
        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        // A relay with no carrier has no link deadline of its own, and with local discovery off no beacon is due.
        let mut rig = Rig::with_tcp(&identity, prekey, None);
        rig.conn.set_local_discovery(false);
        tick_at(&mut rig, u64::MAX - HOME_RETRY_NS);
        assert_eq!(rig.conn.next_deadline(u64::MAX - 1), Some(u64::MAX));
    });
}
