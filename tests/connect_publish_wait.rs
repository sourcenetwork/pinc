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
use vinc_crypto::Software;
use vinc_security::Env;
use vinc_tests::Host;

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
