//! The pinned relay as the home of a node that hears no relay at all: the fallback takes the pin only when a relay
//! is configured at that table position, and otherwise the relay with the lowest id, as without a pin.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

mod connect_common;

use connect_common::{SEC, big_stack, ed, id};
use vinc_connect::client::{Config, Connectivity, RelayCfg};
use vinc_crypto::{Drbg, Software};
use vinc_security::Env;
use vinc_tests::Host;

type Conn = Connectivity<Software, 3, 4>;

/// The relay configured at table position `i`.
fn relay(i: usize) -> RelayCfg {
    let tag = u8::try_from(i).unwrap();
    RelayCfg {
        id: id(&ed(0x70 + tag)),
        udp: Some(format!("203.0.113.{}:4433", 10 + tag).parse().unwrap()),
        tcp: Some(format!("203.0.113.{}:443", 10 + tag).parse().unwrap()),
        ws: None,
    }
}

/// The table position with the lowest relay id among `at`.
fn lowest(at: &[usize]) -> usize {
    *at.iter().min_by_key(|i| relay(**i).id.bytes).unwrap()
}

/// The home of a node with relays at the table positions `at` and `pin` pinned, after ten seconds in which no relay
/// answers a probe and no carrier opens.
fn home_unanswered(at: &'static [usize], pin: Option<usize>) -> Option<usize> {
    big_stack(move || {
        let start = 1000 * SEC;
        let mut host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), start));
        let mut relays = [None; 3];
        for i in at {
            relays[*i] = Some(relay(*i));
        }
        let cfg = Config {
            me: host.identity.node_id(),
            identity: host.identity,
            relays,
            phone: false,
            restarted: false,
            start,
            v6: false,
            keep_learn: false,
        };
        let mut conn: Box<Conn> = Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, 7));
        conn.set_local(&["192.168.1.2:4433".parse().unwrap()]);
        if let Some(p) = pin {
            conn.pin_home(p);
        }
        let mut drbg = Drbg::new(&[0x62; 32]);
        let mut buf = vec![0u8; 2048];
        let mut now = start;
        for _ in 0..100 {
            now += SEC / 10;
            let mut env = Env {
                provider: &Software,
                now,
                drbg: &mut drbg,
            };
            conn.drive(now, &mut *host.ep, &mut env, Some(now / 1_000_000));
            while conn.poll_io().is_some() {}
            while conn.poll_udp(&mut buf).is_some() {}
        }
        conn.home()
    })
}

#[test]
fn without_a_pin_a_node_that_hears_no_relay_takes_the_lowest_id() {
    assert_eq!(home_unanswered(&[0, 1], None), Some(lowest(&[0, 1])));
}

#[test]
fn a_pinned_relay_is_the_home_of_a_node_that_hears_no_relay() {
    let other = 1 - lowest(&[0, 1]);
    assert_eq!(
        home_unanswered(&[0, 1], Some(other)),
        Some(other),
        "the pin, not the lowest id"
    );
}

#[test]
fn a_pin_on_a_position_with_no_relay_is_not_taken_as_the_home() {
    assert_eq!(
        home_unanswered(&[0, 1], Some(2)),
        Some(lowest(&[0, 1])),
        "no relay is configured at the pinned position: the lowest id is the home, as without a pin"
    );
}
