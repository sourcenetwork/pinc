//! The addresses a node offers and signs into its record: a port mapping's external address leads them only while a
//! relay saw the node at its IP, and a node with no mapping offers what it always did.
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
use vinc_connect::record::{MAX_ADDRS, Reach};
use vinc_crypto::Software;
use vinc_security::Env;
use vinc_tests::Host;

const NOW: u64 = 1000 * SEC;

fn a(s: &str) -> SocketAddr {
    s.parse().unwrap()
}

fn rig() -> Rig {
    let host = Box::new(Host::new(0x31, a("192.168.1.2:4433"), NOW));
    let (identity, prekey) = (host.identity, host.prekey_info.clone());
    Rig::new(&identity, prekey)
}

/// One round of address discovery: the relay saw the node at `src` and says so.
fn report(rig: &mut Rig, now: u64, src: &str) {
    let Rig {
        conn,
        relay,
        sink,
        drbg,
        udp,
        ..
    } = rig;
    let mut env = Env {
        provider: &Software,
        now,
        drbg,
    };
    conn.probe_all(now, &mut env);
    let mut buf = vec![0u8; 2048];
    let (to, n) = conn.poll_udp(&mut buf).expect("a probe");
    assert_eq!(to, *udp);
    relay.datagram(now, a(src), None, &buf[..n], sink).unwrap();
    let reply = sink
        .effects()
        .into_iter()
        .find_map(|r| if let Rec::Udp(_, b) = r { Some(b) } else { None })
        .expect("the relay answers");
    assert!(conn.handle_udp(now, *udp, &reply));
}

fn offered(rig: &Rig) -> Vec<SocketAddr> {
    let mut out = [a("0.0.0.0:0"); MAX_ADDRS];
    let n = rig.conn.candidates(&mut out);
    out[..n].to_vec()
}

#[test]
fn a_node_with_no_mapping_offers_its_reflexive_address_then_its_local_ones() {
    big_stack(|| {
        let mut rig = rig();
        assert_eq!(offered(&rig), [a("192.168.1.2:4433")]);
        report(&mut rig, NOW, "198.51.100.5:20000");
        assert_eq!(offered(&rig), [a("198.51.100.5:20000"), a("192.168.1.2:4433")]);
        assert_eq!(rig.conn.class(), Some(Reach::Nat));
        // an empty mapping set changes nothing
        rig.conn.set_mapped(NOW, &[]);
        assert_eq!(offered(&rig), [a("198.51.100.5:20000"), a("192.168.1.2:4433")]);
        assert_eq!(rig.conn.class(), Some(Reach::Nat));
    });
}

#[test]
fn a_mapping_no_relay_saw_the_node_at_is_held_and_not_offered() {
    big_stack(|| {
        let mut rig = rig();
        // the address of a LAN host's choosing, before and after the relay's report
        rig.conn.set_mapped(NOW, &[a("1.2.3.4:4433")]);
        assert_eq!(
            offered(&rig),
            [a("192.168.1.2:4433")],
            "nothing vouches for the mapping yet"
        );
        report(&mut rig, NOW, "198.51.100.5:20000");
        assert_eq!(
            offered(&rig),
            [a("198.51.100.5:20000"), a("192.168.1.2:4433")],
            "the relay saw another IP"
        );
        assert_eq!(rig.conn.class(), Some(Reach::Nat));
    });
}

#[test]
fn a_mapping_whose_ip_a_relay_saw_leads_and_is_withdrawn_when_the_link_changes() {
    big_stack(|| {
        let mut rig = rig();
        let mapped = a("198.51.100.5:7777");
        rig.conn.set_mapped(NOW, &[mapped]);
        assert_eq!(offered(&rig), [a("192.168.1.2:4433")], "held, not yet vouched for");
        report(&mut rig, NOW, "198.51.100.5:20000");
        assert_eq!(
            offered(&rig),
            [mapped, a("198.51.100.5:20000"), a("192.168.1.2:4433")],
            "published first as soon as the relay's report makes it pass"
        );
        assert_eq!(rig.conn.class(), Some(Reach::PortMapped));
        // the link changed: nothing vouches for the mapping until a relay reports again
        rig.conn.link_changed(NOW + SEC);
        assert_eq!(
            offered(&rig),
            [a("192.168.1.2:4433")],
            "withdrawn when it stops passing"
        );
        report(&mut rig, NOW + 2 * SEC, "198.51.100.5:20001");
        assert_eq!(offered(&rig).first(), Some(&mapped), "published again");
    });
}
