//! One found record per peer: a later lookup answer replaces the peer's earlier one in its slot, an older record never
//! displaces a newer one, a peer never takes a second slot of the ring, and a new peer takes an empty slot before it
//! evicts another peer.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

mod connect_common;

use core::net::SocketAddr;

use connect_common::{SEC, big_stack, ed, id, record_bytes};
use pinc_connect::carrier::DnsAnswer;
use pinc_connect::client::conn::FOUND;
use pinc_connect::client::{Config, Connectivity, RelayCfg};
use pinc_connect::relay::datagram::Datagram;
use pinc_crypto::{Keypair, NodeId, Software};
use pinc_tests::Host;

type Conn = Connectivity<Software, 1, 4>;

const RELAY_UDP: &str = "203.0.113.10:4433";

fn conn() -> Box<Conn> {
    conn_at(RELAY_UDP.parse().unwrap())
}

fn conn_at(relay_udp: SocketAddr) -> Box<Conn> {
    let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
    let mut relays = [None; 1];
    relays[0] = Some(RelayCfg {
        id: id(&ed(0x77)),
        udp: Some(relay_udp),
        tcp: None,
        ws: None,
    });
    let cfg = Config {
        me: host.identity.node_id(),
        identity: host.identity,
        relays,
        phone: false,
        restarted: false,
        start: 1000 * SEC,
        v6: false,
        keep_learn: false,
    };
    Box::new(Connectivity::new(cfg, host.prekey_info.clone(), Software, 7))
}

/// The relay answers a lookup of `kp`'s node with a record homed on `home`, numbered `seq`.
fn answer(c: &mut Conn, now: u64, kp: &Keypair, home: NodeId, seq: u64) {
    answer_from(c, now, RELAY_UDP.parse().unwrap(), kp, home, seq);
}

/// As `answer`, the datagram arriving from `from`.
fn answer_from(c: &mut Conn, now: u64, from: SocketAddr, kp: &Keypair, home: NodeId, seq: u64) {
    let rec = record_bytes(kp, home, seq);
    let mut out = [0u8; 1500];
    let n = Datagram::DnsReply {
        peer: id(kp),
        answer: DnsAnswer::Record(&rec),
    }
    .encode(&mut out)
    .unwrap();
    assert!(c.handle_udp(now, from, &out[..n]), "{from} is not a relay's address");
}

#[test]
fn a_relay_configured_in_mapped_form_is_matched_from_its_plain_v4_source() {
    big_stack(|| {
        let mapped: SocketAddr = "[::ffff:203.0.113.10]:4433".parse().unwrap();
        let mut c = conn_at(mapped);
        let (kp, home) = (ed(0x79), id(&ed(0x81)));
        answer_from(&mut c, 1001 * SEC, RELAY_UDP.parse().unwrap(), &kp, home, 1);
        assert_eq!(c.found(&id(&kp)).unwrap().home, home);
        // and the plain form configured, the datagram arriving from the mapped form
        let mut c = conn();
        answer_from(&mut c, 1001 * SEC, mapped, &kp, home, 1);
        assert_eq!(c.found(&id(&kp)).unwrap().home, home);
    });
}

#[test]
fn a_second_answer_for_a_peer_replaces_the_first() {
    big_stack(|| {
        let mut c = conn();
        let (kp, h1, h2) = (ed(0x79), id(&ed(0x81)), id(&ed(0x82)));
        let peer = id(&kp);
        answer(&mut c, 1001 * SEC, &kp, h1, 1);
        answer(&mut c, 1002 * SEC, &kp, h2, 2);
        assert_eq!(c.found(&peer).unwrap().home, h2, "found gives the newest answer");
        assert_eq!(c.found_fresh(1002 * SEC, &peer).unwrap().home, h2);
    });
}

#[test]
fn one_peer_never_takes_two_slots() {
    big_stack(|| {
        let mut c = conn();
        let home = id(&ed(0x81));
        let a = ed(0x79);
        let others: Vec<Keypair> = (0..3u8).map(|i| ed(0x90 + i)).collect();
        let mut seq = 0;
        let mut t = 1001 * SEC;
        // FOUND + 1 answers for one peer, with one answer for each other peer among them.
        for i in 0..=FOUND {
            seq += 1;
            t += SEC;
            answer(&mut c, t, &a, home, seq);
            if let Some(o) = others.get(i / 2).filter(|_| i % 2 == 0) {
                t += SEC;
                answer(&mut c, t, o, home, 1);
            }
        }
        for o in &others {
            assert!(
                c.found(&id(o)).is_some(),
                "another peer's entry was pushed out of the ring"
            );
        }
        assert_eq!(c.found(&id(&a)).unwrap().seq, seq);
    });
}

#[test]
fn an_older_answer_does_not_replace_a_newer_one() {
    big_stack(|| {
        let mut c = conn();
        let (kp, h1, h2) = (ed(0x79), id(&ed(0x81)), id(&ed(0x82)));
        let peer = id(&kp);
        answer(&mut c, 1001 * SEC, &kp, h1, 5);
        answer(&mut c, 1050 * SEC, &kp, h2, 3);
        let f = c.found(&peer).unwrap();
        assert_eq!((f.home, f.seq), (h1, 5), "the older record displaced the newer one");
        // The held entry keeps its time: stale 30 s after the first answer, not the second.
        assert!(c.found_fresh(1001 * SEC + 1, &peer).is_some());
        assert!(c.found_fresh(1040 * SEC, &peer).is_none());
    });
}

#[test]
fn a_new_peer_takes_a_forgotten_slot() {
    big_stack(|| {
        let mut c = conn();
        let home = id(&ed(0x81));
        let a = ed(0x79);
        let others: Vec<Keypair> = (0..u8::try_from(FOUND - 1).unwrap()).map(|i| ed(0x90 + i)).collect();
        let mut t = 1001 * SEC;
        answer(&mut c, t, &a, home, 1);
        for o in &others {
            t += SEC;
            answer(&mut c, t, o, home, 1);
        }
        let forgotten = others.get(2).unwrap();
        c.forget_found(&id(forgotten));
        let new = ed(0xa0);
        answer(&mut c, t + SEC, &new, home, 1);
        assert!(c.found(&id(&new)).is_some(), "the new peer was not kept");
        assert!(c.found(&id(forgotten)).is_none(), "the forgotten peer came back");
        for (i, kp) in std::iter::once(&a).chain(&others).enumerate() {
            assert!(
                std::ptr::eq(kp, forgotten) || c.found(&id(kp)).is_some(),
                "a forgotten slot was free and another peer's entry was evicted (peer {i})"
            );
        }
    });
}
