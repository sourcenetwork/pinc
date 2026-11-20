//! One found record per peer: a later lookup answer replaces the peer's earlier one in its slot, an older record never
//! displaces a newer one, and a peer never takes a second slot of the ring.
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
    let host = Box::new(Host::new(0x41, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
    let mut relays = [None; 1];
    relays[0] = Some(RelayCfg {
        id: id(&ed(0x77)),
        udp: Some(RELAY_UDP.parse().unwrap()),
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
    let rec = record_bytes(kp, home, seq);
    let mut out = [0u8; 1500];
    let n = Datagram::DnsReply {
        peer: id(kp),
        answer: DnsAnswer::Record(&rec),
    }
    .encode(&mut out)
    .unwrap();
    assert!(c.handle_udp(now, RELAY_UDP.parse::<SocketAddr>().unwrap(), &out[..n]));
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
