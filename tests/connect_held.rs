//! The packets a closed carrier holds: the queue itself, and what a slow node does with them when the carrier opens.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

mod connect_common;
mod connect_rig;

use connect_common::{SEC, big_stack, nid};
use connect_rig::{Ans, Custody, Rig};
use vinc_connect::carrier::frame::MAX_PACKET_LEN;
use vinc_connect::client::queue::{HeldQueue, QUEUE_BYTES, QUEUED};
use vinc_crypto::Software;
use vinc_security::{Env, KeyRequest};
use vinc_tests::{Answer, Host};

const MS: u64 = 1_000_000;

struct Soft(Box<Host>);

impl Custody for Soft {
    fn answer(&mut self, now: u64, req: &KeyRequest<'_>) -> Ans {
        match self.0.answer(now, req) {
            Answer::Sig(b, n) => Ans::Sig(b[..n].to_vec()),
            Answer::Secret(s) => Ans::Secret(s),
            Answer::Failed => panic!("the software keys failed"),
        }
    }
}

fn drain(q: &mut HeldQueue) -> Vec<(u8, Vec<u8>)> {
    let mut out = Vec::new();
    let mut buf = [0u8; MAX_PACKET_LEN];
    while let Some((dst, n)) = q.pop(&mut buf) {
        out.push((dst.bytes[0], buf[..n].to_vec()));
    }
    out
}

#[test]
fn the_queue_keeps_order_and_drops_the_oldest_when_full() {
    let mut q = HeldQueue::new();
    for i in 0..QUEUED + 5 {
        let dropped = q.push(&nid(1), &[(i % 251) as u8; 20]);
        assert_eq!(dropped, usize::from(i >= QUEUED), "packet {i}");
    }
    assert_eq!(q.len(), QUEUED);
    let all = drain(&mut q);
    assert_eq!(all.first().unwrap().1[0], 5, "the five oldest were dropped");
    assert_eq!(all.last().unwrap().1[0], ((QUEUED + 4) % 251) as u8);
    // bytes run out before the count with full-size packets
    let big = [7u8; MAX_PACKET_LEN];
    for _ in 0..(QUEUE_BYTES / MAX_PACKET_LEN) + 10 {
        q.push(&nid(2), &big);
    }
    assert_eq!(q.len(), QUEUE_BYTES / MAX_PACKET_LEN);
    assert_eq!(
        q.push(&nid(2), &[0u8; MAX_PACKET_LEN + 1]),
        1,
        "an oversize packet is refused"
    );
    assert_eq!(drain(&mut q).len(), QUEUE_BYTES / MAX_PACKET_LEN);
}

#[test]
fn retain_keeps_the_survivors_in_order_and_the_queue_stays_usable() {
    let mut q = HeldQueue::new();
    for i in 0..10u8 {
        q.push(&nid(i), &[i; 30]);
    }
    q.retain(|_, i, h| i % 3 != 0 && h.packet[0] != 5);
    assert_eq!(q.len(), 5);
    q.push(&nid(99), &[99; 30]);
    let got: Vec<u8> = drain(&mut q).into_iter().map(|(_, p)| p[0]).collect();
    assert_eq!(got, [1, 2, 4, 7, 8, 99]);
    // a decision may look at later packets: keep a packet only when no later one equals it
    for p in [1u8, 2, 1, 3, 2] {
        q.push(&nid(1), &[p; 12]);
    }
    q.retain(|q, i, h| !(i + 1..q.len()).any(|j| q.get(j).is_some_and(|o| o.packet == h.packet)));
    let got: Vec<u8> = drain(&mut q).into_iter().map(|(_, p)| p[0]).collect();
    assert_eq!(got, [1, 3, 2]);
}

/// A node with a down carrier holds 22 packets (2 handshake, 20 short-header) for a peer; the carrier then opens.
/// Returns how many reached the relay.
fn held_then_open(node_rtt: u64) -> u64 {
    let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
    let (identity, prekey) = (host.identity, host.prekey_info.clone());
    let mut keys = Soft(host);
    let mut rig = Rig::new(&identity, prekey);
    rig.conn.set_node_rtt(node_rtt, 0);
    let peer = nid(0xb7);
    let to = rig.conn.path_addr(0, &peer);
    for i in 0..22u8 {
        let mut p = vec![0x40u8; 100];
        p[1] = i;
        if i == 0 || i == 10 {
            p[0] = 0xc0;
        }
        rig.conn.route(1000 * SEC, &*keys.0.ep, to, &p);
    }
    let mut answered = 0;
    let now = rig.bring_up(&mut keys, 1000 * SEC, &mut answered);
    for _ in 0..8 {
        rig.shuttle(&mut keys, now, &mut answered);
    }
    rig.relay.stats().rejected
}

#[test]
fn a_slow_node_drops_all_but_the_newest_eight_short_packets_when_its_carrier_opens() {
    big_stack(|| {
        assert_eq!(
            held_then_open(0),
            22,
            "a node that is not slow sends everything it held"
        );
        assert_eq!(
            held_then_open(299 * MS),
            8 + 2,
            "a slow node keeps the handshake packets and the newest eight"
        );
        assert_eq!(held_then_open(250 * MS), 8 + 2);
        assert_eq!(held_then_open(249 * MS), 22);
    });
}

fn long_packet(scid: u8, len: usize) -> Vec<u8> {
    use vinc_security::ConnId;
    use vinc_transport::packet::{LongHeader, LongType};
    let (dcid, scid) = (ConnId::new(&[1; 8]).unwrap(), ConnId::new(&[scid; 8]).unwrap());
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid,
        scid,
        body_len: 0,
    };
    h.body_len = len - h.header_len() - 1;
    let mut p = vec![0u8; len];
    let mut w = vinc_wire::Writer::new(&mut p);
    h.write(&mut w, 0).unwrap();
    p
}

#[test]
fn a_very_slow_node_drops_held_first_flights_of_established_sessions_and_collapses_identical_copies() {
    use vinc_core::Role;
    use vinc_tests::{ALPN_A, CoreNet};
    big_stack(|| {
        let mut net = CoreNet::new(1_900 * MS);
        net.capture = true;
        let (a, b) = (net.add(1), net.add(2));
        net.connect_pair(a, b, ALPN_A, Role::Other);
        let first = net
            .captured
            .iter()
            .find(|(f, _, d)| *f == net.nodes[a].addr && d[0] & 0x80 != 0 && d.len() >= 1200)
            .map(|(_, _, d)| d.clone())
            .expect("the first flight of the session");
        let other = long_packet(9, 1250);

        let host = Box::new(Host::new(0x31, "192.168.1.2:4433".parse().unwrap(), 1000 * SEC));
        let (identity, prekey) = (host.identity, host.prekey_info.clone());
        let mut keys = Soft(host);
        let mut rig = Rig::new(&identity, prekey);
        let now = 1000 * SEC;
        // A node whose peak round trip is above 3.5 s.
        rig.conn.set_node_rtt(4 * SEC, 4 * SEC);
        let drive = |rig: &mut Rig, net: &mut CoreNet, now: u64| {
            let Rig { conn, drbg, .. } = rig;
            let mut env = Env {
                provider: &Software,
                now,
                drbg,
            };
            conn.drive(now, &mut *net.nodes[a].ep, &mut env, Some(now / 1_000_000));
        };
        let to = rig.conn.path_addr(0, &nid(0xb7));
        let mut held = vec![first.clone(), first, other.clone(), other];
        for i in 0..10u8 {
            let mut p = vec![0x40u8; 100];
            p[1] = i;
            held.push(p);
        }
        for p in &held {
            rig.conn.route(now, &*net.nodes[a].ep, to, p);
        }
        let mut answered = 0;
        let now = rig.bring_up(&mut keys, now, &mut answered);
        drive(&mut rig, &mut net, now);
        for _ in 0..8 {
            rig.shuttle(&mut keys, now, &mut answered);
        }
        // The first flight of the established session is stale, the copies of the other collapse to one, and
        // eight of the ten short packets stay.
        assert_eq!(rig.relay.stats().rejected, 1 + 8);
    });
}
