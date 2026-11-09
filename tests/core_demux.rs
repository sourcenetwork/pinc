//! Demultiplexing: a datagram reaches exactly the session that owns its connection id, a forced collision is
//! settled by trying the keys, and a datagram nobody owns is dropped and counted.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::cast_possible_truncation
)]

use vinc_core::{Answer, Command, Event, Query, Role, SessionId, TraceEvent, Value};
use vinc_tests::*;

fn drain_trace(net: &mut CoreNet, n: usize) -> Vec<TraceEvent> {
    let mut v = Vec::new();
    while let Some(r) = net.nodes[n].ep.poll_trace() {
        v.push(r.event);
    }
    v
}

fn send(net: &mut CoreNet, n: usize, s: SessionId, data: &[u8]) -> u64 {
    let now = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(
            now,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!()
    };
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
    net.nodes[n]
        .cmd(now, Command::Finish { session: s, stream: id })
        .unwrap();
    id
}

/// The destination id of the first short-header datagram `from` sent to `to`.
fn short_dcid_of(net: &CoreNet, from: std::net::SocketAddr, to: std::net::SocketAddr) -> [u8; 4] {
    let (_, _, d) = net
        .captured
        .iter()
        .rev()
        .find(|(f, t, d)| *f == from && *t == to && d[0] & 0x80 == 0)
        .unwrap();
    d[1..5].try_into().unwrap()
}

#[test]
fn each_datagram_reaches_the_session_that_owns_its_id() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (s, c1, c2) = (net.add(1), net.add(2), net.add(3));
        let (a1, b1) = net.connect_pair(c1, s, ALPN_A, Role::Other);
        let (a2, b2) = net.connect_pair(c2, s, ALPN_A, Role::Other);
        assert_ne!(b1, b2);
        let _ = drain_trace(&mut net, s);
        let (i1, i2) = (send(&mut net, c1, a1, b"from-one"), send(&mut net, c2, a2, b"from-two"));
        let _ = (i1, i2);
        let end = net.now + 5 * SEC_NS;
        assert!(net.run(end, |n| n.nodes[s].fin.len() == 2));
        let got: Vec<_> = net.nodes[s]
            .read
            .iter()
            .map(|((sess, _), v)| (*sess, v.clone()))
            .collect();
        assert!(
            got.contains(&(b1, b"from-one".to_vec())) && got.contains(&(b2, b"from-two".to_vec())),
            "{got:?}"
        );
        let demux: Vec<_> = drain_trace(&mut net, s)
            .into_iter()
            .filter_map(|e| {
                if let TraceEvent::Demux { slot, candidates } = e {
                    Some((slot, candidates))
                } else {
                    None
                }
            })
            .collect();
        assert!(
            !demux.is_empty() && demux.iter().all(|(slot, c)| *c == 1 && *slot < 2),
            "{demux:?}"
        );
    });
}

#[test]
fn a_forced_collision_is_settled_by_the_keys() {
    big_stack(|| {
        for alias_first in [true, false] {
            let mut net = CoreNet::new(5 * MS_NS);
            net.capture = true;
            let (s, c1, c2) = (net.add(1), net.add(2), net.add(3));
            let (a1, b1) = net.connect_pair(c1, s, ALPN_A, Role::Other);
            let (a2, b2) = net.connect_pair(c2, s, ALPN_A, Role::Other);
            // Both clients must have sent a short-header datagram for their id to be known.
            send(&mut net, c1, a1, b"x");
            send(&mut net, c2, a2, b"y");
            net.run_for(SEC_NS);
            let (addr1, addr2, addr_s) = (net.nodes[c1].addr, net.nodes[c2].addr, net.nodes[s].addr);
            let (cid1, cid2) = (short_dcid_of(&net, addr1, addr_s), short_dcid_of(&net, addr2, addr_s));
            assert_ne!(cid1, cid2);
            let _ = drain_trace(&mut net, s);
            // The server's session 1 now also answers to session 2's id (or the reverse): two holders of four bytes.
            let (holder, victim_cid, owner) = if alias_first { (b1, cid2, b2) } else { (b2, cid1, b1) };
            assert!(net.nodes[s].ep.alias_cid(holder, victim_cid));
            // Data for the owner still reaches the owner, whichever holder is tried first.
            let (writer, writer_session) = if alias_first { (c2, a2) } else { (c1, a1) };
            let before = net.nodes[s].read.len();
            send(&mut net, writer, writer_session, b"after-collision");
            let end = net.now + 5 * SEC_NS;
            assert!(net.run(end, |n| n.nodes[s].read.len() > before));
            let got = net.nodes[s]
                .read
                .iter()
                .find(|(_, v)| v.as_slice() == b"after-collision")
                .map(|((sess, _), _)| *sess);
            assert_eq!(got, Some(owner), "alias_first {alias_first}");
            let tr = drain_trace(&mut net, s);
            assert!(
                tr.iter().any(|e| matches!(e, TraceEvent::Demux { candidates: 2, .. })),
                "{tr:?}"
            );
            assert!(tr.iter().any(|e| matches!(e, TraceEvent::Trial { ok: 1, .. })));
            // The holder that does not own the packets stays healthy.
            let Answer::Stats(st) = net.nodes[s].ep.query(Query::Stats(holder)) else {
                panic!()
            };
            assert!(st.established);
        }
    });
}

#[test]
fn a_datagram_nobody_owns_is_dropped_and_counted() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS_NS);
        let (s, c) = (net.add(1), net.add(2));
        net.connect_pair(c, s, ALPN_A, Role::Other);
        let (addr_c, addr_s) = (net.nodes[c].addr, net.nodes[s].addr);
        let before = net.nodes[s].ep.node_stats().dropped_in;
        let mut short = vec![0x40, 9, 9, 9, 9];
        short.extend_from_slice(&[7u8; 60]);
        let mut rng = SplitMix64::new(3);
        let mut junk = vec![0u8; 200];
        rng.fill(&mut junk);
        junk[0] |= 0x80;
        for d in [short, junk, vec![0u8; 4], vec![0xFF; 1]] {
            let now = net.now;
            net.nodes[s].ep.handle_datagram(now, addr_s, addr_c, &mut d.clone());
        }
        let after = net.nodes[s].ep.node_stats().dropped_in;
        assert_eq!(after - before, 4);
        // The session carries on.
        net.run_for(SEC_NS);
        let Answer::Node(ns) = net.nodes[s].ep.query(Query::Node) else {
            panic!()
        };
        assert_eq!(ns.sessions, 1);
        assert!(!net.nodes[s].saw(|e| matches!(e, Event::Closed { .. })));
    });
}
