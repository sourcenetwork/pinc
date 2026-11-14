//! A first flight or an answer that reaches an endpoint out of order.
//!
//! The later part of a first message that arrives before the part that starts it waits in a small table (at most 4
//! datagrams for the whole endpoint, for at most 1 s, the oldest given up first) and goes only to the session that the
//! start of the same message from the same address creates; holding it sends nothing. An answer that overtakes the
//! Reply that brings its keys waits for them. The Reply of every identity leaves on the budget of the first Initial.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::cell::RefCell;
use std::net::SocketAddr;
use std::rc::Rc;

use vinc_core::{Answer, Command, Event, NodeStats, Query, Role, Value};
use vinc_crypto::IdentityAlg;
use vinc_security::ConnId;
use vinc_tests::*;
use vinc_transport::packet::{LongHeader, LongType};
use vinc_wire::{Reader, Writer};

const MS: u64 = MS_NS;

/// A long Handshake datagram of `len` bytes that carries the part at `offset` of a 4095-byte message for `odcid`
/// (a full Initial when it starts the message).
fn fragment(odcid: u64, offset: u64, len: usize) -> Vec<u8> {
    let mut d = vec![0u8; len];
    let mut h = LongHeader {
        ty: LongType::Handshake,
        dcid: ConnId::new(&odcid.to_be_bytes()).unwrap(),
        scid: ConnId::new(&[1, 2, 3, 4]).unwrap(),
        body_len: 0,
    };
    // The length field is a varint of one or two bytes; settle the body length it describes.
    for _ in 0..3 {
        h.body_len = len - h.header_len();
    }
    let mut w = Writer::new(&mut d);
    h.write(&mut w, 0).unwrap();
    w.put_varint(4095).unwrap();
    w.put_varint(offset).unwrap();
    w.put_u8(1).unwrap();
    d
}

/// The message type a first-flight datagram starts with, if it starts a message.
fn message_type(d: &[u8]) -> Option<u8> {
    let (h, n) = LongHeader::parse(d).ok()?;
    let mut r = Reader::new(d.get(n..n + h.body_len)?);
    r.read_varint().ok()?;
    (r.read_varint().ok()? == 0).then(|| r.read_u8().ok()).flatten()
}

/// Keep back the datagrams `from` sends from now on for which `hold` says so (`hold(k)` for the `k`th, from 0); the
/// kept ones are returned in the order they were sent.
fn hold_back(net: &mut CoreNet, from: SocketAddr, hold: impl Fn(usize) -> bool + 'static) -> Rc<RefCell<Vec<Vec<u8>>>> {
    let kept = Rc::new(RefCell::new(Vec::new()));
    let store = kept.clone();
    let mut k = 0;
    net.loss = Some(Box::new(move |f, _, d| {
        if f != from {
            return false;
        }
        let take = hold(k);
        k += 1;
        if take {
            store.borrow_mut().push(d.to_vec());
        }
        take
    }));
    kept
}

/// Every datagram the table took is accounted for.
fn balanced(s: &NodeStats) -> bool {
    s.fragments_held == s.fragments_replayed + s.fragments_expired + s.fragments_evicted + s.fragments_waiting as u64
}

fn connected(net: &CoreNet, n: usize) -> bool {
    net.nodes[n].saw(|e| matches!(e, Event::Connected { .. }))
}

#[test]
fn a_later_part_of_the_first_flight_that_arrives_first_waits_for_its_start() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS);
        let (a, b) = (net.add(1), net.add(2));
        let (from, to, peer) = (net.nodes[a].addr, net.nodes[b].addr, net.nodes[b].node);
        // The datagram that starts the Initial is kept back; the one with the rest of it goes ahead.
        let kept = hold_back(&mut net, from, |k| k == 0);
        let t0 = net.now;
        net.nodes[a].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
        net.run(t0 + 12 * MS, |_| false);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.fragments_held, s.fragments_waiting, s.sessions), (1, 1, 0));
        assert!(net.nodes[b].sent.is_empty(), "holding a part sent something");
        // The start arrives 2 ms after the rest: the session it creates takes the held part and answers at once.
        net.loss = None;
        let start = kept.borrow()[0].clone();
        net.inject(from, to, start, 0);
        assert!(net.run(t0 + SEC_NS, |n| connected(n, a)));
        assert!(
            net.now - t0 < 50 * MS,
            "connected at {} ms: the dialer waited for its resend",
            (net.now - t0) / MS
        );
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.fragments_replayed, s.fragments_waiting), (1, 0));
        assert!(balanced(&s));
    });
}

#[test]
fn a_flood_of_parts_from_many_addresses_stays_bounded_and_a_real_dial_still_connects() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS);
        let (a, b) = (net.add(1), net.add(2));
        let (from, to, peer) = (net.nodes[a].addr, net.nodes[b].addr, net.nodes[b].node);
        let flood = |net: &mut CoreNet, first: u64, n: u64| {
            for i in first..first + n {
                let x: SocketAddr = ([172, 16, (i >> 8) as u8, i as u8], 7000).into();
                net.inject(x, to, fragment(i, 1100, 1200), 0);
            }
        };
        flood(&mut net, 0, 1000);
        net.run_for(MS);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!(
            (s.fragments_held, s.fragments_evicted, s.fragments_waiting),
            (1000, 996, 4)
        );
        assert_eq!((s.sessions, s.half_open), (0, 0));
        assert!(balanced(&s));
        assert!(net.nodes[b].sent.is_empty(), "a held part caused a send");
        // A real dial whose first flight is reordered while the flood goes on and pushes its held part out.
        let kept = hold_back(&mut net, from, |k| k == 0);
        let t0 = net.now;
        net.nodes[a].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
        net.run(t0 + 6 * MS, |_| false);
        flood(&mut net, 1000, 10);
        net.run_for(MS);
        assert_eq!(net.nodes[b].ep.node_stats().fragments_waiting, 4);
        net.loss = None;
        let start = kept.borrow()[0].clone();
        net.inject(from, to, start, 0);
        assert!(
            net.run(t0 + 5 * SEC_NS, |n| connected(n, a)),
            "the dial did not connect under the flood"
        );
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.fragments_held, s.fragments_replayed), (1011, 0));
        assert!(s.fragments_waiting <= 4 && balanced(&s));
    });
}

#[test]
fn a_held_part_whose_start_never_comes_expires_and_is_never_given_out() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS);
        let b = net.add(2);
        let to = net.nodes[b].addr;
        let x: SocketAddr = "10.9.9.9:4000".parse().unwrap();
        net.inject(x, to, fragment(77, 1100, 1200), 0);
        net.run_for(500 * MS);
        assert_eq!(net.nodes[b].ep.node_stats().fragments_waiting, 1);
        // Past 1 s the part is let go at the next call into the endpoint.
        net.run_for(600 * MS);
        let now = net.now;
        net.nodes[b].ep.handle_timeout(now);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.fragments_expired, s.fragments_waiting), (1, 0));
        // Its start arrives now from the same address: the session it creates does not get the expired part.
        net.inject(x, to, fragment(77, 0, 1200), 0);
        net.run_for(MS);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.sessions, s.fragments_held, s.fragments_replayed), (1, 1, 0));
        assert!(balanced(&s));
        assert!(
            net.nodes[b].sent.is_empty(),
            "a held part or an incomplete Initial was answered"
        );
    });
}

#[test]
fn a_forged_part_given_to_a_new_session_does_not_stop_the_real_dial() {
    big_stack(|| {
        let mut net = CoreNet::new(5 * MS);
        let (a, b) = (net.add(1), net.add(2));
        let (from, to, peer) = (net.nodes[a].addr, net.nodes[b].addr, net.nodes[b].node);
        // Both datagrams of the first flight are kept back; an attacker on the path has seen the second.
        let kept = hold_back(&mut net, from, |k| k < 2);
        let t0 = net.now;
        net.nodes[a].connect(t0, peer, ALPN_A, to, Role::Other).unwrap();
        net.run(t0 + MS, |_| false);
        net.loss = None;
        let (start, rest) = (kept.borrow()[0].clone(), kept.borrow()[1].clone());
        // The attacker sends a changed copy of the rest from the dialer's address ahead of the start: the session the
        // start creates assembles the changed Initial, whose Reply the dialer cannot authenticate.
        let mut forged = rest;
        *forged.last_mut().unwrap() ^= 0xff;
        net.inject(from, to, forged, 0);
        net.inject(from, to, start, MS);
        net.run_for(20 * MS);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.fragments_held, s.fragments_replayed), (1, 1));
        assert!(
            !connected(&net, a),
            "the dialer accepted a session built on a forged Initial"
        );
        // The dialer's own resend starts the real session beside the forged one, which ends at its half-open limit.
        assert!(
            net.run(t0 + 10 * SEC_NS, |n| connected(n, a)),
            "the real dial never connected"
        );
        net.run_for(2 * SEC_NS);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!(
            (s.sessions, s.half_open, s.fragments_waiting),
            (2, 1, 0),
            "the forged session was freed"
        );
        net.run_for(vinc_core::HALF_OPEN_HOLD + SEC_NS);
        let s = net.nodes[b].ep.node_stats();
        assert_eq!((s.sessions, s.half_open, s.fragments_waiting), (1, 0, 0));
        assert!(balanced(&s));
    });
}

#[test]
fn an_answer_that_overtakes_the_resume_reply_waits_for_its_keys() {
    big_stack(|| {
        let mut net = CoreNet::new(10 * MS);
        let (a, b) = (net.add(1), net.add(2));
        let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        let deadline = net.now + 5 * SEC_NS;
        assert!(
            net.run(deadline, |n| !n.nodes[a].ep.tickets().is_empty()),
            "no ticket arrived"
        );
        let t = net.now;
        net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
        net.run_for(SEC_NS);
        for n in &mut net.nodes {
            n.read.clear();
        }
        let (from_b, to_a, to_b, peer) = (
            net.nodes[b].addr,
            net.nodes[a].addr,
            net.nodes[b].addr,
            net.nodes[b].node,
        );
        // The server's first datagram, the Reply, is kept back and arrives 5 ms after the answer sent behind it.
        let kept = hold_back(&mut net, from_b, |k| k == 0);
        let t0 = net.now;
        let rep = net.nodes[a].connect(t0, peer, ALPN_A, to_b, Role::Other).unwrap();
        let s = net.nodes[a].session(&rep);
        let Value::Stream(id) = net.nodes[a]
            .cmd(t0, Command::OpenStream { session: s, bidi: true })
            .unwrap()
            .value
        else {
            panic!("no stream")
        };
        net.nodes[a]
            .cmd(
                t0,
                Command::Write {
                    session: s,
                    stream: id,
                    data: b"H",
                },
            )
            .unwrap();
        let (mut released, mut answered) = (false, false);
        let ok = net.run(t0 + 30 * MS, |n| {
            if !released && !kept.borrow().is_empty() {
                let reply = kept.borrow()[0].clone();
                n.loss = None;
                n.inject(from_b, to_a, reply, 15 * MS);
                released = true;
            }
            if !answered && let Some((sb, sid)) = n.nodes[b].read.iter().find(|(_, v)| !v.is_empty()).map(|(k, _)| *k) {
                let t = n.now;
                n.nodes[b]
                    .cmd(
                        t,
                        Command::Write {
                            session: sb,
                            stream: sid,
                            data: b"k",
                        },
                    )
                    .unwrap();
                // As a host does after every call: the answer leaves now, right behind the Reply.
                n.pump(b);
                answered = true;
            }
            n.nodes[a].read.get(&(s, id)).is_some_and(|v| v == b"k")
        });
        assert!(released && answered);
        assert!(ok, "the answer waited for a retransmission");
        let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(s)) else {
            panic!("no session")
        };
        assert!(
            st.transport.early_buffered >= 1,
            "the answer did not arrive ahead of the Reply"
        );
    });
}

#[test]
fn the_reply_of_every_identity_leaves_on_the_budget_of_the_first_initial() {
    big_stack(|| {
        for alg in [
            IdentityAlg::Ed25519,
            IdentityAlg::EcdsaP256,
            IdentityAlg::MlDsa65,
            IdentityAlg::Hybrid,
        ] {
            let mut net = CoreNet::new(10 * MS);
            net.capture = true;
            let (a, b) = (net.add(1), net.add_with_alg(2, alg));
            let from = net.nodes[a].addr;
            let first_type = |net: &CoreNet| {
                net.captured
                    .iter()
                    .rev()
                    .find(|(f, _, d)| *f == from && message_type(d).is_some_and(|m| matches!(m, 1 | 2)))
                    .and_then(|(_, _, d)| message_type(d))
            };
            let t0 = net.now;
            let (sa, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
            assert_eq!(first_type(&net), Some(1));
            assert!(
                net.now - t0 < 100 * MS,
                "{alg:?} full Initial: connected at {} ms",
                (net.now - t0) / MS
            );
            // The short Initial to a larger identity is padded across datagrams, and its padding-only datagram names
            // no session, so the responder's budget does not count it: only the short Initial that fits one
            // datagram is checked here.
            if !matches!(alg, IdentityAlg::Ed25519 | IdentityAlg::EcdsaP256) {
                continue;
            }
            // A second dial without a ticket, to a peer known to hold the prekey: the short Initial.
            net.run_for(SEC_NS);
            let t = net.now;
            net.nodes[a].cmd(t, Command::Close { session: sa, error: 0 }).unwrap();
            net.run_for(SEC_NS);
            let (peer, now) = (net.nodes[b].node, net.now);
            while net.nodes[a].ep.tickets().take(&peer, ALPN_A, now).is_some() {}
            let t0 = net.now;
            net.connect_pair(a, b, ALPN_A, Role::Other);
            assert_eq!(first_type(&net), Some(2));
            assert!(
                net.now - t0 < 100 * MS,
                "{alg:?} short Initial: connected at {} ms",
                (net.now - t0) / MS
            );
        }
    });
}
