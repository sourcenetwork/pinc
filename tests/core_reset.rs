//! Stateless reset: a peer that restarted on the same address and identity ends the sessions a node still holds to it,
//! and the sub-sessions over them, within one round trip of the node's first packet after the restart, and the next
//! dial reaches the new peer; a forged, replayed or untimely reset ends nothing; a reset never amplifies; a peer that
//! stays down ends the held session as it did before.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use std::net::SocketAddr;

use vinc_core::{Command, EndReason, Event, Role, SessionId, Value};
use vinc_tests::*;
use vinc_transport::conn::CloseReason;

const KEY_A: [u8; 32] = [0xa1; 32];
const KEY_B: [u8; 32] = [0xb2; 32];
/// One way; a round trip is twice this.
const DELAY: u64 = 10 * MS_NS;
const RESET_LEN: usize = 21;

fn dial(net: &mut CoreNet, a: usize, b: usize, alpn: &[u8]) -> (SessionId, vinc_core::Reply) {
    let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(now, peer, alpn, to, Role::Other).unwrap();
    (net.nodes[a].session(&rep), rep)
}

fn write_new(net: &mut CoreNet, n: usize, s: SessionId, data: &[u8]) {
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
}

fn read_by(net: &mut CoreNet, n: usize, data: &[u8]) -> bool {
    let t = net.now;
    net.run(t + 5 * SEC_NS, |k| k.nodes[n].read.values().any(|v| v == data))
}

fn closed_at(n: &TNode, s: SessionId) -> Option<(u64, EndReason)> {
    n.events.iter().find_map(|(t, e)| match e {
        Event::Closed { session, reason } if *session == s => Some((*t, *reason)),
        _ => None,
    })
}

fn is_reset(d: &[u8]) -> bool {
    d.len() == RESET_LEN && d[0] & 0xe0 == 0x60
}

/// Node `a` holds a session to `b` and a sub-session over it, both used, then idle for a second.
fn held(net: &mut CoreNet, key_a: Option<[u8; 32]>, key_b: Option<[u8; 32]>) -> (usize, usize, SessionId, SessionId) {
    let a = net.add_resetting(1, key_a);
    let b = net.add_resetting(2, key_b);
    let (parent, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
    write_new(net, a, parent, b"parent");
    assert!(read_by(net, b, b"parent"));
    let (child, _) = dial(net, a, b, ALPN_B);
    write_new(net, a, child, b"child");
    assert!(read_by(net, b, b"child"));
    net.run_for(SEC_NS);
    (a, b, parent, child)
}

/// The destination id of the last short-header datagram `from` sent `to`.
fn last_dcid(net: &CoreNet, from: SocketAddr, to: SocketAddr) -> Vec<u8> {
    net.captured
        .iter()
        .rev()
        .find(|(f, t, d)| *f == from && *t == to && d[0] & 0xe0 == 0x40)
        .map(|(_, _, d)| d[1..5].to_vec())
        .unwrap()
}

/// The token `key` gives id `cid` used by a peer at `remote`, as `vinc-core` computes it.
fn token(key: &[u8; 32], cid: &[u8], remote: SocketAddr) -> Vec<u8> {
    let ip = match remote.ip() {
        std::net::IpAddr::V4(v) => v.to_ipv6_mapped().octets(),
        std::net::IpAddr::V6(v) => v.octets(),
    };
    let mut input = cid.to_vec();
    input.extend_from_slice(&ip);
    input.extend_from_slice(&remote.port().to_be_bytes());
    vinc_crypto::extract(key, &input)[..16].to_vec()
}

fn reset(cid: &[u8], tok: &[u8]) -> Vec<u8> {
    let mut r = vec![0x60];
    r.extend_from_slice(cid);
    r.extend_from_slice(tok);
    r
}

#[test]
fn a_restarted_peer_ends_the_held_session_and_its_sub_sessions_within_one_round_trip() {
    big_stack(|| {
        let mut net = CoreNet::new(DELAY);
        let (a, b, parent, child) = held(&mut net, Some(KEY_A), Some(KEY_B));
        net.restart(b, 2, Some(KEY_B), 1);
        let (sent0, b_addr) = (net.nodes[a].sent.len(), net.nodes[b].addr);
        // The application dials the peer again: the dial still rides the held session, reported at once.
        let (redial, rep) = dial(&mut net, a, b, ALPN_B);
        assert!(
            rep.events.any(|e| matches!(e, Event::Connected { .. })),
            "the sub-session was not reported at once"
        );
        write_new(&mut net, a, redial, b"after");
        let t = net.now;
        assert!(net.run(t + 5 * SEC_NS, |n| closed_at(&n.nodes[a], parent).is_some()));
        let first = net.nodes[a].sent[sent0..]
            .iter()
            .find(|(_, to, _)| *to == b_addr)
            .map(|(t, ..)| *t)
            .unwrap();
        for s in [parent, child, redial] {
            let (at, why) = closed_at(&net.nodes[a], s).unwrap_or_else(|| panic!("{s:?} is still up"));
            assert!(
                at <= first + 2 * DELAY + MS_NS,
                "{s:?} closed {} us after a's first packet; a round trip is {} us",
                (at - first) / 1000,
                2 * DELAY / 1000
            );
            assert_eq!(why, EndReason::Transport(CloseReason::Reset), "{s:?}");
        }
        let (fresh, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        write_new(&mut net, a, fresh, b"again");
        assert!(
            read_by(&mut net, b, b"again"),
            "the next dial did not reach the restarted peer"
        );
    });
}

#[test]
fn a_forged_reset_ends_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(DELAY);
        net.capture = true;
        let (a, b, parent, child) = held(&mut net, Some(KEY_A), Some(KEY_B));
        let (a_addr, b_addr) = (net.nodes[a].addr, net.nodes[b].addr);
        let cid = last_dcid(&net, a_addr, b_addr);
        let good = token(&KEY_B, &cid, a_addr);
        let mut bad = good.clone();
        bad[15] ^= 1;
        // The right id with a token one bit off, a token made with another key, and the right token for another id.
        net.inject(b_addr, a_addr, reset(&cid, &bad), 0);
        net.inject(b_addr, a_addr, reset(&cid, &token(&KEY_A, &cid, a_addr)), 0);
        net.inject(b_addr, a_addr, reset(&[9, 9, 9, 9], &good), 0);
        net.run_for(SEC_NS);
        assert!(closed_at(&net.nodes[a], parent).is_none() && closed_at(&net.nodes[a], child).is_none());
        write_new(&mut net, a, child, b"still up");
        assert!(read_by(&mut net, b, b"still up"));
        // The genuine reset, sent the same way, does end the session: the forgeries failed on their tokens alone.
        net.run_for(SEC_NS);
        net.inject(b_addr, a_addr, reset(&cid, &good), 0);
        net.run_for(SEC_NS);
        assert!(closed_at(&net.nodes[a], parent).is_some() || closed_at(&net.nodes[a], child).is_some());
    });
}

#[test]
fn a_replayed_reset_ends_nothing() {
    big_stack(|| {
        let mut net = CoreNet::new(DELAY);
        net.capture = true;
        let (a, b, parent, _child) = held(&mut net, Some(KEY_A), Some(KEY_B));
        let (a_addr, b_addr) = (net.nodes[a].addr, net.nodes[b].addr);
        net.restart(b, 2, Some(KEY_B), 1);
        write_new(&mut net, a, parent, b"after");
        let t = net.now;
        assert!(net.run(t + 5 * SEC_NS, |n| closed_at(&n.nodes[a], parent).is_some()));
        let resets: Vec<Vec<u8>> = net
            .captured
            .iter()
            .filter(|(f, t, d)| *f == b_addr && *t == a_addr && is_reset(d))
            .map(|(_, _, d)| d.clone())
            .collect();
        assert!(!resets.is_empty(), "the restarted peer sent no reset");
        let (fresh, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
        write_new(&mut net, a, fresh, b"fresh");
        assert!(read_by(&mut net, b, b"fresh"));
        net.run_for(SEC_NS);
        for r in &resets {
            net.inject(b_addr, a_addr, r.clone(), 0);
        }
        net.run_for(SEC_NS);
        assert!(
            closed_at(&net.nodes[a], fresh).is_none(),
            "a replayed reset ended the new session"
        );
        write_new(&mut net, a, fresh, b"fresh still");
        assert!(read_by(&mut net, b, b"fresh still"));
    });
}

#[test]
fn a_reset_with_the_right_token_is_ignored_while_the_peer_is_heard() {
    big_stack(|| {
        let mut net = CoreNet::new(DELAY);
        net.capture = true;
        let (a, b, parent, _child) = held(&mut net, Some(KEY_A), Some(KEY_B));
        let (a_addr, b_addr) = (net.nodes[a].addr, net.nodes[b].addr);
        let cid = last_dcid(&net, a_addr, b_addr);
        let good = reset(&cid, &token(&KEY_B, &cid, a_addr));
        // A stray reset lands just after an answer of the live peer: within a round trip of it, it is not believed.
        write_new(&mut net, a, parent, b"ping");
        let before = net.tapped.len();
        let t = net.now;
        assert!(net.run(t + 5 * SEC_NS, |n| {
            n.tapped[before..]
                .iter()
                .any(|(_, f, to, _)| *f == b_addr && *to == a_addr)
        }));
        net.inject(b_addr, a_addr, good, DELAY + 1_000);
        net.run_for(SEC_NS);
        assert!(
            closed_at(&net.nodes[a], parent).is_none(),
            "a reset within a round trip of hearing the peer ended it"
        );
    });
}

#[test]
fn a_reset_never_amplifies() {
    big_stack(|| {
        let mut net = CoreNet::new(DELAY);
        let b = net.add_resetting(2, Some(KEY_B));
        let b_addr = net.nodes[b].addr;
        // A spoofed source: no node is there.
        let x: SocketAddr = ([10, 0, 0, 9], 4433).into();
        let short = |len: usize| {
            let mut d = vec![0x40; len];
            d[1..5].copy_from_slice(&[9, 9, 9, 9]);
            d
        };
        let to_x = |net: &CoreNet| {
            net.nodes[b]
                .sent
                .iter()
                .filter(|(_, to, _)| *to == x)
                .map(|(.., n)| *n)
                .collect::<Vec<_>>()
        };
        net.inject(x, b_addr, short(RESET_LEN), 0);
        net.run_for(100 * MS_NS);
        assert!(to_x(&net).is_empty(), "a datagram no longer than a reset was answered");
        net.inject(x, b_addr, short(RESET_LEN + 1), 0);
        net.run_for(100 * MS_NS);
        assert_eq!(
            to_x(&net),
            vec![RESET_LEN],
            "one reset of 21 bytes answers a longer datagram"
        );
        net.inject(x, b_addr, reset(&[9, 9, 9, 9], &[0; 16]), 0);
        net.run_for(100 * MS_NS);
        assert_eq!(to_x(&net).len(), 1, "a reset was answered");
        // A burst that arrives at once gets one reset: at most one waits to be sent.
        for _ in 0..100 {
            net.inject(x, b_addr, short(1200), 0);
        }
        net.run_for(100 * MS_NS);
        let sent = to_x(&net);
        assert_eq!(sent.len(), 2, "a burst of 100 got {} resets", sent.len() - 1);
        assert!(sent.iter().all(|n| *n == RESET_LEN));
    });
}

#[test]
fn a_peer_that_stays_down_ends_the_held_session_as_without_resets() {
    let end = |keys: bool| {
        big_stack(move || {
            let (ka, kb) = if keys { (Some(KEY_A), Some(KEY_B)) } else { (None, None) };
            let mut net = CoreNet::new(DELAY);
            let (a, b, parent, child) = held(&mut net, ka, kb);
            net.stop(b, 2);
            let t = net.now;
            write_new(&mut net, a, child, b"into the void");
            assert!(net.run(t + 200 * SEC_NS, |n| closed_at(&n.nodes[a], parent).is_some()));
            let (at, why) = closed_at(&net.nodes[a], parent).unwrap();
            (at - t, why)
        })
    };
    let (with, without) = (end(true), end(false));
    assert_eq!(with.1, without.1, "the held session ends for another reason");
    assert_ne!(with.1, EndReason::Transport(CloseReason::Reset));
    assert!(
        with.0.abs_diff(without.0) <= 100 * MS_NS,
        "with resets {with:?}, without {without:?}"
    );
}
