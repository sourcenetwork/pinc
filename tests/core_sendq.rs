//! The send queue: a session with data waiting stays on it when the buffer of one call leaves it no room.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines
)]

use std::collections::HashSet;

use vinc_core::{Command, Role, SessionId, Transmit, Value};
use vinc_tests::*;

const DATA: usize = 30_000;

fn write_all(net: &mut CoreNet, n: usize, s: SessionId) {
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
        panic!("no stream")
    };
    let data = vec![7u8; DATA];
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data: &data,
            },
        )
        .unwrap();
}

fn poll(net: &mut CoreNet, n: usize, size: usize) -> Option<Transmit> {
    let now = net.now;
    net.nodes[n].ep.poll_transmit(now, &mut vec![0u8; size])
}

/// A node `a` with `peers` connected sessions, each with `DATA` bytes written and nothing sent yet.
fn loaded(peers: u8) -> (CoreNet, usize) {
    let mut net = CoreNet::new(10 * MS_NS);
    let a = net.add(1);
    let sessions: Vec<_> = (2..2 + peers)
        .map(|tag| {
            let b = net.add(tag);
            net.connect_pair(a, b, ALPN_A, Role::Other).0
        })
        .collect();
    net.run_for(SEC_NS);
    for s in sessions {
        write_all(&mut net, a, s);
    }
    (net, a)
}

#[test]
fn a_tight_buffer_after_the_first_datagram_does_not_strand_the_data_of_a_session() {
    big_stack(|| {
        let (mut net, a) = loaded(1);
        let first = poll(&mut net, a, 1455).expect("data waits, a datagram leaves");
        assert_eq!(first.len, first.segment_size, "one datagram");
        let second = poll(&mut net, a, 65_536);
        assert!(second.is_some(), "the session left the queue with {DATA} bytes waiting");
    });
}

#[test]
fn the_same_two_calls_with_a_large_buffer_both_send() {
    big_stack(|| {
        let (mut net, a) = loaded(1);
        assert!(poll(&mut net, a, 65_536).is_some());
        assert!(poll(&mut net, a, 65_536).is_some());
    });
}

#[test]
fn a_tight_buffer_keeps_every_session_with_data_on_the_queue() {
    big_stack(|| {
        let (mut net, a) = loaded(2);
        let (b, c) = (net.nodes[1].addr, net.nodes[2].addr);
        assert!(poll(&mut net, a, 1455).is_some());
        let mut seen = HashSet::new();
        for _ in 0..200 {
            let Some(t) = poll(&mut net, a, 65_536) else { break };
            seen.insert(t.remote);
        }
        assert!(
            seen.contains(&b) && seen.contains(&c),
            "a session with data waiting was dropped from the queue: sent to {seen:?}"
        );
    });
}
