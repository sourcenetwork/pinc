//! Received datagrams are readable: copied into the caller's buffer in arrival order, a too-small buffer leaves the
//! datagram queued, and the bounded receive queue drops the oldest and counts it.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use pinc_core::{Answer, Command, CommandError, Event, Query, Role, SessionId};
use pinc_tests::*;

const D: u64 = 5 * MS_NS;

fn pair() -> (CoreNet, usize, usize, SessionId, SessionId) {
    let mut net = CoreNet::new(D);
    let (a, b) = (net.add(1), net.add(2));
    let (sa, sb) = net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    (net, a, b, sa, sb)
}

fn send(net: &mut CoreNet, a: usize, sa: SessionId, data: &[u8]) {
    let t = net.now;
    net.nodes[a]
        .cmd(t, Command::SendDatagram { session: sa, data })
        .unwrap();
    net.run_for(MS_NS);
}

fn read_all(net: &mut CoreNet, b: usize, sb: SessionId) -> Vec<Vec<u8>> {
    let mut out = Vec::new();
    let mut buf = [0u8; 1500];
    while let Some(n) = net.nodes[b].ep.read_datagram(sb, &mut buf).unwrap() {
        out.push(buf[..n].to_vec());
    }
    out
}

#[test]
fn datagrams_read_end_to_end_in_arrival_order() {
    big_stack(|| {
        let (mut net, a, b, sa, sb) = pair();
        for i in 0..20u32 {
            send(&mut net, a, sa, &i.to_be_bytes());
        }
        net.run_for(SEC_NS);
        assert_eq!(net.nodes[b].count(|e| matches!(e, Event::DatagramReceived { .. })), 20);
        let got = read_all(&mut net, b, sb);
        let want: Vec<Vec<u8>> = (0..20u32).map(|i| i.to_be_bytes().to_vec()).collect();
        assert_eq!(got, want);
        let mut buf = [0u8; 8];
        assert_eq!(net.nodes[b].ep.read_datagram(sb, &mut buf), Ok(None));
    });
}

#[test]
fn a_buffer_that_is_too_small_leaves_the_datagram_queued() {
    big_stack(|| {
        let (mut net, a, b, sa, sb) = pair();
        send(&mut net, a, sa, &[7u8; 50]);
        net.run_for(SEC_NS);
        let mut small = [0u8; 10];
        assert_eq!(
            net.nodes[b].ep.read_datagram(sb, &mut small),
            Err(CommandError::BufferTooSmall { len: 50 })
        );
        let mut buf = [0u8; 50];
        assert_eq!(net.nodes[b].ep.read_datagram(sb, &mut buf), Ok(Some(50)));
        assert_eq!(buf, [7u8; 50]);
        assert_eq!(net.nodes[b].ep.read_datagram(sb, &mut buf), Ok(None));
    });
}

#[test]
fn the_receive_queue_is_bounded_and_the_drops_are_counted() {
    big_stack(|| {
        let (mut net, a, b, sa, sb) = pair();
        for i in 0..300u32 {
            send(&mut net, a, sa, &i.to_be_bytes());
        }
        net.run_for(SEC_NS);
        let got = read_all(&mut net, b, sb);
        assert!(got.len() <= 64, "the queue holds {} datagrams", got.len());
        assert_eq!(
            got.last().unwrap().as_slice(),
            299u32.to_be_bytes(),
            "the newest is kept"
        );
        assert!(got.windows(2).all(|w| w[0] < w[1]), "arrival order");
        let Answer::Stats(st) = net.nodes[b].ep.query(Query::Stats(sb)) else {
            panic!()
        };
        let arrived = net.nodes[b].count(|e| matches!(e, Event::DatagramReceived { .. })) as u64;
        assert_eq!(st.transport.datagrams_dropped_recv + got.len() as u64, arrived);
        assert!(st.transport.datagrams_dropped_recv > 0);
    });
}

#[test]
fn a_session_that_ended_cannot_be_read() {
    big_stack(|| {
        let (mut net, _, b, _, sb) = pair();
        let t = net.now;
        net.nodes[b].cmd(t, Command::Close { session: sb, error: 0 }).unwrap();
        net.run_for(3 * SEC_NS);
        let mut buf = [0u8; 8];
        assert_eq!(
            net.nodes[b].ep.read_datagram(sb, &mut buf),
            Err(CommandError::NoSession)
        );
    });
}
