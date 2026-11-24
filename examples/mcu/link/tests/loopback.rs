//! The two ends of the line in one process, on virtual time: the table sizes of the small endpoint carry a handshake
//! and an echo, and the framing carries every datagram.
#![allow(missing_docs, clippy::unwrap_used, clippy::print_stderr, clippy::too_many_lines)]

use std::collections::VecDeque;
use std::mem::size_of;

use pinc_core::{Command, Event, Role, Value};
use pinc_mcu_link::app::Echo;
use pinc_mcu_link::frame::{Deframer, encode, encoded_max};
use pinc_mcu_link::{
    ALPN, BOARD_ADDR, Ep, EpPlace, EpSlot, EpStreams, MTU, Memory, Node, PEER_ADDR, SlotTable, node_id,
};

const MS: u64 = 1_000_000;

fn leak<T>(v: T) -> &'static mut T {
    Box::leak(Box::new(v))
}

/// Send everything `node` has into `line`, framed.
fn flush(node: &mut Node<'_, '_, '_>, now: u64, line: &mut VecDeque<u8>) {
    let mut out = [0u8; 2048];
    let mut framed = [0u8; encoded_max(2048)];
    while let Some(t) = node.ep.poll_transmit(now, &mut out) {
        assert!(t.len <= usize::from(MTU));
        let n = encode(&out[..t.len], &mut framed).unwrap();
        line.extend(&framed[..n]);
    }
}

#[test]
fn a_handshake_and_an_echo_between_the_two_ends() {
    eprintln!(
        "sizes on this host: endpoint {} B, slot {} B, streams {} B, memory {} B",
        size_of::<Ep>(),
        size_of::<EpSlot>(),
        size_of::<EpStreams>(),
        size_of::<Memory>()
    );
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(run)
        .unwrap()
        .join()
        .unwrap();
}

fn run() {
    let (board_seed, peer_seed) = ([7u8; 32], [9u8; 32]);
    let mut now = 1_000 * MS;
    let mut board = Node::new(
        now,
        &board_seed,
        BOARD_ADDR,
        leak(Memory::new()),
        leak(SlotTable::uninit()),
        leak(EpPlace::uninit()),
    )
    .unwrap();
    let mut peer = Node::new(
        now,
        &peer_seed,
        PEER_ADDR,
        leak(Memory::new()),
        leak(SlotTable::uninit()),
        leak(EpPlace::uninit()),
    )
    .unwrap();
    let mut echo = Echo::new();
    let (mut to_board, mut to_peer) = (VecDeque::new(), VecDeque::new());
    let (mut board_in, mut peer_in) = (Deframer::<2048>::new(), Deframer::<2048>::new());

    let payload: Vec<u8> = (0..40_000u32).map(|i| (i % 251) as u8).collect();
    let Value::Session(session) = peer
        .command(
            now,
            Command::Connect {
                node: node_id(&board_seed).unwrap(),
                alpn: ALPN,
                addrs: &[BOARD_ADDR],
                role: Role::Other,
            },
        )
        .unwrap()
    else {
        panic!("no session")
    };
    let (mut stream, mut sent, mut back, mut done) = (None, 0, Vec::new(), false);
    for _ in 0..200_000 {
        // The peer's application.
        while let Some(ev) = peer.next_event(now) {
            match ev {
                Event::Connected { .. } => {
                    let Value::Stream(id) = peer.command(now, Command::OpenStream { session, bidi: true }).unwrap()
                    else {
                        panic!("no stream")
                    };
                    stream = Some(id);
                }
                Event::StreamReadable { stream, .. } => loop {
                    let mut buf = [0u8; 4096];
                    let (n, ended) = peer.read(now, session, stream, &mut buf);
                    back.extend_from_slice(&buf[..n]);
                    done |= ended;
                    if n == 0 {
                        break;
                    }
                },
                Event::ConnectFailed { reason, .. } => panic!("dial failed: {reason:?}"),
                _ => {}
            }
        }
        if let Some(stream) = stream
            && sent < payload.len()
        {
            if let Ok(Value::Written(w)) = peer.command(
                now,
                Command::Write {
                    session,
                    stream,
                    data: &payload[sent..],
                },
            ) {
                sent += w;
            }
            if sent == payload.len() {
                peer.command(now, Command::Finish { session, stream }).unwrap();
            }
        }
        while let Some(ev) = board.next_event(now) {
            echo.on_event(&mut board, now, &ev);
        }
        flush(&mut peer, now, &mut to_board);
        flush(&mut board, now, &mut to_peer);
        if done {
            break;
        }
        // The line: every byte arrives 1 ms later, in order.
        now += MS;
        while let Some(b) = to_board.pop_front() {
            if let Some(d) = board_in.push(b) {
                board.ep.handle_datagram(now, BOARD_ADDR, PEER_ADDR, d);
            }
        }
        while let Some(b) = to_peer.pop_front() {
            if let Some(d) = peer_in.push(b) {
                peer.ep.handle_datagram(now, PEER_ADDR, BOARD_ADDR, d);
            }
        }
        for node in [&mut board, &mut peer] {
            if node.ep.poll_timeout().is_some_and(|t| t <= now) {
                node.ep.handle_timeout(now);
            }
        }
    }
    assert!(
        done,
        "the echo did not end: {} of {} bytes back",
        back.len(),
        payload.len()
    );
    assert_eq!(back, payload);
    assert_eq!(echo.bytes, payload.len() as u64);
}
