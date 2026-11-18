//! The connection's event queue never loses an event the application cannot recover, whatever one packet carries:
//! packets packed with stream-opening, reset, ready, ticket, sleep, path and datagram frames are handed to a connected
//! server without the application polling in between.
#![allow(
    clippy::many_single_char_names,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

use std::collections::HashSet;

use pinc_crypto::IdentityAlg;
use pinc_security::{TicketBatch, TicketEntry};
use pinc_tests::*;
use pinc_transport::conn::{Drop, Event, PathId};
use pinc_transport::frame::Frame;
use pinc_wire::Writer;
use proptest::prelude::*;

#[derive(Debug, Clone)]
enum F {
    Reset(u64),
    OpenStream(u64),
    Ready,
    Tickets,
    Sleep,
    Wake,
    Datagram,
    PathResponse(u8),
    Ext,
}

fn frames() -> impl Strategy<Value = Vec<Vec<F>>> {
    // Client-initiated bidirectional ids are multiples of 4, unidirectional ones are 2 mod 4.
    let id = (0..24u64, any::<bool>()).prop_map(|(k, uni)| 4 * k + if uni { 2 } else { 0 });
    let f = prop_oneof![
        6 => id.clone().prop_map(F::Reset),
        6 => id.clone().prop_map(F::OpenStream),
        3 => Just(F::Ready),
        2 => Just(F::Tickets),
        1 => Just(F::Sleep),
        1 => Just(F::Wake),
        1 => Just(F::Datagram),
        2 => any::<u8>().prop_map(F::PathResponse),
        1 => Just(F::Ext),
    ];
    prop::collection::vec(prop::collection::vec(f, 1..2200), 1..6)
}

fn encode(fs: &[F], buf: &mut [u8]) -> usize {
    let mut w = Writer::new(buf);
    let mut ticket = TicketBatch::new();
    ticket.push(TicketEntry {
        tid: [3; 16],
        lifetime_s: 60,
    });
    for f in fs {
        let frame = match f {
            F::Reset(id) => Frame::ResetStream {
                id: *id,
                error: 1,
                final_size: 0,
            },
            F::OpenStream(id) => Frame::Stream {
                id: *id,
                offset: 0,
                fin: true,
                data: &[],
                implicit_len: false,
            },
            F::Ready => Frame::Ready,
            F::Tickets => Frame::NewTickets(ticket),
            F::Sleep => Frame::Sleep,
            F::Wake => Frame::Wake,
            F::Datagram => Frame::Datagram {
                data: &[],
                implicit_len: false,
            },
            F::PathResponse(b) => Frame::PathResponse([*b; 8]),
            F::Ext => Frame::Extension { ty: 0x41, body: &[] },
        };
        if frame.write(&mut w).is_err() {
            break;
        }
    }
    w.written().len()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]
    #[test]
    fn a_packet_cannot_push_an_unrecoverable_event_out_of_the_queue(packets in frames(), seed in 0..3u64) {
        let ok = big_stack(move || {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::with_chunks(false, 20_000));
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(40 + seed, Params::new(5 * MS)));
            assert!(net.connect(net.now + 10 * SEC));
            let t = net.now + SEC;
            net.run(t, |_| false);
            // Everything the handshake queued is read first, so the queue starts empty.
            while net.b.conn.poll_event().is_some() {}
            let now = net.now;
            for (k, fs) in packets.iter().enumerate() {
                let mut buf = vec![0u8; 9000];
                let n = encode(fs, &mut buf);
                let _ = net.b.with_lent(now, |c, env, l| c.inject_payload(env, l, PathId(1), now, 5000 + k as u64, &buf[..n]));
            }
            let lost = net.b.conn.stats().events_lost;
            let (mut opened, mut reset) = (HashSet::new(), HashSet::new());
            let mut dup = false;
            while let Some(ev) = net.b.conn.poll_event() {
                match ev {
                    Event::StreamOpened(id) => dup |= !opened.insert(id),
                    Event::StreamReset { id, .. } => dup |= !reset.insert(id),
                    _ => {}
                }
            }
            lost == 0 && !dup
        });
        prop_assert!(ok, "an unrecoverable event was lost or repeated");
    }
}

fn gated_pair(f: impl FnOnce(&mut Net<'_, '_, RING>) + Send + 'static) {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::with_chunks(false, 20_000));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        let t = net.now + SEC;
        net.run(t, |_| false);
        f(&mut net);
    });
}

#[test]
fn a_gated_connection_refuses_data_unacknowledged_and_takes_it_when_the_gate_opens() {
    gated_pair(|net| {
        net.b.conn.set_gated(true);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"hello").unwrap();
        net.a.conn.finish(id).unwrap();
        let t = net.now + 2 * SEC;
        net.run(t, |_| false);
        assert!(net.rx_drops.contains(&(false, Drop::Gated)), "{:?}", net.rx_drops);
        assert!(
            !net.b.saw(|r| matches!(r, Rec::Opened(_))),
            "an event was raised through the gate"
        );
        net.b.conn.set_gated(false);
        let t = net.now + 5 * SEC;
        assert!(
            net.run(t, |n| n.b.fin.contains(&id)),
            "the peer's retransmission was not accepted"
        );
        assert_eq!(net.b.read[&id], b"hello");
    });
}

#[test]
fn a_gated_connection_still_takes_acknowledgements_and_a_close() {
    gated_pair(|net| {
        // A is gated: B's acknowledgements of A's data (packets with no event frames) still reach it.
        net.a.conn.set_gated(true);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &vec![3u8; 20_000]).unwrap();
        net.a.conn.finish(id).unwrap();
        let t = net.now + 3 * SEC;
        assert!(net.run(t, |n| n.b.fin.contains(&id)));
        let t = net.now + SEC;
        net.run(t, |_| false);
        assert_eq!(
            net.a.conn.recovery().bytes_in_flight(),
            0,
            "the acknowledgements were refused: {:?}",
            net.rx_drops
        );
        // A close from B reaches the gated A.
        let now = net.now;
        net.b.with_lent(now, |c, env, l| c.close(env, l, 0));
        let t = net.now + 2 * SEC;
        net.run(t, |_| false);
        assert!(net.a.conn.is_closed(), "the close was refused by the gate");
    });
}

/// A packet of the given frames injected into B at `pn`; the opened streams B reported, in order.
fn opened_by(net: &mut Net<'_, '_, RING>, pn: u64, frames: &[Frame<'_>]) -> Vec<u64> {
    let mut buf = vec![0u8; 2000];
    let mut w = Writer::new(&mut buf);
    for f in frames {
        f.write(&mut w).unwrap();
    }
    let n = w.written().len();
    let now = net.now;
    net.b
        .with_lent(now, |c, env, l| c.inject_payload(env, l, PathId(1), now, pn, &buf[..n]))
        .unwrap();
    let mut opened = Vec::new();
    while let Some(ev) = net.b.conn.poll_event() {
        if let Event::StreamOpened(id) = ev {
            opened.push(id);
        }
    }
    opened
}

fn data(id: u64) -> Frame<'static> {
    Frame::Stream {
        id,
        offset: 0,
        fin: false,
        data: b"x",
        implicit_len: false,
    }
}

#[test]
fn a_stream_that_arrives_first_opens_every_lower_stream_of_its_kind_with_an_event() {
    gated_pair(|net| {
        while net.b.conn.poll_event().is_some() {}
        // The client opened bidirectional streams 0, 4 and 8 and unidirectional 2, 6 and 10; the last of each kind
        // arrives alone: the earlier ones are opened by it and each is reported once.
        assert_eq!(opened_by(net, 5000, &[data(8)]), [0, 4, 8]);
        assert_eq!(opened_by(net, 5001, &[data(10)]), [2, 6, 10]);
        // A frame for a stream already reported opens nothing, and the next stream is reported alone.
        assert_eq!(opened_by(net, 5002, &[data(4), data(12)]), [12]);
        // A reset opens the streams below it the same way.
        let reset = Frame::ResetStream {
            id: 24,
            error: 5,
            final_size: 0,
        };
        assert_eq!(opened_by(net, 5003, &[reset]), [16, 20, 24]);
        // Out of order within one packet: each id is reported once, in order.
        assert_eq!(opened_by(net, 5004, &[data(22), data(18), data(14)]), [14, 18, 22]);
    });
}

#[test]
fn a_stop_request_resets_the_sender_with_its_code_and_both_sides_hear_it() {
    gated_pair(|net| {
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &vec![7u8; 50_000]).unwrap();
        let t = net.now + SEC;
        net.run(t, |n| n.b.read.get(&id).is_some_and(|d| !d.is_empty()));
        net.b.conn.stop_sending(id, 77).unwrap();
        let t = net.now + 2 * SEC;
        net.run(t, |_| false);
        assert!(
            net.a.saw(|r| matches!(r, Rec::Stopped(i, 77) if *i == id)),
            "the writer did not hear the stop"
        );
        assert!(
            net.b.saw(|r| matches!(r, Rec::Reset(i, 77) if *i == id)),
            "the stopper did not see the reset"
        );
        assert_eq!(net.a.log.iter().filter(|r| matches!(r, Rec::Stopped(..))).count(), 1);
        assert!(net.a.conn.write(id, b"more").is_err(), "a stopped stream took a write");
    });
}

#[test]
fn a_lost_stop_request_is_sent_again_and_a_stop_for_an_ended_stream_is_ignored() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Params::new(5 * MS);
        link.loss_ppm = 400_000;
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(11, link));
        assert!(net.connect(net.now + 30 * SEC));
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &vec![7u8; 20_000]).unwrap();
        let t = net.now + 5 * SEC;
        net.run(t, |n| n.b.read.get(&id).is_some_and(|d| !d.is_empty()));
        net.b.conn.stop_sending(id, 9).unwrap();
        let t = net.now + 30 * SEC;
        assert!(
            net.run(t, |n| n.a.saw(|r| matches!(r, Rec::Stopped(i, 9) if *i == id))),
            "the stop never arrived over a lossy link"
        );
        // A stop request for a stream the peer already finished sends nothing and fails nothing.
        let id2 = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id2, b"done").unwrap();
        net.a.conn.finish(id2).unwrap();
        let t = net.now + 30 * SEC;
        assert!(net.run(t, |n| n.b.fin.contains(&id2)));
        // The stream may already be gone (read to its end): either answer is fine, and nothing reaches the sender.
        let _ = net.b.conn.stop_sending(id2, 1);
        let t = net.now + SEC;
        net.run(t, |_| false);
        assert!(!net.a.saw(|r| matches!(r, Rec::Stopped(i, 1) if *i == id2)));
    });
}

#[test]
fn a_stop_request_for_a_stream_the_peer_cannot_send_on_is_a_violation() {
    gated_pair(|net| {
        while net.b.conn.poll_event().is_some() {}
        let stop = Frame::StopSending { id: 2, error: 1 };
        let mut buf = vec![0u8; 64];
        let mut w = Writer::new(&mut buf);
        stop.write(&mut w).unwrap();
        let n = w.written().len();
        let now = net.now;
        // Id 2 is a client-initiated unidirectional stream: B, the server, has no send half on it.
        let r = net.b.with_lent(now, |c, env, l| {
            c.inject_payload(env, l, PathId(1), now, 6000, &buf[..n])
        });
        assert_eq!(r, Err(Drop::Closed));
    });
}

/// The connection's statistics show the stream layer's range counters: a peer stream whose received ranges outgrow the
/// inline array moves them into a slot of the endpoint's arena, once.
#[test]
fn the_connection_statistics_count_a_stream_range_spill() {
    gated_pair(|net| {
        net.b.spill = pinc_transport::stream::spill::SpillArena::new_boxed(2);
        while net.b.conn.poll_event().is_some() {}
        let stats = net.b.conn.stats();
        assert_eq!((stats.range_spills, stats.range_overflows), (0, 0));
        // One-byte frames at every 20th offset leave 100 holes, past the 96 ranges kept inline.
        let frames: Vec<Frame<'_>> = (0..100u64)
            .map(|k| Frame::Stream {
                id: 0,
                offset: 20 * k + 10,
                fin: false,
                data: b"x",
                implicit_len: false,
            })
            .collect();
        opened_by(net, 5000, &frames);
        let stats = net.b.conn.stats();
        assert_eq!((stats.range_spills, stats.range_overflows), (1, 0));
    });
}
