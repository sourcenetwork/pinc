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

use proptest::prelude::*;
use vinc_crypto::IdentityAlg;
use vinc_security::{TicketBatch, TicketEntry};
use vinc_tests::*;
use vinc_transport::conn::{Drop, Event, PathId};
use vinc_transport::frame::Frame;
use vinc_wire::Writer;

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
                let _ = net.b.with_env(now, |c, env| c.inject_payload(env, PathId(1), now, 5000 + k as u64, &buf[..n]));
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
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
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
        net.b.with_env(now, |c, env| c.close(env, 0));
        let t = net.now + 2 * SEC;
        net.run(t, |_| false);
        assert!(net.a.conn.is_closed(), "the close was refused by the gate");
    });
}
