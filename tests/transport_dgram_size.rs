//! No datagram leaves larger than its path's datagram size, except the two the rules build larger on purpose: a first
//! flight sent whole (up to 1452 bytes, with nothing behind it) and a path MTU probe. Before
//! [#554](https://github.com/sourcenetwork/pinc/issues/554) the packet coalesced behind a whole flight filled the room
//! the flight was given, up to 1452 bytes on a 1200-byte path.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

use std::cell::RefCell;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::MIN_MTU;
use pinc_transport::packet::{LongHeader, LongType};

pinc_tests::install_counting_allocator!();

type Log = Rc<RefCell<Vec<(bool, Vec<u8>)>>>;

/// The bytes behind a datagram's leading handshake packet, or `None` when it does not start with one.
fn behind_handshake(d: &[u8]) -> Option<&[u8]> {
    let (h, at) = LongHeader::parse(d).ok()?;
    (h.ty == LongType::Handshake).then(|| &d[at + h.body_len..])
}

/// Every datagram of a resumed dial, each side sending its first flight whole and probing no larger size: the client
/// writes a request of `len` bytes before the dial, so its early data waits behind the Hello, and the responder answers
/// with `len` bytes as soon as the request is whole. `(sent by the client, datagram)`.
fn resumed_exchange(len: usize) -> Vec<(bool, Vec<u8>)> {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.flight_split = true;
    w.cfg.probe_mtu = false;
    let mut tickets = first_session(&mut w);
    let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let a = w.client(&mut sa, Some(ticket), pinc_security::ClientTickets::new());
    let b = w.server(&mut sb);
    let mut net = Net::new(a, b, Link::new(7, Params::new(10 * MS)), &mut w.stores);
    let log: Log = Rc::default();
    let sink = log.clone();
    net.on_tx = Some(Box::new(move |is_a, d, _| sink.borrow_mut().push((is_a, d.to_vec()))));
    let id = net.a.open_bi().unwrap();
    net.a.write(id, &vec![1; len]).unwrap();
    net.a.conn.finish(id).unwrap();
    let mut answered = false;
    let done = net.run(net.now + 10 * SEC, |n| {
        if !answered && n.b.fin.contains(&id) {
            n.b.write(id, &vec![2; len]).unwrap();
            n.b.conn.finish(id).unwrap();
            answered = true;
        }
        n.a.fin.contains(&id)
    });
    assert!(done, "no answer: {:?}", net.rx_drops);
    assert_eq!((net.a.read[&id].len(), net.b.read[&id].len()), (len, len));
    log.borrow().clone()
}

#[test]
fn nothing_rides_behind_a_whole_flight_past_the_path_datagram_size() {
    big_stack(|| {
        let sent = resumed_exchange(4000);
        let path = usize::from(MIN_MTU);
        // The early data did ride behind the Hello: the case is exercised.
        let coalesced = sent
            .iter()
            .filter(|(is_a, d)| *is_a && behind_handshake(d).is_some_and(|t| t.iter().any(|b| *b != 0)))
            .count();
        assert_ne!(coalesced, 0, "no early data behind the Hello");
        for (is_a, d) in &sent {
            if d.len() <= path {
                continue;
            }
            // Above the path's size only a whole flight goes, and nothing but padding follows it.
            let tail = behind_handshake(d);
            assert!(
                tail.is_some_and(|t| t.iter().all(|b| *b == 0)),
                "a {}-byte datagram from {} on a {path}-byte path carries more than a whole flight",
                d.len(),
                if *is_a { "the client" } else { "the responder" }
            );
        }
    });
}
