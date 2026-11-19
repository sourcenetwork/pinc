//! The lifecycle of the PINCER connection: idle and keepalive, one close, the give-up, sleep and wake, link
//! outages, amplification limits, early packets, tail repair, connection ids, memory bounds and hostile input.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::manual_assert_eq, // a failing comparison of megabytes must not print them
    clippy::cast_precision_loss,
    clippy::large_stack_arrays
)]

use std::cell::RefCell;
use std::rc::Rc;

use proptest::prelude::*;
use pinc_crypto::IdentityAlg;
use pinc_security::Env;
use pinc_tests::*;
use pinc_transport::conn::{CloseReason, PathId, PathInfo};
use pinc_transport::packet::LongHeader;

pinc_tests::install_counting_allocator!();

fn connected<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, link: Link) -> Net<'a, 'a> {
    let mut net = setup(w, sa, sb, link);
    assert!(net.connect(net.now + 30 * SEC), "{:?}", net.rx_drops);
    net
}

#[test]
fn idle_timeout_closes_silently() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(1, Params::new(10 * MS)));
        let start = net.now;
        assert!(net.run(start + 100 * SEC, |n| n.a.closed().is_some() && n.b.closed().is_some()));
        assert_eq!(net.a.closed(), Some(CloseReason::IdleTimeout));
        assert_eq!(net.b.closed(), Some(CloseReason::IdleTimeout));
        let last = net.a.tx_log.last().unwrap().0.max(net.b.tx_log.last().unwrap().0);
        assert!(
            last < start + 5 * SEC,
            "no packet announces the idle close: last send at +{} ms",
            (last - start) / MS
        );
        assert!(net.a.conn.is_closed() && net.b.conn.is_closed());
    });
}

#[test]
fn keepalive_holds_a_quiet_connection_open() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(2, Params::new(10 * MS)));
        net.a.conn.set_keepalive(Some(20 * SEC));
        net.run(net.now + 300 * SEC, |_| false);
        assert!(
            net.a.closed().is_none() && net.b.closed().is_none(),
            "{:?} {:?}",
            net.a.closed(),
            net.b.closed()
        );
        assert!(net.a.conn.is_connected() && net.b.conn.is_connected());
        let pings = net.a.tx_log.iter().filter(|t| t.0 > T0 + 10 * SEC).count();
        assert!(
            (10..=40).contains(&pings),
            "about one packet per keepalive interval, got {pings}"
        );
    });
}

#[test]
fn one_close_then_the_state_is_freed() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(3, Params::new(10 * MS)));
        net.run(net.now + SEC, |_| false);
        let at = net.now;
        net.a.with_env(at, |c, env| c.close(env, 42));
        assert!(net.run(at + 5 * SEC, |n| n.b.closed().is_some()));
        assert_eq!(net.a.closed(), Some(CloseReason::Local { error: 42 }));
        assert_eq!(net.b.closed(), Some(CloseReason::Peer { error: 42 }));
        let (a_sent, b_sent) = (net.a.tx_log.len(), net.b.tx_log.len());
        // Both states are freed at once: no timer, no waiting, nothing sent afterwards.
        assert!(net.a.conn.is_closed() && net.b.conn.is_closed());
        net.run(net.now + 10 * SEC, |_| false);
        assert_eq!(net.b.tx_log.len(), b_sent);
        assert_eq!(net.a.tx_log.len(), a_sent);
        assert!(net.a.conn.poll_timeout().is_none() && net.b.conn.poll_timeout().is_none());
        assert!(net.b.conn.open_bi().is_err());
    });
}

/// A frame held back for want of room must not discard the frames behind it in its packet. The room the held stream
/// waits for only comes back as the stream ahead of it receives its bytes, and those ride behind it in every
/// retransmission.
#[test]
fn a_held_back_stream_does_not_discard_the_frames_behind_it_in_its_packet() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        // A server whose pool holds two windows, one chunk of it taken for good by a stream nobody reads: the second
        // stream fits only once the first has been received whole and read.
        let mut small = pinc_transport::stream::Config::new(false);
        small.initial_stream_window = 64 * 1024;
        small.max_stream_window = 64 * 1024;
        let mut sa = Store::new(true);
        let mut sb = Store::with_stream(8, &small);
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(5, Params::new(10 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        net.b.auto_read = false;
        // The opener ignores the credit the server gave: the held-back rule is the net under test.
        net.a.conn.raise_stream_credit(100);
        let parked = net.a.conn.open_bi().unwrap();
        net.a.conn.write(parked, &[9; 100]).unwrap();
        net.run(net.now + SEC, |_| false);
        let (first, second) = (net.a.conn.open_bi().unwrap(), net.a.conn.open_bi().unwrap());
        // The second stream is served first, so its frame leads the packet that carries the first stream's bytes.
        net.a.conn.set_urgency(second, 0).unwrap();
        let (d1, d2) = (pattern(30_000, 61), pattern(100, 62));
        for (id, d) in [(first, &d1), (second, &d2)] {
            assert_eq!(net.a.conn.write(id, d).unwrap(), d.len());
            net.a.conn.finish(id).unwrap();
        }
        let ok = net.run(net.now + 60 * SEC, |n| {
            n.b.read_stream(n.now, first);
            n.b.read_stream(n.now, second);
            n.b.fin.contains(&first) && n.b.fin.contains(&second)
        });
        assert!(ok, "the streams were not delivered: {:?}", net.b.fin);
        assert!(net.b.read[&first] == d1 && net.b.read[&second] == d2);
        assert!(!net.a.saw(|r| matches!(r, Rec::Reset(..))), "a stream was reset");
    });
}

#[test]
fn a_stream_the_pool_cannot_hold_waits_unacknowledged_and_is_delivered_once_there_is_room() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        // A server whose pool holds the windows of three streams: a fourth stream waits for room, and is never
        // reset or dropped silently.
        let mut small = pinc_transport::stream::Config::new(false);
        small.initial_stream_window = 192 * 1024;
        small.max_stream_window = 192 * 1024;
        let mut sa = Store::new(true);
        let mut sb = Store::with_stream(40, &small);
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(4, Params::new(10 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        net.b.auto_read = false;
        // The opener ignores the credit the server gave: the held-back rule is the net under test.
        net.a.conn.raise_stream_credit(100);
        let ids: Vec<u64> = (0..5).map(|_| net.a.conn.open_bi().unwrap()).collect();
        let data: Vec<Vec<u8>> = (0..5).map(|i| pattern(20_000 + 1_000 * i, 50 + i as u64)).collect();
        for (id, d) in ids.iter().zip(&data) {
            assert_eq!(net.a.conn.write(*id, d).unwrap(), d.len());
            net.a.conn.finish(*id).unwrap();
        }
        // Nothing is read, so the pool stays full: the streams beyond it keep being retried, without a reset.
        net.run(net.now + 3 * SEC, |_| false);
        assert!(!net.a.saw(|r| matches!(r, Rec::Reset(..))), "a stream was reset");
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
        // Reading frees the room, and every stream arrives once, whole and in order.
        net.b.auto_read = true;
        let ok = net.run(net.now + 60 * SEC, |n| {
            for id in &ids {
                n.b.read_stream(n.now, *id);
            }
            ids.iter().all(|id| n.b.fin.contains(id))
        });
        assert!(ok, "not every stream was delivered");
        for (id, d) in ids.iter().zip(&data) {
            assert!(net.b.read[id] == *d, "stream {id} differs");
        }
        assert!(!net.a.saw(|r| matches!(r, Rec::Reset(..))), "a stream was reset");
    });
}

#[test]
fn a_restarted_peer_is_caught_by_the_give_up() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(5, Params::new(10 * MS)));
        net.run(net.now + 2 * SEC, |_| false);
        // The server restarts and forgets the session: nothing it sends comes back, and nothing it answers is valid.
        // From the client this looks like a peer that went silent, and the give-up closes the connection.
        let gone = Params::new(10 * MS).loss(100.0);
        net.link.set(PathId(1), gone, gone);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"anyone there").unwrap();
        let ok = net.run(net.now + 400 * SEC, |n| n.a.closed().is_some());
        assert!(ok, "the client must give up");
        assert_eq!(net.a.closed(), Some(CloseReason::PathDead));
        assert!(net.a.conn.is_closed());
    });
}

/// B sends `size` bytes to A on a new stream; returns the stream id.
fn serve(net: &mut Net<'_, '_>, data: &[u8], off: &mut usize, id: u64) {
    while *off < data.len() {
        let k = net.b.conn.write(id, &data[*off..]).unwrap();
        if k == 0 {
            break;
        }
        *off += k;
    }
}

#[test]
fn sleep_and_wake_resume_a_transfer_without_collapse() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(8, Params::new(10 * MS)));
        let data = pattern(8 << 20, 9);
        let id = net.b.conn.open_bi().unwrap();
        let mut off = 0;
        // The server sends; the client sleeps part way through.
        net.run(net.now + 60 * SEC, |n| {
            serve(n, &data, &mut off, id);
            n.a.read.get(&id).map_or(0, Vec::len) > (2 << 20)
        });
        let cwnd_before = net.b.conn.stats().cwnd;
        let ptos_before = net.b.conn.stats().ptos;
        let now = net.now;
        net.a.with_env(now, pinc_transport::conn::Connection::sleep);
        net.run(now + 50 * MS, |n| {
            serve(n, &data, &mut off, id);
            false
        });
        assert!(net.b.conn.peer_asleep() && net.b.saw(|r| *r == Rec::PeerAsleep));
        net.link.route(PathId(1)).up = false;
        net.run(net.now + 25 * SEC, |n| {
            serve(n, &data, &mut off, id);
            false
        });
        assert_eq!(
            net.b.conn.stats().ptos,
            ptos_before,
            "no probe timeout fires while the peer sleeps"
        );
        assert!(net.b.closed().is_none() && net.a.closed().is_none());
        net.link.route(PathId(1)).up = true;
        let now = net.now;
        net.a.with_env(now, pinc_transport::conn::Connection::wake);
        let mut finished = false;
        let ok = net.run(net.now + 120 * SEC, |n| {
            serve(n, &data, &mut off, id);
            if off == data.len() && !finished {
                n.b.conn.finish(id).unwrap();
                finished = true;
            }
            n.a.fin.contains(&id)
        });
        assert!(ok, "the transfer resumes after the wake");
        assert!(net.a.read[&id] == data);
        assert!(net.b.saw(|r| *r == Rec::PeerAwake));
        assert!(!net.a.saw(|r| *r == Rec::WakeUnanswered));
        let after = net.b.conn.stats();
        assert!(after.ptos <= ptos_before + 2, "{} -> {}", ptos_before, after.ptos);
        assert!(
            after.cwnd >= cwnd_before / 4,
            "no congestion collapse: {cwnd_before} -> {}",
            after.cwnd
        );
    });
}

#[test]
fn an_unanswered_wake_is_reported_after_800_ms() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(9, Params::new(10 * MS)));
        let now = net.now;
        net.a.with_env(now, pinc_transport::conn::Connection::sleep);
        net.run(now + 100 * MS, |_| false);
        net.link.route(PathId(1)).up = false;
        net.run(net.now + 2 * SEC, |_| false);
        let at = net.now;
        net.a.with_env(at, pinc_transport::conn::Connection::wake);
        assert!(net.run(at + 5 * SEC, |n| n.a.saw(|r| *r == Rec::WakeUnanswered)));
        let waited = net.now - at;
        assert!(
            (800 * MS..900 * MS).contains(&waited),
            "reported after {} ms",
            waited / MS
        );
    });
}

#[test]
fn a_link_return_does_not_wait_800_ms_for_an_answer() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(9, Params::new(10 * MS)));
        let now = net.now;
        net.link.route(PathId(1)).up = false;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.run(now + 2 * SEC, |_| false);
        let at = net.now;
        net.a.with_env(at, |c, env| c.set_link_down(env, false));
        assert!(!net.run(at + 5 * SEC, |n| n.a.saw(|r| *r == Rec::WakeUnanswered)));
    });
}

#[test]
fn a_link_outage_freezes_the_probe_backoff() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(10, Params::new(10 * MS)));
        let data = pattern(4 << 20, 11);
        let id = net.b.conn.open_bi().unwrap();
        let mut off = 0;
        net.run(net.now + 60 * SEC, |n| {
            serve(n, &data, &mut off, id);
            n.a.read.get(&id).map_or(0, Vec::len) > (1 << 20)
        });
        let count = net.b.conn.recovery().pto_count();
        let now = net.now;
        net.link.route(PathId(1)).up = false;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.b.with_env(now, |c, env| c.set_link_down(env, true));
        net.run(now + 20 * SEC, |_| false);
        // The probe timer still runs (it declares the oldest packet lost and pings) but the count does not grow.
        assert!(net.b.conn.stats().ptos > 0);
        assert_eq!(net.b.conn.recovery().pto_count(), count);
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
        net.link.route(PathId(1)).up = true;
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.b.with_env(now, |c, env| c.set_link_down(env, false));
        let mut finished = false;
        let ok = net.run(net.now + 120 * SEC, |n| {
            serve(n, &data, &mut off, id);
            if off == data.len() && !finished {
                n.b.conn.finish(id).unwrap();
                finished = true;
            }
            n.a.fin.contains(&id)
        });
        assert!(ok && net.a.read[&id] == data);
    });
}

#[test]
fn the_server_never_exceeds_three_times_what_it_received_before_validation() {
    big_stack(|| {
        for (alg, loss, seed) in [
            (IdentityAlg::Hybrid, 0.0, 1u64),
            (IdentityAlg::MlDsa65, 15.0, 2),
            (IdentityAlg::Ed25519, 25.0, 3),
        ] {
            let mut w = World::new(alg);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = setup(
                &mut w,
                &mut sa,
                &mut sb,
                Link::new(seed, Params::new(10 * MS).loss(loss)),
            );
            net.amp_check = true;
            assert!(net.connect(net.now + 300 * SEC), "{alg:?} never connected");
            assert!(net.b_tx > 0 && net.b_rx > 0);
        }
    });
}

#[test]
fn early_one_rtt_packets_wait_for_the_finish() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(12, Params::new(10 * MS)));
        net.drop_finish = true;
        // Once the client is connected (its Finish lost), it sends stream data that reaches the server first.
        let mut id = None;
        let ok = net.run(net.now + 20 * SEC, |n| {
            if id.is_none() && n.a.conn.is_connected() {
                let s = n.a.conn.open_bi().unwrap();
                n.a.conn.write(s, b"before the finish").unwrap();
                n.a.conn.finish(s).unwrap();
                id = Some(s);
            }
            id.is_some_and(|s| n.b.fin.contains(&s))
        });
        assert!(ok);
        let id = id.unwrap();
        assert_eq!(net.b.read[&id], b"before the finish");
        assert!(
            net.b.conn.stats().early_buffered > 0,
            "the packets were held until the peer was authenticated"
        );
    });
}

#[test]
fn at_most_eight_early_packets_are_held() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(13, Params::new(10 * MS)));
        let scid = Rc::new(RefCell::new(None));
        let s2 = scid.clone();
        net.on_tx = Some(Box::new(move |is_a, d, _| {
            if !is_a && s2.borrow().is_none() {
                *s2.borrow_mut() = LongHeader::parse(d).ok().map(|(h, _)| h.scid);
            }
        }));
        net.run(net.now + 15 * MS, |_| false);
        let cid = scid.borrow().unwrap();
        // The first reply is on the wire, so the server knows its id; the Finish has not reached it yet.
        assert!(!net.b.conn.is_connected());
        let now = net.now;
        for i in 0..20u8 {
            let mut d = vec![0x40u8];
            d.extend_from_slice(cid.as_bytes());
            d.extend_from_slice(&[i; 40]);
            let _ = net.b.with_env(now, |c, env| {
                c.handle_datagram_with(env, &mut *net.stores, PathId(2), &mut d)
            });
        }
        let s = net.b.conn.stats();
        assert_eq!(s.early_buffered, 8);
        assert_eq!(s.early_dropped, 12);
        assert!(
            net.connect(net.now + 20 * SEC),
            "junk in the buffer does not break the handshake"
        );
    });
}

#[test]
fn tail_repair_covers_a_lost_last_packet() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(14, Params::new(10 * MS).loss(8.0)));
        // Let the connection age and the shared loss average build up.
        for round in 0..300u64 {
            let data = pattern(3_000, round);
            let id = net.a.conn.open_uni().unwrap();
            net.a.conn.write(id, &data).unwrap();
            net.a.conn.finish(id).unwrap();
            assert!(net.run(net.now + 60 * SEC, |n| n.b.fin.contains(&id)), "round {round}");
            assert!(net.b.read[&id] == data);
            net.run(net.now + 30 * MS, |_| false);
        }
        assert!(net.a.conn.stats().repairs > 0, "{:?}", net.a.conn.stats());
    });
}

/// A connection old enough and with a loss average high enough to repair its tail, with a datagram buffer of
/// `room` bytes: it sends one small finished stream and polls once, so the repair of that packet is pending.
/// Returns the net with the buffer widened to the full size.
fn net_with_a_repair_pending<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, room: usize) -> Net<'a, 'a> {
    sa.loss.record(1000, 0);
    let mut net = setup(w, sa, sb, Link::new(31, Params::new(10 * MS).mtu(1500)));
    net.buf.truncate(room);
    assert!(net.connect(net.now + 30 * SEC), "{:?}", net.rx_drops);
    net.run(net.now + 3 * SEC, |_| false);
    let id = net.a.conn.open_uni().unwrap();
    net.a.conn.write(id, &pattern(100, 7)).unwrap();
    net.a.conn.finish(id).unwrap();
    assert!(poll_a(&mut net).is_some(), "the stream packet leaves");
    assert_eq!(net.a.conn.stats().repairs, 0, "{:?}", net.a.conn.stats());
    net.buf.resize(65_536, 0);
    net
}

/// One poll of A, by hand, so that nothing else is built in between.
fn poll_a(net: &mut Net<'_, '_>) -> Option<usize> {
    let mut env = Env {
        provider: &net.a.prov,
        now: net.now,
        drbg: &mut net.a.drbg,
    };
    net.a.conn.poll_transmit(&mut env, &mut net.buf).map(|t| t.len)
}

#[test]
fn a_tail_repair_that_is_due_with_a_path_mtu_probe_goes_with_the_next_packet() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // A buffer of 1300 bytes cannot hold the 1452 byte probe, so the first probe waits until the buffer grows.
        let mut net = net_with_a_repair_pending(&mut w, &mut sa, &mut sb, 1300);
        assert_eq!(poll_a(&mut net), Some(1452), "the probe leaves first");
        assert_eq!(net.a.conn.stats().repairs, 0, "{:?}", net.a.conn.stats());
        assert!(
            poll_a(&mut net).is_some_and(|n| n < 700),
            "the repair leaves with the next packet"
        );
        assert_eq!(net.a.conn.stats().repairs, 1, "{:?}", net.a.conn.stats());
    });
}

#[test]
fn a_tail_repair_with_no_probe_due_leaves_with_the_next_packet() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.probe_mtu = false;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = net_with_a_repair_pending(&mut w, &mut sa, &mut sb, 1300);
        assert!(poll_a(&mut net).is_some_and(|n| n < 700), "the repair leaves");
        assert_eq!(net.a.conn.stats().repairs, 1, "{:?}", net.a.conn.stats());
    });
}

#[test]
fn a_node_that_serves_a_relay_sends_no_tail_repair() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.tail_repair = false;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        // The same lossy link and bursts as the test above, where the repairs are sent.
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(14, Params::new(10 * MS).loss(8.0)));
        for round in 0..300u64 {
            let data = pattern(3_000, round);
            let id = net.a.conn.open_uni().unwrap();
            net.a.conn.write(id, &data).unwrap();
            net.a.conn.finish(id).unwrap();
            assert!(net.run(net.now + 60 * SEC, |n| n.b.fin.contains(&id)), "round {round}");
            net.run(net.now + 30 * MS, |_| false);
        }
        assert_eq!(net.a.conn.stats().repairs, 0, "{:?}", net.a.conn.stats());
    });
}

#[test]
fn a_tail_repair_of_a_small_packet_is_not_padded_to_the_full_size_when_datagrams_are_batched() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.max_gso = 8;
        w.cfg.probe_mtu = false;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(14, Params::new(10 * MS).loss(8.0)));
        let before = net.a.tx_log.len();
        for round in 0..300u64 {
            let data = pattern(100, round);
            let id = net.a.conn.open_uni().unwrap();
            net.a.conn.write(id, &data).unwrap();
            net.a.conn.finish(id).unwrap();
            assert!(net.run(net.now + 60 * SEC, |n| n.b.fin.contains(&id)), "round {round}");
            net.run(net.now + 30 * MS, |_| false);
        }
        assert!(net.a.conn.stats().repairs > 0, "{:?}", net.a.conn.stats());
        let biggest = net.a.tx_log.iter().skip(before).map(|t| t.1).max().unwrap();
        assert!(
            biggest < 600,
            "a 100 byte message never leaves in a datagram of {biggest} bytes"
        );
    });
}

#[test]
fn every_path_gets_its_own_connection_id() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(15, Params::new(10 * MS));
        for a in [3u64, 5] {
            link.add_route(PathId(a), PathId(a + 1), Params::new(10 * MS), Params::new(10 * MS));
        }
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        type Seen = Rc<RefCell<Vec<(bool, Vec<u8>, u64)>>>;
        let seen: Seen = Rc::default();
        let s2 = seen.clone();
        net.on_tx = Some(Box::new(move |is_a, d, now| {
            if is_a && d.first().is_some_and(|b| b & 0x80 == 0) {
                s2.borrow_mut().push((is_a, d[1..5].to_vec(), now));
            }
        }));
        net.run(net.now + SEC, |_| false);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(5), PathInfo::default()))
            .unwrap();
        net.run(net.now + 3 * SEC, |_| false);
        net.a.conn.set_active(PathId(3)).unwrap();
        net.a.conn.send_datagram(b"x").unwrap();
        net.run(net.now + SEC, |_| false);
        let mut ids: Vec<Vec<u8>> = seen.borrow().iter().map(|s| s.1.clone()).collect();
        ids.sort();
        ids.dedup();
        assert!(ids.len() >= 3, "three paths use three different ids, saw {}", ids.len());
        net.run(net.now + 5 * SEC, |_| false);
        assert!(net.a.closed().is_none() && net.b.closed().is_none());
    });
}

#[test]
fn a_path_is_not_size_probed_while_a_packet_sent_on_another_path_is_in_flight() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(18, Params::new(10 * MS).mtu(1500));
        link.add_route(
            PathId(3),
            PathId(4),
            Params::new(10 * MS).mtu(1500),
            Params::new(10 * MS).mtu(1500),
        );
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        net.run(net.now + 2 * SEC, |_| false);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
        net.run(net.now + SEC, |_| false);
        assert_eq!(
            net.a.conn.path_mtu(PathId(3)),
            Some(1200),
            "a path that is not active is not probed"
        );
        // A packet leaves on the first path and the session moves to the other before it is acknowledged.
        let id = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id, &pattern(100, 3)).unwrap();
        assert!(
            poll_a(&mut net).is_some_and(|n| n < 700),
            "the data packet leaves on the first path"
        );
        net.a.conn.set_active(PathId(3)).unwrap();
        assert_ne!(
            poll_a(&mut net),
            Some(1452),
            "no size probe while that packet is in flight"
        );
        assert_eq!(net.a.conn.path_mtu(PathId(3)), Some(1200));
        // Once it is acknowledged the probe goes.
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(3)), Some(1452));
    });
}

#[test]
fn a_path_whose_address_the_ledger_holds_is_not_size_probed_until_it_is_released() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(19, Params::new(10 * MS).mtu(1500));
        link.add_route(
            PathId(3),
            PathId(4),
            Params::new(10 * MS).mtu(1500),
            Params::new(10 * MS).mtu(1500),
        );
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        net.run(net.now + 2 * SEC, |_| false);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
        net.run(net.now + SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(3)), Some(1200));
        net.a.conn.set_path_held(PathId(3), true);
        assert!(net.a.conn.has_held_paths());
        net.a.conn.set_active(PathId(3)).unwrap();
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(
            net.a.conn.path_mtu(PathId(3)),
            Some(1200),
            "a size probe was offered on a held path"
        );
        net.a.conn.set_path_held(PathId(3), false);
        assert!(!net.a.conn.has_held_paths());
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(
            net.a.conn.path_mtu(PathId(3)),
            Some(1452),
            "the size probe did not go once the address was released"
        );
    });
}

#[test]
fn a_thin_node_rechallenges_an_idle_direct_path_on_a_backoff() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.thin = true;
        w.cfg.keepalive = Some(10 * SEC);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(16, Params::new(10 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(30 * MS), Params::new(30 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
        let t0 = net.now;
        let sent = |n: &Net<'_, '_>| n.link.routes[1].ab.sent;
        let base = sent(&net);
        let mut marks = Vec::new();
        for target in [15u64, 25, 55, 75, 140, 170] {
            net.run(t0 + target * SEC, |_| false);
            marks.push(sent(&net) - base);
        }
        // The path is silent for 15 s and stops being validated; the first challenge follows 20 s later (at +35 s) and
        // its answer validates the path again. Each later round waits 15 s of silence and then twice the previous
        // back-off: challenges at about +35 s, +90 s and +185 s, so marks are 0, 0, 1, 1, 2, 2. Only the end that
        // added the path challenges it.
        assert_eq!(marks, vec![0, 0, 1, 1, 2, 2], "{marks:?}");
    });
}

#[test]
fn the_pool_budget_is_never_exceeded() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::with_chunks(true, 320), Store::with_chunks(false, 320));
        let p = Params::new(10 * MS).loss(2.0).reorder(2.0, 3 * MS);
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(17, p));
        let data = pattern(16 << 20, 18);
        let id = net.a.conn.open_bi().unwrap();
        let (mut off, mut finished) = (0, false);
        let (mut max_a, mut max_b) = (0, 0);
        let ok = net.run(net.now + 900 * SEC, |n| {
            while off < data.len() {
                let k = n.a.conn.write(id, &data[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            if off == data.len() && !finished {
                n.a.conn.finish(id).unwrap();
                finished = true;
            }
            for _ in 0..4 {
                n.a.conn.send_datagram(&[7; 900]).ok();
                n.b.conn.send_datagram(&[8; 900]).ok();
            }
            max_a = max_a.max(n.a.conn.pool().used_bytes());
            max_b = max_b.max(n.b.conn.pool().used_bytes());
            assert!(n.a.conn.pool().used_bytes() <= n.a.conn.pool().budget_bytes());
            assert!(n.b.conn.pool().used_bytes() <= n.b.conn.pool().budget_bytes());
            n.b.fin.contains(&id)
        });
        assert!(ok && net.b.read[&id] == data);
        let budget = net.a.conn.pool().budget_bytes();
        assert!(
            max_a <= budget && max_b <= budget && budget == 320 * 16 * 1024,
            "{max_a} {max_b} {budget}"
        );
        // The send buffer holds at most max(192 KiB, 1.5 x the window), so the sender uses a fraction of the pool.
        assert!(max_a > budget / 16, "the transfer really used the pool");
    });
}

#[test]
fn steady_state_allocates_nothing() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(19, Params::new(MS)));
        let warm = pattern(4 << 20, 20);
        let (_, id) = bulk(&mut net, &warm, 120 * SEC);
        net.run(net.now + SEC, |_| false);
        let stores = net.stores;
        let (mut a, mut b) = (net.a, net.b);
        let mut now = net.now;
        let sid = a.conn.open_bi().unwrap();
        let chunk = [0x5au8; 8192];
        let mut abuf = vec![0u8; 4096];
        let mut bbuf = vec![0u8; 4096];
        // Warm up the direct pump itself, then measure a window of the transfer.
        for _ in 0..300 {
            now += MS;
            a.conn.write(sid, &chunk).ok();
            pump(&mut a, &mut b, stores, &mut abuf, &mut bbuf, sid, now);
        }
        let before = a.conn.stats().packets_sent + b.conn.stats().packets_sent;
        let stats = measure(|| {
            for _ in 0..2_000 {
                now += MS;
                a.conn.write(sid, &chunk).ok();
                pump(&mut a, &mut b, stores, &mut abuf, &mut bbuf, sid, now);
            }
        });
        let packets = a.conn.stats().packets_sent + b.conn.stats().packets_sent - before;
        assert!(packets > 1_000, "the window moved {packets} packets");
        assert_eq!(stats.count(), 0, "{} allocations over {packets} packets", stats.count());
        let _ = id;
    });
}

/// One allocation-free exchange between two connections: everything each has to send, delivered to the other.
fn pump(a: &mut Node<'_>, b: &mut Node<'_>, stores: &mut Stores, abuf: &mut [u8], bbuf: &mut [u8], sid: u64, now: u64) {
    for _ in 0..8 {
        let mut any = false;
        let mut ea = Env {
            provider: &a.prov,
            now,
            drbg: &mut a.drbg,
        };
        let mut eb = Env {
            provider: &b.prov,
            now,
            drbg: &mut b.drbg,
        };
        while let Some(t) = a.conn.poll_transmit(&mut ea, abuf) {
            b.conn
                .handle_datagram_with(&mut eb, stores, PathId(2), &mut abuf[..t.len])
                .ok();
            any = true;
        }
        while let Some(t) = b.conn.poll_transmit(&mut eb, bbuf) {
            a.conn.handle_datagram(&mut ea, PathId(1), &mut bbuf[..t.len]).ok();
            any = true;
        }
        while a.conn.poll_event().is_some() {}
        while b.conn.poll_event().is_some() {}
        while let Some(c) = b.conn.read_chunk(sid) {
            let n = c.len();
            b.conn.consume(&mut eb, sid, n).ok();
        }
        if a.conn.poll_timeout().is_some_and(|t| t <= now) {
            a.conn.handle_timeout(&mut ea);
        }
        if b.conn.poll_timeout().is_some_and(|t| t <= now) {
            b.conn.handle_timeout(&mut eb);
        }
        if !any {
            break;
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 48, ..ProptestConfig::default() })]

    /// Whatever arrives, nothing panics, and a connection that was not legitimately closed keeps working.
    #[test]
    fn garbage_datagrams_never_panic(
        junk in proptest::collection::vec(proptest::collection::vec(any::<u8>(), 0..1600), 1..24),
        mutate in proptest::collection::vec((0usize..64, 0usize..1500, any::<u8>(), 0usize..1500), 0..24),
    ) {
        big_stack(move || {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(21, Params::new(5 * MS)));
            let seen: Rc<RefCell<Vec<Vec<u8>>>> = Rc::default();
            let s2 = seen.clone();
            net.on_tx = Some(Box::new(move |_, d, _| s2.borrow_mut().push(d.to_vec())));
            // Garbage first, at a server that is still waiting for its first message.
            let now = net.now;
            for j in &junk {
                let mut d = j.clone();
                let _ = net.b.with_env(now, |c, env| c.handle_datagram_with(env, &mut *net.stores, PathId(2), &mut d));
            }
            assert!(net.connect(net.now + 30 * SEC));
            let id = net.a.conn.open_bi().unwrap();
            net.a.conn.write(id, &vec![1; 20_000]).unwrap();
            net.run(net.now + SEC, |_| false);
            // Then junk and altered copies of real packets, at both ends of a live connection.
            let real = seen.borrow().clone();
            let now = net.now;
            for (which, at, byte, cut) in mutate {
                let Some(src) = real.get(which % real.len().max(1)) else { continue };
                let mut d = src.clone();
                let idx = at % d.len().max(1);
                if let Some(x) = d.get_mut(idx) {
                    *x ^= byte;
                }
                d.truncate(d.len().saturating_sub(cut % 8));
                let mut d2 = d.clone();
                let _ = net.a.with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut d));
                let _ = net.b.with_env(now, |c, env| c.handle_datagram_with(env, &mut *net.stores, PathId(2), &mut d2));
            }
            for j in &junk {
                let mut d = j.clone();
                let _ = net.a.with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut d));
            }
            net.run(net.now + 10 * SEC, |_| false);
            if net.a.closed().is_none() && net.b.closed().is_none() {
                net.a.conn.write(id, &[2; 100]).unwrap();
                net.a.conn.finish(id).unwrap();
                assert!(net.run(net.now + 30 * SEC, |n| n.b.fin.contains(&id)), "the connection still works");
            }
        });
    }
}
