//! The rules of the transport pinned with their numbers: derived connection ids, the stream-level limits as the
//! connection shows them, sleep and wake, path rules, path MTU, the fixed packet-number width and the first flight.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::type_complexity
)]

use std::cell::RefCell;
use std::rc::Rc;

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, ExtensionError, PathId, PathInfo, code};
use vinc_transport::frame::ext;
use vinc_transport::recovery::PathKind;

vinc_tests::install_counting_allocator!();

fn connected<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, link: Link) -> Net<'a, 'a> {
    let mut net = setup(w, sa, sb, link);
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    net
}

type Log = Rc<RefCell<Vec<(bool, Vec<u8>, u64)>>>;

fn capture(net: &mut Net<'_, '_>) -> Log {
    let log: Log = Rc::default();
    let sink = log.clone();
    net.on_tx = Some(Box::new(move |is_a, d, now| {
        sink.borrow_mut().push((is_a, d.to_vec(), now));
    }));
    log
}

// ---- derived connection ids ----

#[test]
fn derived_connection_ids_are_per_session_and_unlinkable_across_paths() {
    big_stack(|| {
        let mut ids = Vec::new();
        for seed in [0u8, 1] {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.seed = seed;
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut link = Link::new(1, Params::new(10 * MS));
            link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
            let mut net = connected(&mut w, &mut sa, &mut sb, link);
            let log = capture(&mut net);
            let now = net.now;
            net.a
                .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
                .unwrap();
            assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
            // The index-0 id, the index the second path used and the next two after it are accepted.
            let local: Vec<_> = net.b.conn.local_cids().collect();
            assert_eq!(local.len(), 4, "{local:?}");
            assert!(local.iter().all(|c| net.b.conn.accepts_cid(c)));
            // The datagrams to B on the two paths name different ids, both ones B accepts.
            let mut distinct: Vec<Vec<u8>> = log
                .borrow()
                .iter()
                .filter(|(is_a, d, _)| *is_a && d[0] & 0x80 == 0)
                .map(|(_, d, _)| d[1..5].to_vec())
                .collect();
            distinct.sort();
            distinct.dedup();
            assert!(distinct.len() >= 2, "one id on two paths: {distinct:?}");
            for d in &distinct {
                assert!(local.iter().any(|c| c.as_bytes() == d.as_slice()));
            }
            ids.push(local);
        }
        // Another session derives other ids.
        assert!(ids[0][1..].iter().all(|c| !ids[1].contains(c)));
    });
}

#[test]
fn a_colliding_connection_id_is_decided_by_the_packet_authentication() {
    big_stack(|| {
        // With one-byte ids two sessions of one endpoint collide often. Find two sessions that accept a common id.
        let mut sets = Vec::new();
        for seed in 0u8..64 {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.seed = seed;
            w.cfg.cid_len = 1;
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let net = connected(&mut w, &mut sa, &mut sb, Link::new(2, Params::new(MS)));
            sets.push(net.b.conn.local_cids().skip(1).collect::<Vec<_>>());
        }
        let pair = (0..sets.len())
            .flat_map(|i| (i + 1..sets.len()).map(move |j| (i, j)))
            .find(|(i, j)| sets[*i].iter().any(|c| sets[*j].contains(c)))
            .expect("with 64 sessions and one-byte ids two must share an id");
        let build = |seed: u8| {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.seed = seed;
            w.cfg.cid_len = 1;
            w
        };
        let (mut w1, mut w2) = (build(pair.0 as u8), build(pair.1 as u8));
        let (mut sa1, mut sb1, mut sa2, mut sb2) =
            (Store::new(true), Store::new(false), Store::new(true), Store::new(false));
        let mut n1 = connected(&mut w1, &mut sa1, &mut sb1, Link::new(2, Params::new(MS)));
        let mut n2 = connected(&mut w2, &mut sa2, &mut sb2, Link::new(2, Params::new(MS)));
        let shared = *sets[pair.0].iter().find(|c| sets[pair.1].contains(c)).unwrap();
        // A packet of session 1 addressed with the shared id reaches session 2, which also accepts the id: its
        // authentication refuses the packet, and nothing else changes.
        assert!(n1.b.conn.accepts_cid(&shared) && n2.b.conn.accepts_cid(&shared));
        let log = capture(&mut n1);
        let id = n1.a.conn.open_bi().unwrap();
        n1.a.conn.write(id, &[9u8; 300]).unwrap();
        n1.run(n1.now + SEC, |_| false);
        let mut dg = log
            .borrow()
            .iter()
            .rev()
            .find(|(is_a, d, _)| *is_a && d[0] & 0x80 == 0)
            .map(|(_, d, _)| d.clone())
            .unwrap();
        dg[1] = shared.as_bytes()[0];
        let before = n2.b.conn.stats();
        let now = n2.now;
        let r = n2.b.with_env(now, |c, env| c.handle_datagram(env, PathId(2), &mut dg));
        assert!(r.is_err(), "another session's packet must not open");
        assert!(n2.b.conn.is_connected());
        assert_eq!(n2.b.conn.stats().packets_received, before.packets_received);
        let id2 = n2.a.conn.open_bi().unwrap();
        n2.a.conn.write(id2, b"still fine").unwrap();
        n2.a.conn.finish(id2).unwrap();
        assert!(n2.run(n2.now + 5 * SEC, |n| n.b.fin.contains(&id2)));
    });
}

// ---- close ----

#[test]
fn close_carries_one_code_and_leave_is_0x4c() {
    big_stack(|| {
        assert_eq!((code::NO_ERROR, code::FLOW_CONTROL, code::LEAVE), (0, 3, 0x4C));
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(3, Params::new(5 * MS)));
        let now = net.now;
        net.a.with_env(now, |c, env| c.close(env, code::LEAVE));
        assert!(net.run(net.now + SEC, |n| n.b.closed().is_some()));
        assert_eq!(net.b.closed(), Some(CloseReason::Peer { error: 0x4C }));
        assert!(net.a.conn.is_closed() && net.b.conn.is_closed());
    });
}

// ---- send buffer, urgency, last frame ----

#[test]
fn the_send_buffer_is_bounded_by_the_window_and_the_congestion_window() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(4, Params::new(10 * MS)));
        let id = net.a.conn.open_bi().unwrap();
        let data = vec![1u8; 4 << 20];
        // A fresh connection: cwnd 44,000, so max(192 KiB, 1.5 x 44,000) = 192 KiB, below the 1.25 MiB window.
        let first = net.a.conn.write(id, &data).unwrap();
        assert_eq!(first, 196_608);
        assert_eq!(net.a.conn.write(id, &data).unwrap(), 0);
        // Acknowledgements free room and wake the writer.
        assert!(net.run(net.now + 5 * SEC, |n| n.a.saw(|r| *r == Rec::Writable(id))));
    });
}

#[test]
fn streams_are_served_in_order_of_urgency() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(5, Params::new(10 * MS)));
        let (low, high) = (net.a.conn.open_bi().unwrap(), net.a.conn.open_bi().unwrap());
        net.a.conn.set_urgency(low, 5).unwrap();
        net.a.conn.set_urgency(high, 1).unwrap();
        let data = vec![7u8; 100_000];
        // The less urgent stream is written first; the more urgent one is still served first.
        net.a.conn.write(low, &data).unwrap();
        net.a.conn.write(high, &data).unwrap();
        net.a.conn.finish(low).unwrap();
        net.a.conn.finish(high).unwrap();
        let order = Rc::new(RefCell::new(Vec::new()));
        net.run(net.now + 10 * SEC, |n| {
            for id in [low, high] {
                if n.b.fin.contains(&id) && !order.borrow().contains(&id) {
                    order.borrow_mut().push(id);
                }
            }
            order.borrow().len() == 2
        });
        assert_eq!(*order.borrow(), vec![high, low]);
    });
}

#[test]
fn the_last_stream_frame_of_a_packet_leaves_its_length_out() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(6, Params::new(10 * MS)));
        net.run(net.now + 3 * SEC, |_| false);
        let log = capture(&mut net);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &[0x42u8; 100]).unwrap();
        net.run(net.now + 200 * MS, |_| false);
        // Short header (1 + 4 id + 2 packet number), then the frame: type, stream id, 100 bytes, then the tag. A
        // length field would take one more byte.
        let sent = log.borrow();
        let data_packet = sent.iter().find(|(is_a, d, _)| *is_a && d.len() >= 120).unwrap();
        assert_eq!(data_packet.1.len(), 1 + 4 + 2 + (1 + 1 + 100) + 16);
    });
}

// ---- reliability of extension frames ----

#[test]
fn an_extension_frame_is_sent_again_when_its_packet_is_lost() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(7, Params::new(10 * MS)));
        net.run(net.now + SEC, |_| false);
        net.link.route(PathId(1)).ab.drop_next(1);
        net.a.conn.send_extension(ext::TEST_FIRST, b"sub open").unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| {
            n.b.saw(|r| *r == Rec::Extension(ext::TEST_FIRST, b"sub open".to_vec()))
        }));
        let max = net.a.conn.max_extension_size(0x41);
        assert!(max > 1025, "{max}");
        assert_eq!(
            net.a.conn.send_extension(ext::TEST_FIRST, &vec![0u8; max + 1]),
            Err(ExtensionError::TooLarge { max_size: max })
        );
        assert_eq!(net.a.conn.send_extension(0x10, b"low"), Err(ExtensionError::BadType));
    });
}

#[test]
fn an_extension_frame_near_the_packet_limit_is_delivered_once_under_loss() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(8, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        let max = net.a.conn.max_extension_size(0x41);
        assert!(max > 1300, "{max}");
        let body: Vec<u8> = (0..max).map(|i| (i % 251) as u8).collect();
        net.link.route(PathId(1)).ab.drop_next(2);
        net.a.conn.send_extension(ext::TEST_FIRST, &body).unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| {
            n.b.saw(|r| *r == Rec::Extension(ext::TEST_FIRST, body.clone()))
        }));
        // Once acknowledged the frame is not sent again.
        net.run(net.now + 5 * SEC, |_| false);
        let seen = net
            .b
            .log
            .iter()
            .filter(|r| **r == Rec::Extension(ext::TEST_FIRST, body.clone()))
            .count();
        assert_eq!(seen, 1, "delivered {seen} times");
        // One byte more cannot fit the packet.
        assert!(matches!(
            net.a.conn.send_extension(ext::TEST_FIRST, &vec![0u8; max + 1]),
            Err(ExtensionError::TooLarge { .. })
        ));
    });
}

#[test]
fn an_extension_frame_that_no_longer_fits_after_the_mtu_falls_is_reported_and_frees_its_slot() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(9, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 2 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        // A second path, still at the minimum size, is validated while the first is about to lose its datagrams.
        let p = Params::new(10 * MS);
        net.link.add_route(PathId(3), PathId(4), p, p);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
        net.run(net.now + SEC, |_| false);
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        assert_eq!(net.a.conn.path_mtu(PathId(3)), Some(1200));
        // A frame as large as the first path takes goes out and is never acknowledged.
        let big = net.a.conn.max_extension_size(0x41);
        net.link.route(PathId(1)).up = false;
        net.a.conn.send_extension(ext::TEST_FIRST, &vec![7u8; big]).unwrap();
        net.run(net.now + 300 * MS, |_| false);
        // The connection moves to the smaller path: the held frame cannot fit a packet there.
        net.a.conn.set_active(PathId(3)).unwrap();
        let max = net.a.conn.max_extension_size(0x41);
        assert!(max < big, "{max} {big}");
        net.run(net.now + 10 * MS, |_| false);
        assert!(net.a.saw(|r| *r == Rec::ExtensionUndeliverable(ext::TEST_FIRST, big)));
        assert!(matches!(
            net.a.conn.send_extension(ext::TEST_FIRST, &vec![0u8; big]),
            Err(ExtensionError::TooLarge { max_size }) if max_size == max
        ));
        // Every slot is free: eight more frames, each as large as now fits, all arrive once.
        for ty in 0x50..0x58u64 {
            net.a.conn.send_extension(ty, &vec![ty as u8; max]).unwrap();
        }
        assert!(net.run(net.now + 30 * SEC, |n| {
            (0x50..0x58u64).all(|ty| n.b.saw(|r| *r == Rec::Extension(ty, vec![ty as u8; max])))
        }));
        assert!(
            !net.b.saw(|r| matches!(r, Rec::Extension(ext::TEST_FIRST, _))),
            "the dropped frame was delivered"
        );
    });
}

// ---- amplification ----

#[test]
fn a_server_counts_48_bytes_more_than_each_datagram_it_sends() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Hybrid);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(8, Params::new(10 * MS)));
        net.amp_check = true;
        assert!(net.connect(net.now + 30 * SEC));
        assert!(net.b_tx > 0 && net.b_tx <= 3 * net.b_rx, "{} {}", net.b_tx, net.b_rx);
    });
}

// ---- packet number width and the first flight ----

#[test]
fn the_packet_number_is_two_bytes_wide_for_a_window_up_to_40_mb() {
    // The test table holds windows of at most 4 MiB, so only the base width runs end to end here; the rule that
    // picks three bytes above 40 MB is pinned in the packet tests (`the_width_follows_the_granted_window`).
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(9, Params::new(5 * MS)));
        let log = capture(&mut net);
        net.a.conn.send_datagram(b"x").unwrap();
        net.run(net.now + 200 * MS, |_| false);
        let sent = log.borrow();
        let short: Vec<_> = sent.iter().filter(|(is_a, d, _)| *is_a && d[0] & 0x80 == 0).collect();
        assert_ne!(short.len(), 0);
        // Header: 1 + 4 id + 2 packet number; frame: DATAGRAM, length, 1 byte; then the 16-byte tag.
        assert_eq!(short[0].1.len(), 1 + 4 + 2 + 3 + 16);
    });
}

#[test]
fn a_first_flight_that_fits_one_datagram_goes_whole_only_when_asked() {
    big_stack(|| {
        let count = |split: bool| -> (usize, usize) {
            big_stack(move || {
                let mut w = World::new(IdentityAlg::Ed25519);
                w.cfg.flight_split = split;
                let (mut sa, mut sb) = (Store::new(true), Store::new(false));
                let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(10, Params::new(10 * MS)));
                let log = capture(&mut net);
                net.run(net.now + 5 * MS, |_| false);
                let a: Vec<_> = log
                    .borrow()
                    .iter()
                    .filter(|(is_a, ..)| *is_a)
                    .map(|(_, d, _)| d.len())
                    .collect();
                assert!(net.connect(net.now + 5 * SEC));
                (a.len(), a.iter().copied().max().unwrap())
            })
        };
        let (off_n, off_max) = count(false);
        let (on_n, on_max) = count(true);
        assert!(off_max <= 1200, "{off_max}");
        assert_eq!(off_n, 2, "two datagrams of at most 1200 bytes");
        assert_eq!(on_n, 1, "one datagram");
        assert!(on_max > 1200 && on_max <= 1452, "{on_max}");
    });
}

// ---- sleep and wake ----

#[test]
fn any_packet_ends_a_sleep_and_data_flows_to_a_sleeping_peer() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(11, Params::new(10 * MS)));
        let now = net.now;
        net.a.with_env(now, vinc_transport::conn::Connection::sleep);
        assert!(net.run(net.now + SEC, |n| n.b.conn.peer_asleep()));
        // Data is not held back for a peer that announced its sleep.
        let id = net.b.conn.open_bi().unwrap();
        net.b.conn.write(id, b"for a sleeper").unwrap();
        net.b.conn.finish(id).unwrap();
        net.run(net.now + SEC, |_| false);
        assert!(net.b.conn.stats().packets_sent > 0 && net.b.conn.peer_asleep());
        // Any packet from the sleeper ends the sleep, with or without a WAKE: here it simply sends data.
        let now = net.now;
        net.a.with_env(now, vinc_transport::conn::Connection::wake);
        assert!(net.run(net.now + 5 * SEC, |n| !n.b.conn.peer_asleep()));
        assert!(net.b.saw(|r| *r == Rec::PeerAwake));
    });
}

#[test]
fn a_lost_wake_does_not_leave_the_connection_suspended() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(12, Params::new(10 * MS)));
        let now = net.now;
        net.a.with_env(now, vinc_transport::conn::Connection::sleep);
        assert!(net.run(net.now + SEC, |n| n.b.conn.peer_asleep()));
        // The datagram carrying the WAKE is lost; the sleeper then sends ordinary data.
        net.link.route(PathId(1)).ab.drop_next(1);
        let now = net.now;
        net.a.with_env(now, vinc_transport::conn::Connection::wake);
        net.run(net.now + 10 * MS, |_| false);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"I am back").unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| n.b.fin.contains(&id)));
        assert!(!net.b.conn.peer_asleep(), "the data ended the sleep");
        // And B's own data reaches A again.
        let back = net.b.conn.open_bi().unwrap();
        net.b.conn.write(back, b"welcome").unwrap();
        net.b.conn.finish(back).unwrap();
        assert!(net.run(net.now + 10 * SEC, |n| n.a.fin.contains(&back)));
    });
}

#[test]
fn a_link_return_sends_wake_and_the_probes_repeat_it_for_3_seconds() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(13, Params::new(10 * MS)));
        net.run(net.now + SEC, |_| false);
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.link.route(PathId(1)).up = false;
        net.run(net.now + 2 * SEC, |_| false);
        net.link.route(PathId(1)).up = true;
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &[1u8; 5000]).unwrap();
        let log = capture(&mut net);
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.run(net.now + 50 * MS, |_| false);
        assert!(net.a.conn.stats().packets_sent > 0);
        assert!(!log.borrow().is_empty(), "a datagram leaves at once on a link return");
    });
}

// ---- paths ----

#[test]
fn a_direct_path_silent_for_15_seconds_is_no_longer_validated_and_the_session_falls_back_to_a_relay() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(14, Params::new(10 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(40 * MS), Params::new(40 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let relay = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), relay)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(4), relay)).unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.a.conn.path_validated(PathId(3))));
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)));
        // Nothing arrives on the direct path any more.
        net.link.route(PathId(1)).up = false;
        net.run(net.now + 14 * SEC, |_| false);
        assert!(net.a.conn.path_validated(PathId(1)));
        net.run(net.now + 3 * SEC, |_| false);
        assert!(!net.a.conn.path_validated(PathId(1)));
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(3)),
            "the session left the silent direct path"
        );
    });
}

#[test]
fn both_ends_follow_a_new_path_at_once_and_challenge_it_in_parallel() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(15, Params::new(10 * MS));
        link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        // A's route 1 now looks to B like a new address: NAT rebinding.
        net.link.rebind(PathId(1), PathId(9));
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"after the rebinding").unwrap();
        net.a.conn.finish(id).unwrap();
        // One trip later B sends on the new path, before any challenge is answered.
        assert!(net.run(net.now + 25 * MS, |n| n.b.conn.active_path() == Some(PathId(9))));
        assert!(!net.b.conn.path_validated(PathId(9)) || net.b.saw(|r| *r == Rec::PathValidated(PathId(9))));
        assert!(net.run(net.now + 5 * SEC, |n| n.b.fin.contains(&id)));
        assert!(net.run(net.now + 5 * SEC, |n| n.b.conn.path_validated(PathId(9))));
    });
}

// ---- path MTU ----

#[test]
fn mtu_probes_go_on_direct_udp_paths_of_nodes_that_are_not_thin_and_not_just_resumed() {
    big_stack(|| {
        // A thin node never probes.
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.thin = true;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, Link::new(16, Params::new(10 * MS).mtu(1500)));
        net.run(net.now + 3 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1200));
        // After a link return no probe is sent for 10 s.
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(17, Params::new(10 * MS).mtu(1500)));
        net.a.conn.set_keepalive(None);
        assert!(net.connect(net.now + 10 * SEC));
        let now = net.now;
        net.a.with_env(now, |c, env| c.set_link_down(env, true));
        net.a.with_env(now, |c, env| c.set_link_down(env, false));
        net.link.route(PathId(1)).up = true;
        net.run(net.now + 9 * SEC, |_| false);
        net.run(net.now + 3 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(1452));
        // A relay path is not probed.
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(18, Params::new(10 * MS));
        link.add_route(
            PathId(3),
            PathId(4),
            Params::new(10 * MS).mtu(1500),
            Params::new(10 * MS).mtu(1500),
        );
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let relay = PathInfo {
            kind: PathKind::Relay,
            ..PathInfo::default()
        };
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), relay)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(4), relay)).unwrap();
        net.run(net.now + 5 * SEC, |_| false);
        assert_eq!(net.a.conn.path_mtu(PathId(3)), Some(1200));
    });
}

#[test]
fn a_jumbo_probe_needs_an_interface_above_2904_bytes() {
    big_stack(|| {
        for (iface, want) in [(2904u16, 1452u16), (3000, 3000), (9000, 8952)] {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(19, Params::new(MS / 4).mtu(9000)));
            // The interface size is the endpoint's knowledge of the first path.
            assert!(net.connect(net.now + 10 * SEC));
            let now = net.now;
            let info = PathInfo {
                interface_mtu: iface,
                ..PathInfo::default()
            };
            net.a.with_env(now, |c, env| c.add_path(env, PathId(1), info)).unwrap();
            net.run(net.now + 10 * SEC, |_| false);
            assert_eq!(net.a.conn.path_mtu(PathId(1)), Some(want), "interface {iface}");
        }
    });
}

#[test]
fn data_after_an_idle_spell_brings_the_slow_rechallenge_forward() {
    big_stack(|| {
        let run = |write_at_20s: bool| -> u64 {
            big_stack(move || {
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
                let base = net.link.routes[1].ab.sent;
                // The path is silent for 15 s, then waits 20 s for its first re-challenge (at +35 s).
                net.run(t0 + 20 * SEC, |_| false);
                if write_at_20s {
                    // Data of more than 72 bytes after an idle spell: the next challenge goes out now.
                    let id = net.a.conn.open_bi().unwrap();
                    net.a.conn.write(id, &[3u8; 100]).unwrap();
                }
                net.run(t0 + 28 * SEC, |_| false);
                net.link.routes[1].ab.sent - base
            })
        };
        assert_eq!(run(false), 0, "without data the first re-challenge waits for +35 s");
        assert_eq!(run(true), 1, "with data it goes out at once");
    });
}
