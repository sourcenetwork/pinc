//! The VINCER connection end to end over a deterministic in-memory link.
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
    clippy::large_stack_arrays,
    clippy::assert_is_empty
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{CloseReason, Drop, PathId};
use vinc_transport::frame::ext;
use vinc_transport::stream::datagram::DatagramError;

vinc_tests::install_counting_allocator!();

fn connect_with(alg: IdentityAlg) {
    big_stack(move || {
        let mut w = World::new(alg);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(1, Params::new(10 * MS)));
        assert!(net.connect(net.now + 10 * SEC), "{:?} {:?}", net.rx_drops, net.a.log);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"hello").unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(net.run(net.now + 5 * SEC, |n| n.b.fin.contains(&id)));
        assert_eq!(net.b.read[&id], b"hello");
        assert!(net.a.conn.session().is_some_and(|s| s.peer == w_peer(alg)));
    });
}

fn w_peer(alg: IdentityAlg) -> vinc_crypto::NodeId {
    World::new(alg).rp.id.node_id()
}

#[test]
fn handshake_ed25519() {
    connect_with(IdentityAlg::Ed25519);
}

#[test]
fn handshake_ecdsa_p256() {
    connect_with(IdentityAlg::EcdsaP256);
}

#[test]
fn handshake_ml_dsa_65() {
    connect_with(IdentityAlg::MlDsa65);
}

#[test]
fn handshake_hybrid() {
    connect_with(IdentityAlg::Hybrid);
}

const BULK: usize = 64 << 20;

/// 64 MiB from A to B over a link with the given loss, 1% duplication and reordering; bytes must match exactly.
fn bulk_64(seed: u64, loss: f64) {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let p = Params::new(10 * MS).loss(loss).dup(1.0).reorder(2.0, 3 * MS).jitter(MS);
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, p));
        assert!(net.connect(net.now + 60 * SEC), "{:?}", net.a.log);
        let data = pattern(BULK, seed);
        let (t, _) = bulk(&mut net, &data, 3600 * SEC);
        let s = net.a.conn.stats();
        eprintln!(
            "64 MiB at {loss}% loss: {} ms virtual, {:.1} MB/s, lost {} acked {} ptos {} repairs {} mtu {}",
            t / MS,
            BULK as f64 / 1e6 / (t as f64 / 1e9),
            s.packets_lost,
            s.packets_acked,
            s.ptos,
            s.repairs,
            s.mtu
        );
        // The sender finishes too: every byte is acknowledged and nothing stays in flight.
        assert!(
            net.run(net.now + 60 * SEC, |n| n.a.conn.recovery().bytes_in_flight() == 0),
            "data left in flight"
        );
    });
}

#[test]
fn bulk_64_mib_no_loss() {
    bulk_64(21, 0.0);
}

#[test]
fn bulk_64_mib_1_percent_loss() {
    bulk_64(22, 1.0);
}

#[test]
fn bulk_64_mib_5_percent_loss() {
    bulk_64(23, 5.0);
}

/// 8 MiB over 20 ms with `params`; returns (virtual ms, packets declared lost, packets sent).
fn transfer_8_mib(seed: u64, params: Params) -> (u64, u64, u64) {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, params));
        assert!(net.connect(net.now + 60 * SEC));
        let data = pattern(8 << 20, seed);
        let (t, _) = bulk(&mut net, &data, 600 * SEC);
        let s = net.a.conn.stats();
        (t / MS, s.packets_lost, s.packets_sent)
    })
}

/// Datagrams that overtake each other on one path (independent 1 ms jitter on a 20 ms path: every pacing burst
/// arrives shuffled) are not loss: after the first overtaken packet the path keeps the time rule, so the transfer takes
/// about as long as on an ordered path and almost nothing is declared lost.
#[test]
fn reordering_on_one_path_does_not_collapse_the_window() {
    let (ordered_ms, _, _) = transfer_8_mib(41, Params::new(10 * MS).jitter(MS));
    let (ms, lost, sent) = transfer_8_mib(41, Params::new(10 * MS).unordered_jitter(MS));
    assert!(ms <= 2 * ordered_ms, "reordered {ms} ms vs ordered {ordered_ms} ms");
    assert!(lost * 200 <= sent, "{lost} of {sent} packets declared lost");
}

/// A path whose bandwidth-delay product (an unlimited link over 100 ms) exceeds what the 512-slot sent ring holds in
/// flight (about 740 KB) lets the window open past the ring while a packet that arrives late holds the ring head. The
/// sender must then wait for acknowledgements, not rebuild a packet the ring refuses at the same instant (which stalls
/// virtual time): the transfer finishes, at about the rate the ring allows, one ring per round trip.
#[test]
fn a_path_whose_bandwidth_delay_product_exceeds_the_ring_makes_progress() {
    for seed in [41, 42] {
        let (ms, lost, sent) = transfer_8_mib(seed, Params::new(50 * MS).unordered_jitter(MS));
        assert!(ms < 10_000, "{ms} ms for 8 MiB");
        assert!(lost * 100 <= sent, "{lost} of {sent} packets declared lost");
    }
}

/// `size` bytes over `params`; returns the datagrams the receiver dropped, by reason.
fn receiver_drops(seed: u64, size: usize, params: Params) -> std::collections::BTreeMap<String, u64> {
    big_stack(move || {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, params));
        assert!(net.connect(net.now + 60 * SEC));
        let data = pattern(size, seed);
        bulk(&mut net, &data, 600 * SEC);
        let mut drops = std::collections::BTreeMap::new();
        for (to_a, d) in &net.rx_drops {
            if !*to_a {
                *drops.entry(format!("{d:?}")).or_insert(0) += 1;
            }
        }
        drops
    })
}

/// Deep reordering at a window of megabytes leaves dozens of holes open at once. The receiver must keep track of all
/// of them: a datagram dropped for lack of room (`Drop::Empty`: pool space or stream ranges) is lost to the sender, and
/// a new packet judged a duplicate (`Drop::Duplicate`; the link duplicates nothing here) is never acknowledged.
#[test]
fn deep_reordering_at_a_large_window_drops_nothing_for_room_or_as_a_duplicate() {
    // 5 ms of independent jitter on top of 5% of the datagrams held back 20 ms: the deepest case measured (116 packet
    // ranges open at once at 16 MiB). 2 MiB is enough to fail with 32 packet ranges and 16 stream ranges.
    let drops = receiver_drops(
        83,
        2 << 20,
        Params::new(10 * MS).unordered_jitter(5 * MS).reorder(5.0, 20 * MS),
    );
    for kind in [Drop::Empty, Drop::Duplicate] {
        assert_eq!(drops.get(&format!("{kind:?}")), None, "{drops:?}");
    }
}

#[test]
fn many_concurrent_streams_in_both_directions() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        // Every admitted stream is charged its whole window, so the pool must hold the windows of all 40 at once.
        let (mut sa, mut sb) = (Store::with_chunks(true, 8192), Store::with_chunks(false, 8192));
        let mut net = setup(
            &mut w,
            &mut sa,
            &mut sb,
            Link::new(31, Params::new(5 * MS).loss(0.5).reorder(1.0, 2 * MS)),
        );
        assert!(net.connect(net.now + 10 * SEC));
        // The table keeps half its slots free for the credit it gave, so 32 of the 64 are ours to open. Both ends open far more than the credit of the handshake: the test is about delivery under loss.
        net.a.conn.raise_stream_credit(100);
        net.b.conn.raise_stream_credit(100);
        let a_ids: Vec<u64> = (0..32).map(|_| net.a.conn.open_bi().unwrap()).collect();
        let b_ids: Vec<u64> = (0..8).map(|_| net.b.conn.open_uni().unwrap()).collect();
        let a_data: Vec<Vec<u8>> = (0..32).map(|i| pattern(100_000 + i * 1_000, 100 + i as u64)).collect();
        let b_data: Vec<Vec<u8>> = (0..8).map(|i| pattern(60_000 + i * 500, 200 + i as u64)).collect();
        let (mut ao, mut bo) = (vec![0usize; 32], vec![0usize; 8]);
        let (mut a_fin, mut b_fin) = (vec![false; 32], vec![false; 8]);
        let ok = net.run(net.now + 600 * SEC, |n| {
            for (i, id) in a_ids.iter().enumerate() {
                while ao[i] < a_data[i].len() {
                    let k = n.a.conn.write(*id, &a_data[i][ao[i]..]).unwrap();
                    if k == 0 {
                        break;
                    }
                    ao[i] += k;
                }
                if ao[i] == a_data[i].len() && !a_fin[i] {
                    n.a.conn.finish(*id).unwrap();
                    a_fin[i] = true;
                }
            }
            for (i, id) in b_ids.iter().enumerate() {
                while bo[i] < b_data[i].len() {
                    let k = n.b.conn.write(*id, &b_data[i][bo[i]..]).unwrap();
                    if k == 0 {
                        break;
                    }
                    bo[i] += k;
                }
                if bo[i] == b_data[i].len() && !b_fin[i] {
                    n.b.conn.finish(*id).unwrap();
                    b_fin[i] = true;
                }
            }
            a_ids.iter().all(|id| n.b.fin.contains(id)) && b_ids.iter().all(|id| n.a.fin.contains(id))
        });
        if !ok {
            let missing_a: Vec<_> = a_ids
                .iter()
                .enumerate()
                .filter(|(_, id)| !net.b.fin.contains(id))
                .map(|(i, id)| (*id, ao[i], net.b.read.get(id).map_or(0, Vec::len)))
                .collect();
            let missing_b: Vec<_> = b_ids
                .iter()
                .enumerate()
                .filter(|(_, id)| !net.a.fin.contains(id))
                .map(|(i, id)| (*id, bo[i], net.a.read.get(id).map_or(0, Vec::len)))
                .collect();
            panic!(
                "streams did not all finish: a {missing_a:?} b {missing_b:?} status {:?} {:?} chunk {:?}",
                net.a.conn.recv_status(3),
                net.a.conn.recv_status(7),
                net.a.conn.read_chunk(3).map(<[u8]>::len)
            );
        }
        for (i, id) in a_ids.iter().enumerate() {
            assert!(net.b.read[id] == a_data[i], "stream {id} differs");
        }
        for (i, id) in b_ids.iter().enumerate() {
            assert!(net.a.read[id] == b_data[i], "stream {id} differs");
        }
    });
}

#[test]
fn flow_control_limits_a_transfer_until_the_reader_reads() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(32, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        net.b.auto_read = false;
        let data = pattern(6 << 20, 33);
        let id = net.a.conn.open_bi().unwrap();
        let mut off = 0;
        net.run(net.now + 5 * SEC, |n| {
            while off < data.len() {
                let k = n.a.conn.write(id, &data[off..]).unwrap();
                if k == 0 {
                    break;
                }
                off += k;
            }
            false
        });
        let window = 1_310_720u64;
        let held = net.b.conn.pool().used_bytes();
        assert!(
            held <= window + 16 * 1024,
            "the receiver holds {held} bytes against a window of {window}"
        );
        assert!(
            off as u64 <= 2 * window + (1 << 20),
            "the sender buffered {off} bytes past the window"
        );
        assert!(net.b.fin.is_empty() && !net.b.read.contains_key(&id));
        // Reading opens the window again and the rest flows.
        net.b.auto_read = true;
        let mut finished = false;
        let ok = net.run(net.now + 120 * SEC, |n| {
            n.b.read_stream(n.now, id);
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
            n.b.fin.contains(&id)
        });
        assert!(ok);
        assert!(net.b.read[&id] == data);
    });
}

#[test]
fn datagrams_are_unreliable_and_ordered_per_packet() {
    big_stack(|| {
        for (seed, loss) in [(41u64, 0.0), (42, 10.0)] {
            let mut w = World::new(IdentityAlg::Ed25519);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = setup(
                &mut w,
                &mut sa,
                &mut sb,
                Link::new(seed, Params::new(5 * MS).loss(loss)),
            );
            assert!(net.connect(net.now + 10 * SEC));
            let max = net.a.conn.max_datagram_size();
            assert!(matches!(
                net.a.conn.send_datagram(&vec![0; max + 1]),
                Err(DatagramError::TooLarge { .. })
            ));
            for i in 0..200u32 {
                let mut d = pattern(800, u64::from(i));
                d[..4].copy_from_slice(&i.to_be_bytes());
                net.a.conn.send_datagram(&d).unwrap();
                net.run(net.now + MS, |_| false);
            }
            net.run(net.now + 2 * SEC, |_| false);
            let got = &net.b.dgrams;
            let mut last = None;
            for d in got {
                let i = u32::from_be_bytes(d[..4].try_into().unwrap());
                assert!(
                    d.len() == 800 && d[4..] == pattern(800, u64::from(i))[4..],
                    "datagram {i} is corrupt"
                );
                assert!(last.is_none_or(|l| i > l), "datagram {i} repeated or reordered");
                last = Some(i);
            }
            if loss == 0.0 {
                assert_eq!(got.len(), 200);
            } else {
                assert!(got.len() > 120 && got.len() < 200, "{} datagrams arrived", got.len());
            }
            assert_eq!(net.a.conn.stats().packets_lost > 0, loss > 0.0);
        }
    });
}

#[test]
fn extension_frames_reach_the_endpoint_layer() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(43, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        assert!(net.a.conn.send_extension(0x10, b"too low").is_err());
        for i in 0..3u8 {
            net.a
                .conn
                .send_extension(ext::TEST_FIRST + u64::from(i), &[i; 100])
                .unwrap();
        }
        net.a.conn.send_extension(0x1_0000, b"large type").unwrap();
        net.a.conn.send_ready();
        assert!(net.run(net.now + 2 * SEC, |n| n.b.saw(|r| *r == Rec::Ready)));
        let got: Vec<_> = net
            .b
            .log
            .iter()
            .filter_map(|r| {
                if let Rec::Extension(t, b) = r {
                    Some((*t, b.clone()))
                } else {
                    None
                }
            })
            .collect();
        assert_eq!(got.len(), 4);
        assert_eq!(got[0], (ext::TEST_FIRST, vec![0; 100]));
        assert_eq!(got[2], (ext::TEST_LAST, vec![2; 100]));
        assert_eq!(got[3], (0x1_0000, b"large type".to_vec()));
    });
}

#[test]
fn gso_batches_same_size_datagrams() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.max_gso = 8;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(51, Params::new(5 * MS).loss(1.0)));
        assert!(net.connect(net.now + 10 * SEC));
        let data = pattern(4 << 20, 52);
        bulk(&mut net, &data, 120 * SEC);
        let batched = net.a.tx_log.iter().filter(|t| t.1 > 2 * 1200).count();
        assert!(
            batched > 100,
            "full-size datagrams to one path travel in batches: {batched}"
        );
        assert!(
            net.a.tx_log.iter().all(|t| t.1 <= 8 * 1452),
            "no batch exceeds the configured count"
        );
    });
}

#[test]
fn the_handshake_timer_backs_off_and_caps() {
    big_stack(|| {
        // A client that hears nothing: retransmits at max(500 ms, 2 x RTT), doubling up to max(16 s, 4 x RTT), 8 s when thin.
        for (thin, remembered, expect) in [(false, None, 6u64), (true, None, 8), (false, Some(SEC), 4)] {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.cfg.thin = thin;
            w.cfg.remembered_rtt = remembered;
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut link = Link::new(53, Params::new(10 * MS));
            link.route(PathId(1)).up = false;
            let mut net = setup(&mut w, &mut sa, &mut sb, link);
            net.run(net.now + 40 * SEC, |_| false);
            assert_eq!(
                net.a.conn.stats().handshake_retransmits,
                expect,
                "thin {thin} remembered {remembered:?}"
            );
            assert!(!net.a.conn.is_connected());
        }
    });
}

#[test]
fn a_lost_first_flight_is_sent_again() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(54, Params::new(10 * MS));
        link.route(PathId(1)).ab.drop_next(2);
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        assert!(net.connect(net.now + 10 * SEC));
        assert_eq!(net.a.conn.stats().handshake_retransmits, 1);
        assert!(net.now - T0 >= 500 * MS);
    });
}

#[test]
fn a_reset_drops_the_buffers_of_the_stream() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(55, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &[1; 10_000]).unwrap();
        net.run(net.now + 100 * MS, |_| false);
        net.a.conn.reset(id, 77).unwrap();
        assert!(net.run(net.now + 2 * SEC, |n| n.b.saw(|r| *r == Rec::Reset(id, 77))));
    });
}

#[test]
fn rejected_resumption_falls_back_and_sends_early_data_again() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        // The server forgot its tickets: the Hello is rejected and a full handshake follows.
        *w.stores = Stores::default();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(56, Params::new(10 * MS)), &mut w.stores);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"sent early, sent again").unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(net.run(net.now + 20 * SEC, |n| n.b.fin.contains(&id)));
        assert_eq!(net.b.read[&id], b"sent early, sent again");
        assert!(net.a.saw(|r| *r == Rec::Connected(false)) && net.b.saw(|r| *r == Rec::Connected(false)));
    });
}

/// A full handshake that also collects the resumption tickets.
fn first_session(w: &mut World) -> vinc_security::ClientTickets<8> {
    let (mut sa, mut sb) = (Store::new(true), Store::new(false));
    let mut net = setup(w, &mut sa, &mut sb, Link::new(4, Params::new(10 * MS)));
    assert!(net.connect(net.now + 10 * SEC));
    assert!(
        net.run(net.now + 5 * SEC, |n| !n.a.tickets.is_empty()),
        "no tickets arrived"
    );
    std::mem::take(&mut net.a.tickets)
}

#[test]
fn short_initial_hit_and_miss() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        first_session(&mut w);
        // Hit: the server cached our prekey during the first session.
        w.short = true;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(5, Params::new(10 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        assert!(
            net.a.tx_log.iter().take(2).all(|t| t.1 < 600),
            "a short Initial hit sends no full-size flight: {:?}",
            net.a.tx_log
        );
        drop(net);
        // Miss: a server that never saw the prekey rejects the short form, and the client falls back to the full one.
        let mut w2 = World::new(IdentityAlg::Ed25519);
        w2.short = true;
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w2, &mut sa, &mut sb, Link::new(6, Params::new(10 * MS)));
        assert!(net.connect(net.now + 10 * SEC));
        assert!(
            net.a.tx_log.iter().take(4).any(|t| t.1 >= 1200),
            "the fallback is a full-size flight: {:?}",
            net.a.tx_log
        );
    });
}

#[test]
fn resumption_delivers_zero_rtt_data() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut net = Net::new(a, b, Link::new(7, Params::new(10 * MS)), &mut w.stores);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"early bytes").unwrap();
        net.a.conn.finish(id).unwrap();
        // The data arrives with the first flight, one way delay after the start, before the handshake completes.
        let deadline = net.now + 10 * MS + MS / 2;
        net.run(deadline, |n| n.b.fin.contains(&id));
        assert_eq!(net.b.read.get(&id).map(Vec::as_slice), Some(&b"early bytes"[..]));
        assert!(!net.a.conn.is_connected());
        assert!(net.connect(net.now + 5 * SEC));
        assert!(net.a.saw(|r| *r == Rec::Connected(true)) && net.b.saw(|r| *r == Rec::Connected(true)));
        // The early packets were acknowledged, so the sender has nothing left in flight.
        net.run(net.now + SEC, |_| false);
        assert!(net.a.conn.recovery().bytes_in_flight() == 0);
    });
}

#[test]
fn zero_rtt_data_that_overtakes_the_hello_waits_for_its_keys() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut link = Link::new(9, Params::new(10 * MS));
        // The datagram with the Hello arrives 5 ms after the 0-RTT datagrams sent right behind it.
        link.route(PathId(1)).ab.delay_index(1, 5 * MS);
        let mut net = Net::new(a, b, link, &mut w.stores);
        let data = pattern(3000, 1);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &data).unwrap();
        net.a.conn.finish(id).unwrap();
        let t0 = net.now;
        assert!(
            net.run(t0 + 16 * MS, |n| n.b.fin.contains(&id)),
            "the 0-RTT data waited for a retransmission: {:?}",
            net.rx_drops
        );
        assert_eq!(net.b.read[&id], data);
        assert!(net.b.conn.stats().early_buffered >= 1);
        assert_eq!(net.b.conn.stats().early_dropped, 0);
    });
}

#[test]
fn an_answer_that_overtakes_the_resume_reply_waits_for_its_keys() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
        let b = w.server(&mut sb);
        let mut link = Link::new(10, Params::new(10 * MS));
        // The server's first datagram (the Reply) arrives 5 ms after the answer sent right behind it.
        link.route(PathId(1)).ba.delay_index(1, 5 * MS);
        let mut net = Net::new(a, b, link, &mut w.stores);
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"ping").unwrap();
        net.a.conn.finish(id).unwrap();
        let t0 = net.now;
        let mut answered = false;
        let ok = net.run(t0 + 26 * MS, |n| {
            if !answered && n.b.fin.contains(&id) {
                n.b.conn.write(id, b"pong").unwrap();
                n.b.conn.finish(id).unwrap();
                answered = true;
            }
            n.a.fin.contains(&id)
        });
        assert!(ok, "the answer waited for a retransmission: {:?}", net.rx_drops);
        assert_eq!(net.a.read[&id], b"pong");
        assert!(net.a.conn.stats().early_buffered >= 1);
        assert!(net.a.conn.session().unwrap().resumed);
    });
}

#[test]
fn zero_rtt_replay_is_rejected() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut tickets = first_session(&mut w);
        let ticket = tickets.take(&w.rp.id.node_id(), ALPN, T0).unwrap();
        let first_flight = std::rc::Rc::new(std::cell::RefCell::new(Vec::<Vec<u8>>::new()));
        {
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let a = w.client(&mut sa, Some(ticket), vinc_security::ClientTickets::new());
            let b = w.server(&mut sb);
            let mut net = Net::new(a, b, Link::new(8, Params::new(10 * MS)), &mut w.stores);
            let id = net.a.conn.open_bi().unwrap();
            net.a.conn.write(id, b"pay once").unwrap();
            net.a.conn.finish(id).unwrap();
            let rec = first_flight.clone();
            net.on_tx = Some(Box::new(move |is_a, d, now| {
                if is_a && now == T0 {
                    rec.borrow_mut().push(d.to_vec());
                }
            }));
            assert!(net.connect(net.now + 5 * SEC));
            assert!(net.run(net.now + SEC, |n| n.b.fin.contains(&id)));
            assert_eq!(net.b.read[&id], b"pay once");
        }
        let flight = first_flight.borrow().clone();
        assert!(!flight.is_empty());
        // An attacker replays the first flight to a fresh server sharing the same ticket store.
        let mut sb = Store::new(false);
        let mut b = w.server(&mut sb);
        for mut d in flight {
            let _ = b.with_env(T0 + 5 * SEC, |c, env| {
                c.handle_datagram_with(env, &mut w.stores, PathId(2), &mut d)
            });
        }
        b.service(T0 + 5 * SEC);
        assert!(b.read.is_empty(), "replayed early data must not be delivered");
        assert!(!b.connected());
        assert!(!b.saw(|r| matches!(r, Rec::Opened(_) | Rec::Readable(_))));
        // The server answered the replay with a rejection, not a session.
        let mut out = vec![0u8; 2048];
        let reply = b.with_env(T0 + 5 * SEC, |c, env| c.poll_transmit(env, &mut out));
        assert!(
            reply.is_some_and(|t| t.len < 400),
            "a short reject, not a handshake reply"
        );
    });
}

#[test]
fn a_lost_middle_fragment_of_a_handshake_flight_is_all_that_is_missing() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::MlDsa65);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = Link::new(57, Params::new(10 * MS));
        link.route(PathId(1)).ba.drop_index(3);
        let mut net = setup(&mut w, &mut sa, &mut sb, link);
        let sent = std::rc::Rc::new(std::cell::RefCell::new(Vec::<Vec<u8>>::new()));
        let rec = sent.clone();
        net.on_tx = Some(Box::new(move |is_a, d, _| {
            if !is_a {
                rec.borrow_mut().push(d.to_vec());
            }
        }));
        net.run(net.now + 200 * MS, |_| false);
        let flight = sent.borrow().clone();
        assert!(flight.len() >= 5, "the reply spans several datagrams: {}", flight.len());
        assert!(!net.a.conn.is_connected());
        // The reply is larger than three times the client's first flight, so the server's first copy stops short
        // of the end (the amplification limit counts 48 bytes per datagram) and the rest follows the client's
        // retransmission. The lost datagram, delivered late, fills the hole in the middle.
        let mut lost = flight[2].clone();
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.handle_datagram(env, PathId(1), &mut lost))
            .unwrap();
        assert!(
            net.connect(net.now + 2 * SEC),
            "the flight completes after one retransmission"
        );
        assert_eq!(net.a.conn.stats().handshake_retransmits, 1);
    });
}

#[test]
fn key_answers_may_come_several_polls_later() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(58, Params::new(10 * MS)));
        net.a.auto_keys = false;
        net.b.auto_keys = false;
        // Whoever has a request waits; the other side's timers keep running meanwhile.
        for _ in 0..8 {
            net.run(net.now + 5 * SEC, |n| {
                n.a.deferred.is_some() || n.b.deferred.is_some() || (n.a.conn.is_connected() && n.b.conn.is_connected())
            });
            net.run(net.now + 300 * MS, |_| false);
            let now = net.now;
            if net.a.deferred.is_some() {
                net.a.deliver_deferred(now).unwrap();
            }
            if net.b.deferred.is_some() {
                net.b.deliver_deferred(now).unwrap();
            }
            if net.a.conn.is_connected() && net.b.conn.is_connected() {
                break;
            }
        }
        assert!(net.connect(net.now + 5 * SEC));
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, b"after slow keys").unwrap();
        net.a.conn.finish(id).unwrap();
        assert!(net.run(net.now + 2 * SEC, |n| n.b.fin.contains(&id)));
    });
}

#[test]
fn a_failed_key_answer_closes_with_a_typed_reason() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(59, Params::new(10 * MS)));
        net.a.auto_keys = false;
        net.a.fail_keys = true;
        assert!(net.run(net.now + 5 * SEC, |n| n.a.deferred.is_some()));
        net.run(net.now + 200 * MS, |_| false);
        let now = net.now;
        assert_eq!(net.a.deliver_deferred(now), Err(vinc_security::Failure::KeyOperation));
        net.a.service(now);
        assert_eq!(
            net.a.closed(),
            Some(CloseReason::Handshake(vinc_security::Failure::KeyOperation))
        );
        assert!(net.a.conn.is_closed());
    });
}
