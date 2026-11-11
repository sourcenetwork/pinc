//! A long clean path: the packets in flight are bounded by the congestion window and the stream window, not by the
//! size of the table of sent packets. A 150 ms round trip at 200 Mbit/s, the facade's sizes: a 32 MiB transfer on one
//! stream at the rate the stream window allows.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::manual_assert_eq // a failing comparison of megabytes must not print them
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::{DEFAULT_SEND_WINDOW, credit_for_streams};
use vinc_transport::recovery::SENT_PACKETS;
use vinc_transport::stream::{self, DEFAULT_INITIAL_WINDOW};

/// Chunk-ring entries per stream half of the facade: one more than the chunks of the default window.
const RING_FACADE: usize = 81;
/// Pool chunks: the table clamps a window to half the pool.
const CHUNKS_FACADE: usize = 1024;
const TRANSFER: usize = 32 << 20;

fn store(client: bool) -> Store<RING_FACADE, SENT_PACKETS> {
    Store::sized(CHUNKS_FACADE, &stream::Config::new(client))
}

#[test]
fn a_150_ms_200_mbit_path_runs_at_the_rate_the_stream_window_allows() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&stream::Config::new(false));
        let (mut sa, mut sb) = (store(true), store(false));
        let mut link = Params::new(75 * MS);
        link.bps = 200_000_000;
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, link));
        assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
        assert_eq!(net.a.conn.peer_credit().window_bytes(), DEFAULT_INITIAL_WINDOW);
        let data = pattern(TRANSFER, 5);
        let (elapsed, _) = bulk(&mut net, &data, 600 * SEC);
        // The stream window over the round trip is 8.7 MB/s; a table of 128 sent packets holds 186 KB per round trip,
        // 1.2 MB/s, and takes 27 s for this transfer. Half the window's rate is 8 s including the slow start.
        assert!(
            elapsed < 8 * SEC,
            "32 MiB took {} ms, the window allows 8.7 MB/s (3.9 s and the slow start)",
            elapsed / MS
        );
    });
}

/// `streams` bidirectional streams of `each` bytes sent at once from A; the time until B has every byte of all of them.
fn many_streams(streams: usize, each: usize, send_window: u64) -> u64 {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.send_window = send_window;
    w.cfg.credit = credit_for_streams(&stream::Config::new(false));
    // The facade's default pool: 512 chunks of 16 KiB.
    let mut sa = Store::<RING_FACADE, SENT_PACKETS>::sized(512, &stream::Config::new(true));
    let mut sb = Store::<RING_FACADE, SENT_PACKETS>::sized(512, &stream::Config::new(false));
    let mut link = Params::new(75 * MS);
    link.bps = 200_000_000;
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, link));
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    let data = pattern(each, 9);
    let ids: Vec<u64> = (0..streams).map(|_| net.a.conn.open_bi().unwrap()).collect();
    let mut off = vec![0usize; streams];
    let mut ended = vec![false; streams];
    let start = net.now;
    let finished = net.run(net.now + 600 * SEC, |n| {
        for (k, id) in ids.iter().enumerate() {
            while off[k] < data.len() {
                let end = (off[k] + 64 * 1024).min(data.len());
                let w = n.a.conn.write(*id, &data[off[k]..end]).unwrap();
                if w == 0 {
                    break;
                }
                off[k] += w;
            }
            if off[k] == data.len() && !ended[k] {
                n.a.conn.finish(*id).unwrap();
                ended[k] = true;
            }
        }
        ids.iter().all(|id| n.b.fin.contains(id))
    });
    assert!(finished, "not every stream finished");
    for id in &ids {
        assert!(net.b.read[id] == data, "bytes differ on stream {id}");
    }
    net.now - start
}

#[test]
fn the_send_window_bounds_the_streams_together_and_a_raised_one_lets_them_fill_the_congestion_window() {
    big_stack(|| {
        // 16 streams of 2 MiB: the 32 MiB of the single stream. With the default send window the written data waiting
        // for acknowledgement is 1.25 MiB at most, one window per round trip: 3.9 s and the slow start. With 8 MiB
        // the streams together fill the congestion window, up to the 200 Mbit/s of the path.
        let default = many_streams(16, 2 << 20, DEFAULT_SEND_WINDOW);
        assert!(
            (3800 * MS..8 * SEC).contains(&default),
            "32 MiB over 16 streams took {} ms with the default send window",
            default / MS
        );
        let raised = many_streams(16, 2 << 20, 8 << 20);
        assert!(
            raised < 3500 * MS,
            "32 MiB over 16 streams took {} ms with 8 MiB",
            raised / MS
        );
    });
}

#[test]
fn the_facades_default_pool_carries_every_stream_the_connection_opens() {
    big_stack(|| {
        // 32 streams open at once with 1 MiB each, each granted the 1.25 MiB window: none is refused and all arrive.
        let elapsed = many_streams(32, 1 << 20, DEFAULT_SEND_WINDOW);
        assert!(elapsed < 8 * SEC, "32 MiB over 32 streams took {} ms", elapsed / MS);
    });
}
