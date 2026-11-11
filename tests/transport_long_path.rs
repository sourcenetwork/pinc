//! Long clean paths at the facade's defaults: the packets in flight are bounded by the congestion window and the
//! windows of the streams, not by the table of sent packets, the send window or the pool. A 150 ms round trip at
//! 200 Mbit/s and at 1 Gbit/s, one stream and 16, with the facade's sizes.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_precision_loss,
    clippy::manual_assert_eq // a failing comparison of megabytes must not print them
)]

use vinc_crypto::IdentityAlg;
use vinc_security::CreditRecord;
use vinc_tests::*;
use vinc_transport::recovery::SENT_PACKETS;
use vinc_transport::stream;

/// `streams` streams of `each` bytes at once from A on a clean path of `rtt_ms` round trip at `bps`, with the sizes of
/// the facade and the limits `limits`; the virtual time until B has every byte.
fn transfer(bps: u64, rtt_ms: u64, streams: usize, each: usize, limits: vinc::Limits) -> u64 {
    let mut w = World::new(IdentityAlg::Ed25519);
    w.cfg.send_window = limits.send_window;
    w.cfg.credit = CreditRecord::new(limits.stream_window, limits.streams, u16::MAX);
    let mut sa = Store::<{ vinc::RING }, SENT_PACKETS>::sized(limits.pool_chunks, &stream::Config::new(true));
    let mut sb = Store::<{ vinc::RING }, SENT_PACKETS>::sized(limits.pool_chunks, &stream::Config::new(false));
    let mut link = Params::new(rtt_ms * MS / 2);
    link.bps = bps;
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
                let end = (off[k] + 256 * 1024).min(data.len());
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

fn mib_s(total: usize, elapsed: u64) -> f64 {
    (total as f64 / 1_048_576.0) / (elapsed as f64 / 1e9)
}

/// Before the send window, the stream windows and the pool were raised these took 6.7, 6.9, 7.6 and 7.9 MiB/s: one
/// window of data per round trip, 1.25 MiB over 150 ms. The link allows 23.8 MiB/s and 119 MiB/s, and the transfers
/// are short enough for the slow start to take a good part of them.
#[test]
fn the_facade_defaults_fill_long_paths() {
    big_stack(|| {
        let l = vinc::Limits::default;
        for (bps, total, one, many, label) in [
            (200_000_000u64, 32usize << 20, 10.0, 10.0, "200 Mbit/s"),
            (1_000_000_000, 128 << 20, 16.0, 32.0, "1 Gbit/s"),
        ] {
            for (streams, floor) in [(1usize, one), (16, many)] {
                let elapsed = transfer(bps, 150, streams, total / streams, l());
                let rate = mib_s(total, elapsed);
                assert!(
                    rate >= floor,
                    "{label} 150 ms, {streams} streams: {rate:.1} MiB/s, expected at least {floor}"
                );
            }
        }
    });
}

/// The transport's default is the reference's cap, and the facade's is not: the same 16 streams on the same path.
#[test]
fn the_transports_send_window_is_the_references_and_the_facades_lets_the_congestion_window_bind() {
    use vinc_transport::conn::{Config, DEFAULT_SEND_WINDOW};
    big_stack(|| {
        assert_eq!(DEFAULT_SEND_WINDOW, 1_310_720);
        assert_eq!(Config::new().send_window, DEFAULT_SEND_WINDOW);
        assert_eq!(vinc::Limits::default().send_window, 16 << 20);
        let reference = vinc::Limits {
            send_window: DEFAULT_SEND_WINDOW,
            ..vinc::Limits::default()
        };
        let held = transfer(200_000_000, 150, 16, 2 << 20, reference);
        let free = transfer(200_000_000, 150, 16, 2 << 20, vinc::Limits::default());
        // 1.25 MiB over 150 ms is 8.3 MiB/s: 32 MiB take 3.8 s and the slow start.
        assert!(
            held >= 3800 * MS,
            "32 MiB over 16 streams took {} ms with a send window of 1.25 MiB",
            held / MS
        );
        assert!(
            held * 3 >= free * 4,
            "the facade's default took {} ms against {} ms",
            free / MS,
            held / MS
        );
    });
}

#[test]
fn the_default_pool_carries_every_stream_the_connection_opens() {
    big_stack(|| {
        // 32 streams of 1 MiB at once, each granted the window of 1.25 MiB: none is refused and all arrive.
        let elapsed = transfer(200_000_000, 150, 32, 1 << 20, vinc::Limits::default());
        assert!(elapsed < 4 * SEC, "32 MiB over 32 streams took {} ms", elapsed / MS);
    });
}
