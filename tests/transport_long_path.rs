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
use vinc_transport::conn::credit_for_streams;
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
