//! The 3-byte packet number end to end: a granted window above 40 MB selects it, and a transfer long enough to pass
//! packet number 2^16 still delivers every byte.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::manual_assert_eq // a failing comparison of megabytes must not print them
)]

use std::cell::RefCell;
use std::rc::Rc;

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::credit_for_streams;
use pinc_transport::stream;

/// Chunk-ring slots per stream: 2600 x 16 KiB holds a window of 42 MB, above the 4 MiB of the default harness.
const WIDE_RING: usize = 2600;
/// The granted window: just above the 40 MB at which the packet number grows to 3 bytes.
const WINDOW: u64 = 41_000_000;
/// Pool chunks: the table clamps a window to half the pool.
const WIDE_CHUNKS: usize = 10_240;
/// Enough data for more than 2^16 packets from A at 1452 bytes per datagram.
const BULK: usize = 100_000_000;

fn wide(client: bool) -> Store<WIDE_RING> {
    let mut cfg = stream::Config::new(client);
    cfg.initial_stream_window = WINDOW;
    cfg.max_stream_window = WINDOW;
    Store::sized(WIDE_CHUNKS, &cfg)
}

#[test]
fn a_window_above_40_mb_selects_the_3_byte_packet_number_and_a_long_transfer_delivers_every_byte() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let mut scfg = stream::Config::new(false);
        scfg.initial_stream_window = WINDOW;
        w.cfg.credit = credit_for_streams(&scfg);
        let (mut sa, mut sb) = (wide(true), wide(false));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(31, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
        assert!(net.a.conn.peer_credit().window_bytes() > 40_000_000);
        net.run(net.now + 2 * SEC, |_| false);

        // Short header (1 + 4 id + 3 packet number), the frame (type, stream id, 100 bytes), then the tag.
        let log: Rc<RefCell<Vec<(bool, usize)>>> = Rc::default();
        let sink = log.clone();
        net.on_tx = Some(Box::new(move |is_a, d, _| sink.borrow_mut().push((is_a, d.len()))));
        let id = net.a.conn.open_bi().unwrap();
        net.a.conn.write(id, &[0x42u8; 100]).unwrap();
        net.run(net.now + 200 * MS, |_| false);
        assert!(
            log.borrow()
                .iter()
                .any(|(is_a, len)| *is_a && *len == 1 + 4 + 3 + (1 + 1 + 100) + 16),
            "no data packet with a 3-byte packet number"
        );
        net.on_tx = None;

        let data = pattern(BULK, 77);
        let (_, _) = bulk(&mut net, &data, 3600 * SEC);
        let sent = net.a.conn.stats().datagrams_sent;
        assert!(
            sent > 1 << 16,
            "only {sent} datagrams: the packet numbers did not pass 2^16"
        );
    });
}
