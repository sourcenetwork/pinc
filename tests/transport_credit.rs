//! Stream credit end to end: an opener that opens far more streams than the receiver's pool holds waits for the
//! credit instead of sending them, every stream arrives with its bytes, and the receiver holds none back; a frame that
//! opens many silent streams at once is admitted; a stream that ends gives the opener one more while every other one
//! stays live; the configured window is the one advertised and the one the streams run with; and, on a table, a
//! window charged to the ledger from its stream's first byte, with streams admitted while a first charge fits.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;
use vinc_transport::conn::credit_for_streams;
use vinc_transport::stream;
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use vinc_transport::stream::{ControlFrame, StreamError};

type Table = stream::Streams<stream::NoSource, 8, 1025>;

/// A server table with the stream credit on and windows of `window` chunks, over a pool of `chunks`.
fn table(chunks: usize, window: u64) -> (BufferPool<'static>, Box<Table>) {
    let pool = BufferPool::new_boxed(chunks);
    let mut cfg = stream::Config::new(false);
    cfg.initial_stream_window = window * CHUNK_SIZE as u64;
    cfg.peer = stream::PeerLimits {
        window: 1 << 20,
        max_streams: 100,
    };
    let t = Box::new(Table::new(&cfg, &pool));
    (pool, t)
}

/// Read a stream to its end and let it see the end; returns the bytes read.
fn read_to_end(t: &mut Table, pool: &mut BufferPool<'_>, id: u64) -> usize {
    let mut n = 0;
    while let Some(c) = t.read_chunk(pool, id) {
        let k = c.len();
        n += k;
        t.consume(pool, id, k, 0, 0).unwrap();
    }
    t.consume(pool, id, 0, 0, 0).unwrap();
    n
}

/// Streams the opener wants open in all; the receiver's pool holds the windows of a few.
const STREAMS: usize = 60;
/// Bytes on each.
const LEN: usize = 3000;

fn config(client: bool) -> stream::Config {
    let mut cfg = stream::Config::new(client);
    cfg.initial_stream_window = 64 * 1024;
    cfg.max_stream_window = 64 * 1024;
    cfg
}

#[test]
fn an_opener_far_beyond_the_credit_delivers_every_stream_and_the_receiver_holds_none_back() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&config(false));
        // The receiver's pool is 16 chunks: it tells the opener it admits a few to start, fewer than the streams wanted.
        let (mut sa, mut sb) = (
            Store::<RING>::sized(256, &config(true)),
            Store::<RING>::sized(16, &config(false)),
        );
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(41, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
        net.run(net.now + SEC, |_| false);
        let first = net.a.conn.peer_credit().max_streams;
        assert!(
            first > 0 && usize::from(first) < STREAMS,
            "the handshake credit is {first}"
        );

        let mut opened: Vec<u64> = Vec::new();
        let mut waited = 0usize;
        let done = net.run(net.now + 600 * SEC, |n| {
            while opened.len() < STREAMS {
                let ready = n.a.conn.open_ready(false);
                match n.a.conn.open_uni() {
                    Ok(id) => {
                        assert_eq!(ready, Ok(()), "open_ready said no to an open that worked");
                        let k = opened.len();
                        let data = pattern(LEN, 1000 + k as u64);
                        assert_eq!(n.a.conn.write(id, &data).unwrap(), LEN);
                        n.a.conn.finish(id).unwrap();
                        opened.push(id);
                    }
                    Err(e) => {
                        assert_eq!(ready, Err(e), "open_ready disagrees with the open");
                        waited += 1;
                        break;
                    }
                }
            }
            opened.len() == STREAMS && opened.iter().all(|id| n.b.fin.contains(id))
        });
        assert!(done, "opened {} of {STREAMS}", opened.len());
        assert!(
            waited > 0,
            "the opener never had to wait for credit: the test does not exercise it"
        );
        for (k, id) in opened.iter().enumerate() {
            assert!(net.b.read[id] == pattern(LEN, 1000 + k as u64), "stream {id} differs");
        }
        assert_eq!(net.b.conn.stats().held_back, 0, "the receiver held a stream back");
    });
}

/// The opener has as many streams live as the credit allows, each with data on it and none finished. One of them ends
/// on both sides: the receiver raises the credit by that one stream and the opener opens another.
#[test]
fn a_stream_that_ends_gives_the_opener_one_more_while_every_other_stream_stays_live() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        w.cfg.credit = credit_for_streams(&config(false));
        let (mut sa, mut sb) = (
            Store::<RING>::sized(1024, &config(true)),
            Store::<RING>::sized(1024, &config(false)),
        );
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(47, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
        net.run(net.now + SEC, |_| false);
        let credit = usize::from(net.a.conn.peer_credit().max_streams);
        assert_eq!(credit, 32, "half the slots of the table");
        let ids: Vec<u64> = (0..credit).map(|_| net.a.conn.open_bi().unwrap()).collect();
        for id in &ids {
            assert_eq!(net.a.conn.write(*id, &[7]).unwrap(), 1);
        }
        assert_eq!(net.a.conn.open_bi(), Err(StreamError::StreamLimit));
        let all = net.run(net.now + 10 * SEC, |n| ids.iter().all(|id| n.b.read.contains_key(id)));
        assert!(all, "the receiver saw {} of {credit} streams", net.b.read.len());
        net.run(net.now + SEC, |_| false);
        assert_eq!(net.a.conn.open_ready(true), Err(StreamError::StreamLimit));

        let last = *ids.last().unwrap();
        net.a.conn.finish(last).unwrap();
        net.b.conn.finish(last).unwrap();
        let again = net.run(net.now + 10 * SEC, |n| n.a.conn.open_ready(true).is_ok());
        assert!(
            again,
            "the stream ended and no credit came back: {:?}",
            net.a.conn.open_ready(true)
        );
        let id = net.a.conn.open_bi().unwrap();
        assert_eq!(net.a.conn.write(id, &[8]).unwrap(), 1);
        let seen = net.run(net.now + 10 * SEC, |n| n.b.read.contains_key(&id));
        assert!(seen, "the new stream did not arrive");
        assert_eq!(net.b.conn.stats().held_back, 0, "the receiver held a stream back");
    });
}

/// The window in the credit record an endpoint is configured with is the window its streams run with: the one its
/// peer is told, the one it enforces and the one it counts. A window far under the default delivers a stream many
/// windows long (the grants follow the reader), and a window above the default is advertised whole.
#[test]
fn the_configured_stream_window_is_the_one_advertised_and_the_one_the_streams_run_with() {
    big_stack(|| {
        const LONG: usize = 1 << 20;
        for window in [64 * 1024u64, 2 << 20] {
            let mut w = World::new(IdentityAlg::Ed25519);
            w.cfg.credit = vinc_security::CreditRecord::new(window, 100, u16::MAX);
            let (mut sa, mut sb) = (Store::new(true), Store::new(false));
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(53, Params::new(5 * MS)));
            assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
            net.run(net.now + SEC, |_| false);
            assert_eq!(
                net.a.conn.peer_credit().window_bytes(),
                window,
                "the window the opener was told"
            );
            let id = net.a.conn.open_uni().unwrap();
            let data = pattern(LONG, 9);
            let (mut sent, mut ended) = (0, false);
            let done = net.run(net.now + 60 * SEC, |n| {
                while sent < LONG {
                    let k = n.a.conn.write(id, &data[sent..]).unwrap();
                    if k == 0 {
                        break;
                    }
                    sent += k;
                }
                if sent == LONG && !ended {
                    n.a.conn.finish(id).unwrap();
                    ended = true;
                }
                n.b.fin.contains(&id)
            });
            assert!(
                done,
                "a window of {window}: {sent} of {LONG} bytes written, the stream did not end"
            );
            assert!(net.b.read[&id] == data, "the stream's bytes differ");
        }
    });
}

/// A frame for a high stream index opens every skipped lower index at once. The skipped streams cost the pool only what
/// the ledger counts for a stream that has not carried data, which the credit already set aside: nothing is refused.
#[test]
fn a_first_frame_on_the_highest_of_many_streams_opens_the_silent_ones_below_it_without_a_refusal() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        // A pool of 128 chunks: the default window is cut to half of it (64 chunks), so two windows charged whole fill it.
        let (mut sa, mut sb) = (Store::with_chunks(true, 1024), Store::with_chunks(false, 128));
        let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(43, Params::new(5 * MS)));
        assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
        net.run(net.now + SEC, |_| false);
        let credit = usize::from(net.a.conn.peer_credit().max_streams);
        assert!(credit >= 12, "the handshake credit is {credit}");
        let ids: Vec<u64> = (0..12).map(|_| net.a.conn.open_uni().unwrap()).collect();
        let last = *ids.last().unwrap();
        let data = pattern(LEN, 77);
        assert_eq!(net.a.conn.write(last, &data).unwrap(), LEN);
        net.a.conn.finish(last).unwrap();
        let done = net.run(net.now + 30 * SEC, |n| n.b.fin.contains(&last));
        assert!(done, "the stream with the high index was not delivered");
        assert!(net.b.read[&last] == data, "the stream's bytes differ");
        assert_eq!(net.b.conn.stats().held_back, 0, "a skipped stream was refused");
    });
}

/// The ledger counts the first four chunks of a stream that has carried no data and its whole window from its first
/// byte, and no window is granted while it is past the pool. Admitting a stream asks less: a first charge for it
/// beside one for each open stream. So with streams that carry data and hold the ledger past the pool, a stream of
/// ours still opens and a peer stream beyond the credit is still admitted, until the pool has no first charge left.
#[test]
fn a_window_is_charged_from_its_first_byte_and_a_stream_is_admitted_while_a_first_charge_fits() {
    let chunk = CHUNK_SIZE as u64;
    // Windows of 16 chunks against a pool of 32: charged at admission, two streams would fill it.
    let (mut pool, mut t) = table(32, 16);
    assert_eq!(
        t.advertised_streams(),
        4,
        "eight first charges fit: half of them, and 4 of the 8 slots"
    );
    t.on_stream_frame(&mut pool, 0, 0, &[1], false).unwrap();
    assert_eq!(
        t.granted_unreceived(),
        15 * chunk,
        "the whole window less the chunk it holds"
    );
    // The second window does not fit beside the first and the credit left; its bytes are stored all the same.
    t.on_stream_frame(&mut pool, 4, 0, &[2], false).unwrap();
    // A frame on index 3 opens index 2 as well, inside the credit: admitted, the silent one counted at four chunks.
    t.on_stream_frame(&mut pool, 12, 0, &[3], false).unwrap();
    assert_eq!(t.open_streams(), 4);
    assert_eq!(t.granted_unreceived(), (3 * 15 + 4) * chunk);
    assert!(
        t.granted_unreceived() > pool.available_bytes(),
        "the ledger is past the pool"
    );
    assert_eq!(t.stats().held_back, 0);
    // A stream of ours opens all the same: four open streams count a first charge each (16 chunks), and a fifth
    // first charge fits the 29 chunks the pool has left.
    let mut ours = vec![t.open_stream(&pool, true).unwrap()];
    // The credit is not raised: the peer has as many streams live as it may.
    t.regrant(&pool);
    assert!(std::iter::from_fn(|| t.pending_control()).all(|f| !matches!(f, ControlFrame::MaxStreams { .. })));
    // A peer stream beyond the credit is admitted too, while its first charge fits.
    t.on_stream_frame(&mut pool, 16, 0, &[4], false).unwrap();
    assert_eq!(t.stats().held_back, 0);
    // Six open streams count 24 chunks and the pool has 28 left: one more of ours fits, and then none does.
    ours.push(t.open_stream(&pool, true).unwrap());
    assert_eq!(t.open_stream(&pool, true), Err(StreamError::Exhausted));
    assert_eq!(
        t.on_stream_frame(&mut pool, 20, 0, &[5], false),
        Err(StreamError::Exhausted),
        "a stream beyond the credit with no first charge left is held back"
    );
    assert_eq!(t.stats().held_back, 1);
    // The silent stream stores what arrives while chunks are free.
    t.on_stream_frame(&mut pool, 8, 0, &[5; 1000], false).unwrap();
    // The streams end and are read, our halves end too: the ledger drains and the credit is raised.
    let peers = [(0u64, 1usize), (4, 1), (8, 1000), (12, 1), (16, 1)];
    for (id, len) in peers.into_iter().chain(ours.into_iter().map(|id| (id, 0))) {
        t.on_stream_frame(&mut pool, id, len as u64, &[], true).unwrap();
        assert_eq!(read_to_end(&mut t, &mut pool, id), len);
        t.finish(id).unwrap();
    }
    while let Some(c) = t.next_stream_frame(1200) {
        let mut buf = vec![0u8; c.len];
        t.copy_out(&pool, &c, &mut buf).unwrap();
        t.on_acked(&mut pool, c.id, c.offset, c.len as u64, c.fin);
    }
    assert_eq!(t.open_streams(), 0);
    assert_eq!(t.granted_unreceived(), 0);
    t.regrant(&pool);
    let raise = std::iter::from_fn(|| t.pending_control()).find_map(|f| match f {
        ControlFrame::MaxStreams { limit } => Some(limit),
        _ => None,
    });
    assert_eq!(raise, Some(9), "five admitted and room for four more");
    t.on_stream_frame(&mut pool, 20, 0, &[5], false).unwrap();
    assert_eq!(t.stats().held_back, 1);
}
