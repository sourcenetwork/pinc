//! The transport stream layer: reassembly, receive windows charged to the pool, the rate-sized window, urgency order,
//! the send buffer cap, source-backed streams, stream caps and resets, with the pool accounting checked at every end.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::large_stack_arrays,
    clippy::assert_is_empty,
    clippy::items_after_statements
)]

use std::cell::RefCell;

use proptest::prelude::*;
use vinc_tests::{SplitMix64, measure};
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use vinc_transport::stream::{
    Config, ControlFrame, NoSource, PeerLimits, RecvStatus, StreamChunk, StreamError, StreamSource, Streams,
};

vinc_tests::install_counting_allocator!();

const MIB: u64 = 1 << 20;
/// A send buffer cap that never binds.
const NO_CAP: u64 = u64::MAX;
type Table = Streams<NoSource, 8, 1025>;

fn peer() -> PeerLimits {
    PeerLimits {
        window: 5 * MIB / 4,
        max_streams: 100,
    }
}

/// A server-side table over a heap pool of `chunks` chunks.
fn setup(chunks: usize, edit: impl FnOnce(&mut Config)) -> (BufferPool<'static>, Box<Table>) {
    let pool = BufferPool::new_boxed(chunks);
    let mut config = Config::new(false);
    config.peer = peer();
    // These tests exercise the pool and window rules on their own; the stream credit has its own tests.
    config.credit = false;
    edit(&mut config);
    let table = Box::new(Table::new(&config, &pool));
    (pool, table)
}

/// A server-side table with the stream credit on, over a heap pool of `chunks` chunks.
fn setup_credit(chunks: usize, edit: impl FnOnce(&mut Config)) -> (BufferPool<'static>, Box<Table>) {
    setup(chunks, |c| {
        c.credit = true;
        edit(c);
    })
}

/// The next control frame, the stream-credit raises (see the credit tests) left out.
fn next_control<S: StreamSource, const N: usize, const C: usize>(t: &mut Streams<S, N, C>) -> Option<ControlFrame> {
    std::iter::from_fn(|| t.pending_control()).find(|f| !matches!(f, ControlFrame::MaxStreams { .. }))
}

fn pattern(len: usize, seed: u64) -> Vec<u8> {
    let mut v = vec![0u8; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

/// Read and consume everything readable on `id`.
fn read_all<S: StreamSource, const N: usize, const C: usize>(
    t: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    id: u64,
) -> Vec<u8> {
    let mut out = Vec::new();
    while let Some(chunk) = t.read_chunk(pool, id) {
        let n = chunk.len();
        out.extend_from_slice(chunk);
        t.consume(pool, id, n, 0, 0).unwrap();
    }
    out
}

/// Every control frame the table wants to send, the stream-credit raises left out (see `credit_raises`).
fn drain_control(t: &mut Table) -> Vec<ControlFrame> {
    std::iter::from_fn(|| t.pending_control())
        .filter(|f| !matches!(f, ControlFrame::MaxStreams { .. }))
        .collect()
}

/// Build every frame the table wants to send now, copying out the data.
fn drain_frames(t: &mut Table, pool: &BufferPool<'_>, budget: usize) -> Vec<(StreamChunk, Vec<u8>)> {
    let mut frames = Vec::new();
    while let Some(chunk) = t.next_stream_frame(budget) {
        let mut buf = vec![0u8; chunk.len];
        assert_eq!(t.copy_out(pool, &chunk, &mut buf).unwrap(), chunk.len);
        frames.push((chunk, buf));
    }
    frames
}

// ---- receive ------------------------------------------------------------------------------------------------------

#[test]
fn in_order_data_is_read_back_and_chunks_return() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let data = pattern(50_000, 1);
    for (i, part) in data.chunks(1400).enumerate() {
        let off = (i * 1400) as u64;
        t.on_stream_frame(&mut pool, 0, off, part, off + part.len() as u64 == data.len() as u64)
            .unwrap();
    }
    assert_eq!(pool.used_chunks(), 4);
    assert_eq!(read_all(&mut t, &mut pool, 0), data);
    assert_eq!(t.recv_status(0), Some(RecvStatus::Finished));
    assert_eq!(
        pool.used_chunks(),
        0,
        "the final chunk returns when the end is consumed"
    );
    // The application observes the end; the receive half closes.
    assert_eq!(t.consume(&mut pool, 0, 0, 0, 0), Ok(RecvStatus::Finished));
}

#[test]
fn the_reader_sees_bytes_at_most_one_chunk_at_a_time() {
    let (mut pool, mut t) = setup(1024, |_| {});
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; 3 * CHUNK_SIZE], false)
        .unwrap();
    assert_eq!(t.read_chunk(&pool, 0).unwrap().len(), CHUNK_SIZE);
    assert_eq!(t.consume(&mut pool, 0, CHUNK_SIZE + 10, 0, 0), Ok(RecvStatus::Open));
    assert_eq!(pool.used_chunks(), 2, "the fully consumed chunk is freed");
    assert_eq!(t.read_chunk(&pool, 0).unwrap().len(), CHUNK_SIZE - 10);
    assert_eq!(
        t.consume(&mut pool, 0, 5 * CHUNK_SIZE, 0, 0),
        Err(StreamError::InvalidConsume)
    );
}

#[test]
fn out_of_order_data_waits_for_the_hole() {
    let (mut pool, mut t) = setup(1024, |_| {});
    t.on_stream_frame(&mut pool, 0, 1000, &[2; 500], false).unwrap();
    assert!(t.read_chunk(&pool, 0).is_none());
    t.on_stream_frame(&mut pool, 0, 0, &[1; 1000], false).unwrap();
    let all = read_all(&mut t, &mut pool, 0);
    assert_eq!(all.len(), 1500);
    assert!(all[..1000].iter().all(|&b| b == 1) && all[1000..].iter().all(|&b| b == 2));
}

proptest! {
    /// Any permutation of overlapping and duplicated segments is read back exactly once, in order.
    #[test]
    fn reassembly_matches_the_model(len in 1usize..60_000, seed in any::<u64>(), extra in 0usize..30) {
        let (mut pool, mut t) = setup(1024, |_| {});
        let data = pattern(len, seed);
        let mut rng = SplitMix64::new(seed ^ 0xABCD);
        let mut segs: Vec<(usize, usize)> = Vec::new();
        let mut at = 0;
        while at < len {
            let end = (at + 1 + rng.next_u64() as usize % 9000).min(len);
            segs.push((at, end));
            at = end;
        }
        for _ in 0..extra {
            let a = rng.next_u64() as usize % len;
            let b = (a + 1 + rng.next_u64() as usize % 12_000).min(len);
            segs.push((a, b));
        }
        for _ in 0..extra / 2 {
            let pick = segs[rng.next_u64() as usize % segs.len()];
            segs.push(pick);
        }
        for i in (1..segs.len()).rev() {
            segs.swap(i, rng.next_u64() as usize % (i + 1));
        }
        let mut queue: std::collections::VecDeque<_> = segs.into();
        let mut out = Vec::new();
        let mut guard = 0;
        while let Some((a, b)) = queue.pop_front() {
            guard += 1;
            prop_assert!(guard < 100_000);
            match t.on_stream_frame(&mut pool, 0, a as u64, &data[a..b], b == len) {
                Ok(()) => {}
                // Too many holes right now: the peer would retransmit it later.
                Err(StreamError::Fragmented) => queue.push_back((a, b)),
                Err(e) => prop_assert!(false, "unexpected {e}"),
            }
            out.extend(read_all(&mut t, &mut pool, 0));
        }
        prop_assert_eq!(out, data);
        prop_assert_eq!(t.recv_status(0), Some(RecvStatus::Finished));
        prop_assert_eq!(pool.used_chunks(), 0);
    }
}

#[test]
fn conflicting_overlap_is_detected_and_changes_nothing() {
    let (mut pool, mut t) = setup(1024, |_| {});
    t.on_stream_frame(&mut pool, 0, 0, &[1; 100], false).unwrap();
    let mut bad = vec![1u8; 100];
    bad[10] = 9;
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 50, &bad, false),
        Err(StreamError::Conflict)
    );
    // A faithful overlap extends the stream.
    t.on_stream_frame(&mut pool, 0, 50, &[1; 100], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0), vec![1; 150]);
}

#[test]
fn conflict_inside_a_hole_neighbour_is_detected() {
    let (mut pool, mut t) = setup(1024, |_| {});
    t.on_stream_frame(&mut pool, 0, 100, &[5; 50], false).unwrap();
    let mut spanning = vec![7u8; 100];
    spanning[..].fill(7);
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 80, &spanning, false),
        Err(StreamError::Conflict)
    );
    t.on_stream_frame(&mut pool, 0, 0, &[0; 100], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 150);
}

#[test]
fn final_size_rules() {
    let (mut pool, mut t) = setup(1024, |_| {});
    t.on_stream_frame(&mut pool, 0, 0, &[1; 100], true).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 100, &[1; 10], false),
        Err(StreamError::FinalSize)
    );
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 0, &[1; 90], true),
        Err(StreamError::FinalSize)
    );
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 0, &[1; 110], true),
        Err(StreamError::FinalSize)
    );
    assert_eq!(t.on_reset_stream(&mut pool, 0, 3, 99), Err(StreamError::FinalSize));
    assert_eq!(t.on_reset_stream(&mut pool, 0, 3, 101), Err(StreamError::FinalSize));
    // A fin below data already seen.
    t.on_stream_frame(&mut pool, 4, 0, &[1; 100], false).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 4, 0, &[1; 50], true),
        Err(StreamError::FinalSize)
    );
    // A reset below data already seen.
    assert_eq!(t.on_reset_stream(&mut pool, 4, 3, 50), Err(StreamError::FinalSize));
}

#[test]
fn stream_credit_is_enforced() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 4096);
    t.on_stream_frame(&mut pool, 0, 0, &[1; 4096], false).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 4096, &[1; 1], false),
        Err(StreamError::FlowControl)
    );
    assert_eq!(
        t.on_stream_frame(&mut pool, 4, 4000, &[1; 97], false),
        Err(StreamError::FlowControl)
    );
    assert_eq!(t.on_reset_stream(&mut pool, 8, 0, 4097), Err(StreamError::FlowControl));
}

#[test]
fn an_empty_pool_refuses_data_without_storing_any() {
    let (mut pool, mut t) = setup(4, |_| {});
    t.on_stream_frame(&mut pool, 0, 0, &[], false).unwrap();
    let hog: Vec<_> = (0..3).map(|_| pool.alloc_chunk().unwrap()).collect();
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 0, &vec![1; CHUNK_SIZE + 5], false),
        Err(StreamError::Exhausted)
    );
    assert_eq!(pool.used_chunks(), 3);
    assert!(t.read_chunk(&pool, 0).is_none());
    for c in hog {
        pool.free_chunk(c);
    }
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; CHUNK_SIZE + 5], false)
        .unwrap();
}

#[test]
fn a_grant_waits_for_pool_room_and_is_issued_when_the_pool_gives_it_back() {
    // 16 chunks: 256 KiB. Windows of 64 KiB.
    let (mut pool, mut t) = setup(16, |c| c.initial_stream_window = 64 * 1024);
    assert_eq!(t.recv_window(), 64 * 1024);
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; 48 * 1024], false).unwrap();
    let hog: Vec<_> = (0..13).map(|_| pool.alloc_chunk().unwrap()).collect();
    // Consuming frees three chunks, but granting 48 KiB more on top of the 16 KiB outstanding needs 64 KiB.
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 48 * 1024);
    assert!(
        drain_control(&mut t).is_empty(),
        "no grant while the pool cannot hold it"
    );
    assert_eq!(t.stream_recv_window(0).unwrap().1, 64 * 1024, "the limit did not move");
    for c in hog {
        pool.free_chunk(c);
    }
    // Room is back (the datagram queues and the early-data buffer give chunks back outside the table): the
    // connection retries before it writes control frames, with nothing left to read.
    t.regrant(&pool);
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::MaxStreamData { id: 0, max: 112 * 1024 }]
    );
    assert!(t.granted_unreceived() <= pool.available_bytes());
}

#[test]
fn a_deferred_grant_is_issued_when_acknowledged_send_data_gives_the_pool_back() {
    // Regression: the grant was retried only after a consume, so a peer blocked at its limit, with nothing left to
    // read, waited forever once the pool refilled by an acknowledgement.
    let (mut pool, mut t) = setup(16, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; 48 * 1024], false).unwrap();
    let sid = t.open_stream(&pool, true).unwrap();
    assert_eq!(
        t.write(&mut pool, sid, &vec![2; 13 * CHUNK_SIZE], NO_CAP).unwrap(),
        13 * CHUNK_SIZE
    );
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 48 * 1024);
    assert!(
        drain_control(&mut t).is_empty(),
        "no grant while the send buffer holds the pool"
    );
    let sent = drain_frames(&mut t, &pool, 1 << 20);
    assert!(!sent.is_empty());
    for (c, _) in &sent {
        t.on_acked(&mut pool, c.id, c.offset, c.len as u64, c.fin);
    }
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::MaxStreamData { id: 0, max: 112 * 1024 }],
        "the acknowledgement freed the pool, so the grant goes without a read"
    );
    assert!(t.granted_unreceived() <= pool.available_bytes());
}

#[test]
fn credit_is_charged_in_whole_chunks_including_the_holes_below_the_highest_byte() {
    // Windows of 64 KiB: four chunks. One byte in the last chunk makes the highest byte 64 KiB, so a charge by bytes
    // beyond it would be zero, while the three chunks below it are credit that can still claim the pool.
    let (mut pool, mut t) = setup(16, |c| c.initial_stream_window = 64 * 1024);
    let chunk = CHUNK_SIZE as u64;
    assert_eq!(t.granted_unreceived(), 0, "a stream not opened yet holds no credit");
    t.on_stream_frame(&mut pool, 0, 64 * 1024 - 1, &[1], false).unwrap();
    assert_eq!(t.granted_unreceived(), 3 * chunk);
    // A few bytes at the start claim their whole chunk.
    t.on_stream_frame(&mut pool, 0, 5, &[1; 10], false).unwrap();
    assert_eq!(t.granted_unreceived(), 2 * chunk);
    assert!(t.granted_unreceived() <= pool.available_bytes());
    // Read everything that arrived in order: the chunk is released, the window moves on, still covered by the pool.
    t.on_stream_frame(&mut pool, 0, 0, &[1; 5], false).unwrap();
    t.on_stream_frame(&mut pool, 0, 15, &vec![1; 64 * 1024 - 16], false)
        .unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 64 * 1024);
    drain_control(&mut t);
    assert!(t.granted_unreceived() <= pool.available_bytes());
}

#[test]
fn a_peer_stream_whose_window_does_not_fit_the_pool_is_held_back() {
    let (mut pool, mut t) = setup(12, |c| c.initial_stream_window = 96 * 1024);
    // The ledger counts 64 KiB for a new stream: two fit in 192 KiB less a stored chunk, three do not.
    t.on_stream_frame(&mut pool, 0, 0, &[1; 10], false).unwrap();
    t.on_stream_frame(&mut pool, 4, 0, &[], false).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 8, 0, &[], false),
        Err(StreamError::Exhausted)
    );
    assert_eq!(t.open_streams(), 2);
    assert!(drain_control(&mut t).is_empty(), "a held-back stream is not answered");
    assert!(t.granted_unreceived() <= pool.available_bytes());
}

#[test]
fn a_held_back_peer_stream_is_admitted_once_room_returns_with_its_bytes_intact() {
    // The ledger counts 64 KiB for each stream: in a pool of 8 chunks our own stream and the first of theirs fit, the
    // second of theirs is held back (unacknowledged, so the opener retransmits it from the start), but the same streams
    // fit a pool that has the room.
    let (mut pool, mut t) = setup(8, |_| {});
    // This side opens a stream of its own at the same moment (its receive half is granted a window too).
    let own = t.open_stream(&pool, true).unwrap();
    let theirs = own ^ 1;
    t.on_stream_frame(&mut pool, theirs, 0, &[1; 10], true).unwrap();
    let held = pattern(30_000, 7);
    for _ in 0..3 {
        assert_eq!(
            t.on_stream_frame(&mut pool, theirs + 4, 0, &held, true),
            Err(StreamError::Exhausted),
            "every try is held back while there is no room, and each stores nothing"
        );
    }
    assert!(drain_control(&mut t).is_empty());
    assert_eq!(t.open_streams(), 2);
    assert_eq!(read_all(&mut t, &mut pool, theirs).len(), 10);
    // The first stream is done and gave its grant back: the retransmitted stream is admitted, once, with every byte.
    t.on_stream_frame(&mut pool, theirs + 4, 0, &held, true).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, theirs + 4), held);
    let (mut roomy, mut t) = setup(1024, |_| {});
    let own = t.open_stream(&roomy, true).unwrap();
    t.on_stream_frame(&mut roomy, own ^ 1, 0, &[1; 10], false).unwrap();
    t.on_stream_frame(&mut roomy, (own ^ 1) + 4, 0, &[2; 10], false)
        .unwrap();
    assert_eq!(t.open_streams(), 3);
}

// ---- receive windows ------------------------------------------------------------------------------------------

#[test]
fn max_stream_data_is_sent_after_an_eighth_of_the_window() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let window = 1_310_720u64;
    let eighth = (window / 8) as usize;
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; eighth + 100], false)
        .unwrap();
    // srtt 0 keeps the meter idle, so only the 1/8 rule is visible.
    t.consume(&mut pool, 0, eighth - 1, 10, 0).unwrap();
    assert!(drain_control(&mut t).is_empty());
    t.consume(&mut pool, 0, 1, 10, 0).unwrap();
    let frames = drain_control(&mut t);
    let credit = eighth as u64 + window;
    assert_eq!(frames, [ControlFrame::MaxStreamData { id: 0, max: credit }]);
    assert!(drain_control(&mut t).is_empty());
    // The new limit is usable at once and a lost frame is queued again.
    t.on_stream_frame(
        &mut pool,
        0,
        eighth as u64 + 100,
        &vec![1; window as usize - 100],
        false,
    )
    .unwrap();
    t.on_control_lost(&frames[0]);
    assert_eq!(drain_control(&mut t), [frames[0]]);
}

#[test]
fn a_grant_is_bounded_by_the_final_size() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; 40_000], true).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 40_000);
    assert!(
        drain_control(&mut t).is_empty(),
        "no credit is needed beyond the final size"
    );
}

/// Feed and consume stream 0 in 512 KiB steps so that `per_srtt` steps are consumed per round trip; returns the
/// window size at the end.
fn rate_run(per_srtt: u64) -> u64 {
    let (mut pool, mut t) = setup(4096, |_| {});
    let srtt = 1_200_000u64;
    let step = 512 * 1024u64;
    let mut sent = 0u64;
    let mut sizes = vec![t.stream_recv_window(0).map_or(1_310_720, |w| w.0)];
    t.on_stream_frame(&mut pool, 0, 0, &[], false).unwrap();
    // The first consume starts the epoch.
    t.consume(&mut pool, 0, 0, 0, srtt).unwrap();
    for k in 1..=(8 * per_srtt) {
        let limit = t.stream_recv_window(0).unwrap().1;
        assert!(sent + step <= limit, "the peer must have credit while we read promptly");
        t.on_stream_frame(&mut pool, 0, sent, &vec![7; step as usize], false)
            .unwrap();
        sent += step;
        let now = k * srtt / per_srtt;
        while let Some(chunk) = t.read_chunk(&pool, 0) {
            let len = chunk.len();
            t.consume(&mut pool, 0, len, now, srtt).unwrap();
        }
        drain_control(&mut t);
        sizes.push(t.stream_recv_window(0).unwrap().0);
    }
    assert!(sizes.windows(2).all(|w| w[0] <= w[1]), "the window never shrinks");
    assert!(
        t.granted_unreceived() <= pool.available_bytes(),
        "grants stay within the pool"
    );
    *sizes.last().unwrap()
}

#[test]
fn a_fast_reader_raises_the_window_to_twice_its_rate() {
    // 12 steps of 512 KiB per round trip is 6 MiB per round trip: the window is 12 MiB.
    assert_eq!(rate_run(12), 12 * MIB);
}

#[test]
fn the_window_never_passes_the_ceiling() {
    // 10 MiB per round trip would ask for 20 MiB; the ceiling is 16 MiB.
    assert_eq!(rate_run(20), 16 * MIB);
}

#[test]
fn a_slowly_consumed_window_does_not_grow() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let rtt = 1_000u64;
    let mut sent = 0u64;
    let mut now = 0u64;
    while sent < 4 * MIB {
        t.on_stream_frame(&mut pool, 0, sent, &[1; 65_536], false).unwrap();
        sent += 65_536;
        now += 10 * rtt;
        while let Some(chunk) = t.read_chunk(&pool, 0) {
            let len = chunk.len();
            t.consume(&mut pool, 0, len, now, rtt).unwrap();
        }
        drain_control(&mut t);
    }
    assert_eq!(t.stream_recv_window(0).unwrap().0, 1_310_720);
    assert_eq!(t.recv_window(), 1_310_720);
}

// ---- send ---------------------------------------------------------------------------------------------------------

#[test]
fn write_is_bounded_by_the_peer_window() {
    let (mut pool, mut t) = setup(1024, |c| c.peer.window = 5000);
    let id = t.open_stream(&pool, true).unwrap();
    assert_eq!(id, 1);
    assert_eq!(t.write(&mut pool, id, &[1; 8000], NO_CAP).unwrap(), 5000);
    assert!(drain_control(&mut t).is_empty(), "nothing is sent about a full window");
    assert_eq!(t.write(&mut pool, id, &[1; 10], NO_CAP).unwrap(), 0);
    assert_eq!(
        t.poll_writable(NO_CAP),
        None,
        "a cut by the window is woken by the peer"
    );
    t.on_max_stream_data(&pool, id, 20_000).unwrap();
    assert_eq!(t.write(&mut pool, id, &[1; 10_000], NO_CAP).unwrap(), 10_000);
    t.finish(id).unwrap();
    assert_eq!(t.write(&mut pool, id, &[1], NO_CAP), Err(StreamError::Finished));
}

#[test]
fn write_is_bounded_by_the_buffer_cap_and_acks_wake_the_writer() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let a = t.open_stream(&pool, true).unwrap();
    let b = t.open_stream(&pool, true).unwrap();
    assert_eq!(t.write(&mut pool, a, &[1; 5000], 3000).unwrap(), 3000);
    assert_eq!(t.buffered(), 3000);
    assert_eq!(t.write(&mut pool, a, &[1; 10], 3000).unwrap(), 0);
    assert_eq!(
        t.write(&mut pool, b, &[1; 10], 3000).unwrap(),
        0,
        "the cap is connection wide"
    );
    assert_eq!(t.poll_writable(3000), None, "no room yet");
    let frames = drain_frames(&mut t, &pool, 1000);
    assert_eq!(frames.len(), 3);
    t.on_acked(&mut pool, a, 0, 1000, false);
    assert_eq!(t.buffered(), 2000);
    let woken = [t.poll_writable(3000), t.poll_writable(3000), t.poll_writable(3000)];
    assert_eq!(woken.iter().flatten().count(), 2, "both cut streams wake once");
    assert!(woken[0].is_some() && woken[1].is_some() && woken[2].is_none());
    assert_eq!(t.write(&mut pool, b, &[1; 5000], 3000).unwrap(), 1000);
    assert_eq!(t.buffered(), 3000);
    // A reset gives the room back.
    t.reset(&mut pool, a, 1).unwrap();
    assert_eq!(t.buffered(), 1000);
    t.close_all(&mut pool);
    assert_eq!(t.buffered(), 0);
}

#[test]
fn a_cap_of_zero_room_accepts_nothing() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    assert_eq!(t.write(&mut pool, id, &[1; 10], 0).unwrap(), 0);
    assert_eq!(t.poll_writable(0), None);
    assert_eq!(t.poll_writable(1), Some(id));
}

#[test]
fn write_stops_when_the_pool_is_empty() {
    let (mut pool, mut t) = setup(2, |_| {});
    let id = t.open_stream(&pool, false).unwrap();
    assert_eq!(
        t.write(&mut pool, id, &vec![1; 3 * CHUNK_SIZE], NO_CAP).unwrap(),
        2 * CHUNK_SIZE
    );
    assert_eq!(t.write(&mut pool, id, &[1], NO_CAP).unwrap(), 0);
    assert_eq!(pool.available_chunks(), 0);
}

#[test]
fn lost_ranges_go_first_lowest_hole_first() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    let data = pattern(6000, 3);
    t.write(&mut pool, id, &data, NO_CAP).unwrap();
    let frames = drain_frames(&mut t, &pool, 1000);
    assert_eq!(frames.len(), 6);
    assert!(frames.iter().all(|(_, d)| !d.is_empty()));
    let at = |i: usize| (frames[i].0.offset, frames[i].0.len as u64);
    // Loss reports arrive out of order; the retransmission order is by offset.
    t.on_lost(id, at(3).0, at(3).1, false);
    t.on_lost(id, at(1).0, at(1).1, false);
    t.write(&mut pool, id, &pattern(500, 4), NO_CAP).unwrap();
    let first = t.next_stream_frame(1000).unwrap();
    let second = t.next_stream_frame(1000).unwrap();
    let third = t.next_stream_frame(1000).unwrap();
    assert_eq!(
        (first.offset, second.offset, third.offset),
        (1000, 3000, 6000),
        "retransmissions precede new data"
    );
    let mut buf = vec![0u8; 1000];
    t.copy_out(&pool, &first, &mut buf).unwrap();
    assert_eq!(buf, data[1000..2000]);
    // Adjacent losses merge and are cut by the budget, lowest first.
    t.on_lost(id, 1000, 1000, false);
    t.on_lost(id, 2000, 1000, false);
    let a = t.next_stream_frame(1200).unwrap();
    let b = t.next_stream_frame(1200).unwrap();
    assert_eq!((a.offset, a.len, b.offset, b.len), (1000, 1200, 2200, 800));
}

#[test]
fn a_late_ack_cancels_the_queued_retransmission() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    t.write(&mut pool, id, &pattern(3000, 5), NO_CAP).unwrap();
    assert_eq!(drain_frames(&mut t, &pool, 1000).len(), 3);
    t.on_lost(id, 1000, 1000, false);
    t.on_late_acked(&mut pool, id, 1000, 1000, false);
    assert!(t.next_stream_frame(1000).is_none());
    // A partial late ack leaves the rest queued.
    t.on_lost(id, 0, 1000, false);
    t.on_late_acked(&mut pool, id, 0, 400, false);
    let rest = t.next_stream_frame(1000).unwrap();
    assert_eq!((rest.offset, rest.len), (400, 600));
}

#[test]
fn acked_data_returns_its_chunks_and_a_finished_stream_closes() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, false).unwrap();
    let data = pattern(3 * CHUNK_SIZE + 100, 6);
    assert_eq!(t.write(&mut pool, id, &data, NO_CAP).unwrap(), data.len());
    t.finish(id).unwrap();
    assert_eq!(pool.used_chunks(), 4);
    let frames = drain_frames(&mut t, &pool, 1400);
    assert!(frames.last().unwrap().0.fin);
    assert_eq!(frames.iter().filter(|(c, _)| c.fin).count(), 1);
    let rebuilt: Vec<u8> = frames.iter().flat_map(|(_, d)| d.clone()).collect();
    assert_eq!(rebuilt, data);
    // Acknowledge out of order: chunks free only as the prefix grows.
    for (c, _) in frames.iter().rev() {
        t.on_acked(&mut pool, c.id, c.offset, c.len as u64, c.fin);
    }
    assert_eq!(pool.used_chunks(), 0);
    assert_eq!(
        t.open_streams(),
        0,
        "a unidirectional stream closes once its end is acknowledged"
    );
}

#[test]
fn a_lost_end_marker_is_sent_again_on_its_own() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, false).unwrap();
    t.write(&mut pool, id, &[1; 100], NO_CAP).unwrap();
    let frames = drain_frames(&mut t, &pool, 1000);
    t.on_acked(&mut pool, id, 0, 100, false);
    t.finish(id).unwrap();
    let fin = t.next_stream_frame(1000).unwrap();
    assert_eq!((fin.offset, fin.len, fin.fin), (100, 0, true));
    assert!(t.next_stream_frame(1000).is_none());
    t.on_lost(id, fin.offset, 0, true);
    assert_eq!(t.next_stream_frame(1000), Some(fin));
    t.on_acked(&mut pool, id, 100, 0, true);
    assert_eq!(t.open_streams(), 0);
    assert_eq!(frames.len(), 1);
}

#[derive(Debug)]
struct Src<'a> {
    data: &'a [u8],
    log: &'a RefCell<Vec<(u64, usize)>>,
}

impl StreamSource for Src<'_> {
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
        self.log.borrow_mut().push((offset, dst.len()));
        let start = offset as usize;
        let n = dst.len().min(self.data.len().saturating_sub(start));
        dst[..n].copy_from_slice(&self.data[start..start + n]);
        n
    }
}

#[test]
fn a_source_backed_stream_buffers_nothing_and_rereads_lost_ranges() {
    let data = pattern(5000, 8);
    let log = RefCell::new(Vec::new());
    let mut pool = BufferPool::new_boxed(8);
    let mut config = Config::new(false);
    config.peer = peer();
    let mut t = Box::new(Streams::<Src<'_>, 4, 65>::new(&config, &pool));
    let id = t.open_stream(&pool, false).unwrap();
    t.open_source(id, Src { data: &data, log: &log }, data.len() as u64)
        .unwrap();
    assert_eq!(t.write(&mut pool, id, &[1], NO_CAP), Err(StreamError::WrongKind));
    let mut sent = Vec::new();
    let mut buf = [0u8; 1500];
    while let Some(chunk) = t.next_stream_frame(1200) {
        let n = t.copy_out(&pool, &chunk, &mut buf).unwrap();
        sent.push((chunk, buf[..n].to_vec()));
        assert_eq!(pool.used_chunks(), 0, "a source-backed stream holds no chunk");
    }
    let rebuilt: Vec<u8> = sent.iter().flat_map(|(_, d)| d.clone()).collect();
    assert_eq!(rebuilt, data);
    assert_eq!(
        sent.iter().map(|(c, _)| (c.offset, c.len, c.fin)).collect::<Vec<_>>(),
        [
            (0, 1200, false),
            (1200, 1200, false),
            (2400, 1200, false),
            (3600, 1200, false),
            (4800, 200, true)
        ]
    );
    let reads_before = log.borrow().len();
    t.on_lost(id, 1200, 1200, false);
    let again = t.next_stream_frame(1200).unwrap();
    assert_eq!((again.offset, again.len), (1200, 1200));
    t.copy_out(&pool, &again, &mut buf).unwrap();
    assert_eq!(&buf[..1200], &data[1200..2400]);
    assert_eq!(log.borrow().len(), reads_before + 1);
    assert_eq!(log.borrow().last(), Some(&(1200, 1200)));
    assert_eq!(pool.used_chunks(), 0);
    // A lost final frame carries the end marker again.
    t.on_lost(id, 4800, 200, true);
    let last = t.next_stream_frame(1200).unwrap();
    assert_eq!((last.offset, last.len, last.fin), (4800, 200, true));
}

#[test]
fn a_short_source_read_requeues_the_range() {
    let data = pattern(1000, 9);
    let log = RefCell::new(Vec::new());
    let mut pool = BufferPool::new_boxed(2);
    let mut config = Config::new(false);
    config.peer = peer();
    let mut t = Box::new(Streams::<Src<'_>, 2, 65>::new(&config, &pool));
    let id = t.open_stream(&pool, false).unwrap();
    // Claim more than the source holds: the second frame's read comes up short.
    t.open_source(id, Src { data: &data, log: &log }, 2000).unwrap();
    let mut buf = [0u8; 1500];
    let first = t.next_stream_frame(1000).unwrap();
    assert!(t.copy_out(&pool, &first, &mut buf).is_ok());
    let second = t.next_stream_frame(1000).unwrap();
    assert_eq!(t.copy_out(&pool, &second, &mut buf), Err(StreamError::DataUnavailable));
    let retry = t.next_stream_frame(1000).unwrap();
    assert_eq!(
        (retry.offset, retry.len, retry.fin),
        (second.offset, second.len, second.fin)
    );
    t.reset(&mut pool, id, 1).unwrap();
}

#[test]
fn source_credit_is_charged_at_first_transmission() {
    let data = pattern(10_000, 10);
    let log = RefCell::new(Vec::new());
    let mut pool = BufferPool::new_boxed(2);
    let mut config = Config::new(false);
    config.peer = peer();
    config.peer.window = 3000;
    let mut t = Box::new(Streams::<Src<'_>, 2, 65>::new(&config, &pool));
    let id = t.open_stream(&pool, false).unwrap();
    t.open_source(id, Src { data: &data, log: &log }, 10_000).unwrap();
    let mut total = 0;
    while let Some(c) = t.next_stream_frame(1200) {
        total += c.len;
    }
    assert_eq!(total, 3000);
    assert!(next_control(&mut t).is_none());
    t.on_lost(id, 0, 1200, false);
    assert_eq!(
        t.next_stream_frame(1200).unwrap().len,
        1200,
        "retransmissions need no credit"
    );
    t.on_max_stream_data(&pool, id, 6000).unwrap();
    assert_eq!(t.next_stream_frame(5000).unwrap().len, 3000);
    let _ = &mut pool;
}

// ---- reset -----------------------------------------------------------------------------------------------

#[test]
fn reset_drops_buffers_and_closes_when_acknowledged() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, false).unwrap();
    t.write(&mut pool, id, &vec![1; 40_000], NO_CAP).unwrap();
    assert!(pool.used_chunks() > 0);
    t.reset(&mut pool, id, 77).unwrap();
    assert_eq!(pool.used_chunks(), 0);
    let frame = next_control(&mut t).unwrap();
    assert_eq!(
        frame,
        ControlFrame::ResetStream {
            id,
            error_code: 77,
            final_size: 40_000
        }
    );
    assert!(t.next_stream_frame(1000).is_none());
    assert_eq!(t.write(&mut pool, id, &[1], NO_CAP), Err(StreamError::Finished));
    t.on_control_lost(&frame);
    assert_eq!(next_control(&mut t), Some(frame));
    assert_eq!(t.open_streams(), 1);
    t.on_control_acked(&mut pool, &frame);
    assert_eq!(t.open_streams(), 0);
}

#[test]
fn a_peer_reset_frees_the_buffer() {
    let (mut pool, mut t) = setup(1024, |_| {});
    t.on_stream_frame(&mut pool, 2, 0, &[1; 30_000], false).unwrap();
    assert!(pool.used_chunks() > 0);
    t.on_reset_stream(&mut pool, 2, 5, 60_000).unwrap();
    assert_eq!(pool.used_chunks(), 0);
    assert_eq!(t.recv_status(2), Some(RecvStatus::Reset(5)));
    assert!(t.read_chunk(&pool, 2).is_none());
    t.on_stream_frame(&mut pool, 2, 30_000, &[1; 10], false).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 2, 60_000, &[1; 1], false),
        Err(StreamError::FinalSize)
    );
    assert_eq!(t.consume(&mut pool, 2, 0, 0, 0), Ok(RecvStatus::Reset(5)));
    assert_eq!(t.open_streams(), 0);
}

// ---- stream ids and limits ----------------------------------------------------------------------------------------

#[test]
fn stream_ids_follow_the_bit_layout() {
    let pool = BufferPool::new_boxed(8);
    let mut client = Config::new(true);
    client.credit = false;
    client.peer = peer();
    let mut c = Box::new(Table::new(&client, &pool));
    let mut server = Config::new(false);
    server.credit = false;
    server.peer = peer();
    let mut s = Box::new(Table::new(&server, &pool));
    assert_eq!([c.open_stream(&pool, true), c.open_stream(&pool, true)], [Ok(0), Ok(4)]);
    assert_eq!(
        [c.open_stream(&pool, false), c.open_stream(&pool, false)],
        [Ok(2), Ok(6)]
    );
    assert_eq!([s.open_stream(&pool, true), s.open_stream(&pool, true)], [Ok(1), Ok(5)]);
    assert_eq!(
        [s.open_stream(&pool, false), s.open_stream(&pool, false)],
        [Ok(3), Ok(7)]
    );
}

#[test]
fn a_stream_over_the_cap_is_held_back_until_one_closes() {
    let (mut pool, mut t) = setup(1024, |c| c.max_streams = 2);
    t.on_stream_frame(&mut pool, 2, 0, &[1; 10], true).unwrap();
    t.on_stream_frame(&mut pool, 6, 0, &[1; 10], false).unwrap();
    let used = pool.used_chunks();
    for _ in 0..2 {
        assert_eq!(
            t.on_stream_frame(&mut pool, 10, 0, &[1; 100], false),
            Err(StreamError::Exhausted)
        );
        assert_eq!(t.on_reset_stream(&mut pool, 10, 0, 0), Err(StreamError::Exhausted));
    }
    assert_eq!(pool.used_chunks(), used, "a held-back stream stores nothing");
    assert_eq!(t.open_streams(), 2);
    assert!(t.read_chunk(&pool, 10).is_none());
    assert!(drain_control(&mut t).is_empty(), "a held-back stream is not answered");
    // Consuming the last byte of the first stream lets the application see the end, which closes it.
    assert_eq!(read_all(&mut t, &mut pool, 2).len(), 10);
    assert_eq!(t.open_streams(), 1);
    // The retransmission is admitted from its first byte.
    t.on_stream_frame(&mut pool, 10, 0, &[7; 100], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 10), [7; 100]);
    // A frame for a closed stream is ignored.
    t.on_stream_frame(&mut pool, 2, 0, &[1; 10], true).unwrap();
    assert_eq!(t.open_streams(), 2);
    assert!(drain_control(&mut t).is_empty());
}

#[test]
fn held_back_streams_cost_the_table_nothing_however_often_they_are_retried() {
    let mut pool = BufferPool::new_boxed(256);
    let mut config = Config::new(false);
    config.initial_stream_window = 16 * 1024;
    config.max_streams = 20;
    config.peer = peer();
    let mut t = Box::new(Streams::<NoSource, 20, 65>::new(&config, &pool));
    // One frame on the 20th stream opens all twenty.
    t.on_stream_frame(&mut pool, 4 * 19, 0, &[1], false).unwrap();
    assert_eq!(t.open_streams(), 20);
    for round in 0..4u64 {
        for n in 0..20u64 {
            assert_eq!(
                t.on_stream_frame(&mut pool, 4 * (20 + n), round, &[1], false),
                Err(StreamError::Exhausted)
            );
        }
    }
    assert!(next_control(&mut t).is_none());
    assert_eq!(t.open_streams(), 20);
}

#[test]
fn a_stream_id_far_beyond_the_next_is_a_violation() {
    let (mut pool, mut t) = setup(1024, |c| {
        c.max_streams = 4;
        c.initial_stream_window = 16 * 1024;
    });
    assert_eq!(
        t.on_stream_frame(&mut pool, 4 * 4, 0, &[1], false),
        Err(StreamError::StreamLimit)
    );
    assert_eq!(t.on_reset_stream(&mut pool, 4 * 5, 0, 0), Err(StreamError::StreamLimit));
    assert!(
        drain_control(&mut t).is_empty(),
        "a violation is not answered with a reset"
    );
    t.on_stream_frame(&mut pool, 4 * 3, 0, &[1], false).unwrap();
    assert_eq!(t.open_streams(), 4, "the lower ids open implicitly");
    // The next is now index 4: indexes below 8 are inside the allowance (but over the cap).
    assert_eq!(
        t.on_stream_frame(&mut pool, 4 * 4, 0, &[1], false),
        Err(StreamError::Exhausted)
    );
    assert_eq!(
        t.on_stream_frame(&mut pool, 4 * 8, 0, &[1], false),
        Err(StreamError::StreamLimit)
    );
}

#[test]
fn frames_for_the_wrong_direction_or_unopened_local_streams_are_errors() {
    let (mut pool, mut t) = setup(1024, |_| {});
    // Stream 3 is server-initiated unidirectional: the peer cannot send on it, and we never opened it.
    assert_eq!(
        t.on_stream_frame(&mut pool, 3, 0, &[1], false),
        Err(StreamError::StreamState)
    );
    assert_eq!(
        t.on_stream_frame(&mut pool, 1, 0, &[1], false),
        Err(StreamError::StreamState)
    );
    // Stream 2 is client-initiated unidirectional: we cannot send on it.
    t.on_stream_frame(&mut pool, 2, 0, &[1], false).unwrap();
    assert_eq!(t.on_max_stream_data(&pool, 2, 100), Err(StreamError::StreamState));
    assert_eq!(t.write(&mut pool, 2, &[1], NO_CAP), Err(StreamError::StreamState));
}

#[test]
fn locally_opened_streams_are_capped_by_the_peer_and_the_cap_grows() {
    let (mut pool, mut t) = setup(8, |c| c.peer.max_streams = 2);
    assert_eq!(t.open_stream(&pool, false), Ok(3));
    assert_eq!(t.open_stream(&pool, true), Ok(1));
    assert_eq!(t.open_stream(&pool, false), Err(StreamError::StreamLimit));
    assert!(drain_control(&mut t).is_empty());
    // A closed stream frees a place.
    t.write(&mut pool, 3, &[1; 10], NO_CAP).unwrap();
    t.finish(3).unwrap();
    let frame = t.next_stream_frame(100).unwrap();
    t.on_acked(&mut pool, 3, frame.offset, frame.len as u64, frame.fin);
    // The place is free, but the peer has given credit for two streams in all: it raises that as its streams end.
    assert_eq!(t.open_stream(&pool, false), Err(StreamError::StreamLimit));
    t.on_max_streams(3);
    assert_eq!(t.open_stream(&pool, false), Ok(7));
    assert_eq!(t.open_stream(&pool, false), Err(StreamError::StreamLimit));
    // Limits only grow.
    t.on_max_streams(1);
    t.set_peer_limits(&PeerLimits {
        window: 1,
        max_streams: 1,
    });
    assert_eq!(t.open_stream(&pool, false), Err(StreamError::StreamLimit));
    t.set_peer_limits(&PeerLimits {
        window: 1,
        max_streams: 4,
    });
    assert_eq!(t.open_stream(&pool, false), Ok(11));
}

#[test]
fn the_table_is_bounded() {
    // A pool that covers the receive window of the eight streams we open.
    let (mut pool, mut t) = setup(1024, |c| c.max_streams = 100);
    // The peer's stream limit is clamped to the table size.
    assert_eq!(
        t.on_stream_frame(&mut pool, 4 * 8, 0, &[1], false),
        Err(StreamError::StreamLimit)
    );
    for _ in 0..8 {
        t.open_stream(&pool, true).unwrap();
    }
    assert_eq!(t.open_stream(&pool, true), Err(StreamError::TableFull));
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 0, &[1], false),
        Err(StreamError::Exhausted),
        "a peer stream finds no slot and is held back"
    );
    assert_eq!(t.open_streams(), 8);
}

#[test]
fn closing_every_stream_returns_every_chunk() {
    let (mut pool, mut t) = setup(1024, |_| {});
    for sid in [0u64, 4, 8] {
        t.on_stream_frame(&mut pool, sid, 5, &pattern(30_000, sid), false)
            .unwrap();
    }
    let a = t.open_stream(&pool, true).unwrap();
    let b = t.open_stream(&pool, false).unwrap();
    t.write(&mut pool, a, &pattern(50_000, 1), NO_CAP).unwrap();
    t.write(&mut pool, b, &pattern(50_000, 2), NO_CAP).unwrap();
    assert!(pool.used_chunks() > 0);
    t.close_all(&mut pool);
    assert_eq!(t.open_streams(), 0);
    assert_eq!(pool.used_chunks(), 0);
}

// ---- urgency ------------------------------------------------------------------------------------------------------

#[test]
fn streams_are_served_in_urgency_then_id_order() {
    let (mut pool, mut t) = setup(1024, |_| {});
    // Ids 1, 5 and 9: (urgency 3, id 1), (3, 5) and (1, 9).
    let ids = [1u64, 5, 9].map(|_| t.open_stream(&pool, true).unwrap());
    assert_eq!(ids, [1, 5, 9]);
    t.set_urgency(9, 1).unwrap();
    assert_eq!(t.set_urgency(99, 1), Err(StreamError::UnknownStream));
    for id in ids {
        t.write(&mut pool, id, &pattern(3000, id), NO_CAP).unwrap();
    }
    let order: Vec<u64> = drain_frames(&mut t, &pool, 1000).iter().map(|(c, _)| c.id).collect();
    assert_eq!(
        order,
        [9, 9, 9, 1, 1, 1, 5, 5, 5],
        "a better stream drains before a worse one starts"
    );
}

#[test]
fn retransmissions_precede_new_data_within_a_stream_and_urgency_beats_both() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let a = t.open_stream(&pool, true).unwrap();
    let b = t.open_stream(&pool, true).unwrap();
    t.set_urgency(b, 5).unwrap();
    t.write(&mut pool, a, &pattern(3000, 1), NO_CAP).unwrap();
    t.write(&mut pool, b, &pattern(3000, 2), NO_CAP).unwrap();
    assert_eq!(drain_frames(&mut t, &pool, 1000).len(), 6);
    // The worse stream loses a range, the better stream gets new data and a loss of its own.
    t.on_lost(b, 0, 1000, false);
    t.on_lost(a, 2000, 1000, false);
    t.on_lost(a, 1000, 1000, false);
    t.write(&mut pool, a, &pattern(500, 3), NO_CAP).unwrap();
    let got: Vec<(u64, u64)> = drain_frames(&mut t, &pool, 1000)
        .iter()
        .map(|(c, _)| (c.id, c.offset))
        .collect();
    assert_eq!(
        got,
        [(a, 1000), (a, 2000), (a, 3000), (b, 0)],
        "retransmissions lowest first, then new data, all before the worse stream"
    );
    // Raising the urgency of the worse stream (a lower number) reorders at once.
    t.on_lost(b, 1000, 1000, false);
    t.on_lost(a, 0, 1000, false);
    t.set_urgency(b, 0).unwrap();
    let got: Vec<u64> = drain_frames(&mut t, &pool, 1000).iter().map(|(c, _)| c.id).collect();
    assert_eq!(got, [b, a]);
}

#[test]
fn a_stream_without_credit_does_not_hold_up_a_worse_one() {
    let data = pattern(10_000, 10);
    let log = RefCell::new(Vec::new());
    let mut pool = BufferPool::new_boxed(8);
    let mut config = Config::new(false);
    config.peer = peer();
    config.peer.window = 2000;
    let mut t = Box::new(Streams::<Src<'_>, 4, 65>::new(&config, &pool));
    let a = t.open_stream(&pool, false).unwrap();
    let b = t.open_stream(&pool, false).unwrap();
    t.set_urgency(a, 0).unwrap();
    t.open_source(a, Src { data: &data, log: &log }, 10_000).unwrap();
    t.open_source(b, Src { data: &data, log: &log }, 1000).unwrap();
    let mut ids = Vec::new();
    while let Some(c) = t.next_stream_frame(1000) {
        ids.push((c.id, c.len));
    }
    assert_eq!(ids, [(a, 1000), (a, 1000), (b, 1000)]);
    let _ = &mut pool;
}

// ---- pool grant property --------------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Op {
    /// An empty frame that opens stream `k` (or does nothing if it exists).
    Open(usize),
    Frame(usize, usize),
    Consume(usize),
    Hog,
    Unhog,
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        (0usize..6).prop_map(Op::Open),
        (0usize..6, 1usize..30_000).prop_map(|(k, n)| Op::Frame(k, n)),
        (0usize..6).prop_map(Op::Consume),
        Just(Op::Hog),
        Just(Op::Unhog),
    ]
}

proptest! {
    /// Whenever a stream is admitted or a window grows, the pool bytes promised to the peer (the credit granted and not
    /// yet received, and the first charges kept for the streams it may still open) fit the pool, or are no more than
    /// they were before the operation: another user of the pool taking chunks (a `Hog`: the send buffers and the datagram
    /// queues do) can put the promises past what is left, and no admission or grant may add to that.
    ///
    /// This is not a weaker guarantee for the peer's data. A frame that arrives inside a granted window when the pool
    /// has no chunk left for it (another holder took it) is refused by `Recv::on_data` as `StreamError::Exhausted`
    /// before anything is stored; the connection treats that as a shortage, drops the packet unacknowledged and counts
    /// it in `held_back`, and the peer sends it again once chunks are free. Nothing is lost, and the pool is never over
    /// its budget.
    #[test]
    fn granted_credit_fits_the_pool_at_every_admission_and_grant(ops in prop::collection::vec(op(), 1..150)) {
        let mut pool = BufferPool::new_boxed(24);
        let mut config = Config::new(false);
        config.initial_stream_window = 48 * 1024;
        config.max_streams = 4;
        config.peer = peer();
        let mut t = Box::new(Table::new(&config, &pool));
        let mut sent = [0u64; 6];
        let mut hogs = Vec::new();
        let mut now = 0u64;
        for op in ops {
            now += 1000;
            let limits = |t: &Table| -> Vec<Option<u64>> {
                (0..6u64).map(|k| t.stream_recv_window(4 * k).map(|w| w.1)).collect()
            };
            let before = limits(&t);
            let opened_before = t.open_streams();
            let promised_before = t.promised();
            match op {
                Op::Open(k) => {
                    match t.on_stream_frame(&mut pool, 4 * k as u64, sent[k], &[], false) {
                        Ok(()) | Err(StreamError::Exhausted | StreamError::StreamLimit) => {}
                        Err(e) => prop_assert!(false, "unexpected {e}"),
                    }
                    if t.open_streams() > opened_before {
                        prop_assert!(t.promised() <= pool.available_bytes().max(promised_before));
                    }
                }
                Op::Frame(k, n) => {
                    let data = vec![1u8; n];
                    match t.on_stream_frame(&mut pool, 4 * k as u64, sent[k], &data, false) {
                        Ok(()) => sent[k] += n as u64,
                        Err(StreamError::Exhausted | StreamError::StreamLimit
                            | StreamError::FlowControl | StreamError::Fragmented) => {}
                        Err(e) => prop_assert!(false, "unexpected {e}"),
                    }
                }
                Op::Consume(k) => {
                    let id = 4 * k as u64;
                    let n = t.read_chunk(&pool, id).map_or(0, <[u8]>::len);
                    let _ = t.consume(&mut pool, id, n, now, 2000);
                    let after = limits(&t);
                    if before.iter().zip(&after).any(|(b, a)| a > b && b.is_some()) {
                        prop_assert!(t.promised() <= pool.available_bytes().max(promised_before));
                    }
                }
                Op::Hog => {
                    if let Ok(c) = pool.alloc_chunk() {
                        hogs.push(c);
                    }
                }
                Op::Unhog => {
                    if let Some(c) = hogs.pop() {
                        pool.free_chunk(c);
                    }
                }
            }
            // Acknowledge refusals so the queue turns over.
            while let Some(f) = next_control(&mut t) {
                if matches!(f, ControlFrame::ResetStream { .. }) {
                    t.on_control_acked(&mut pool, &f);
                }
            }
        }
        t.close_all(&mut pool);
        prop_assert_eq!(pool.used_chunks(), hogs.len());
    }
}

#[test]
fn a_stream_has_data_to_send_while_new_bytes_or_a_retransmission_wait() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    assert!(!t.has_data_to_send());
    t.write(&mut pool, id, &[1u8; 2800], 1 << 20).unwrap();
    assert!(t.has_data_to_send(), "new bytes wait");
    let mut frames = Vec::new();
    while let Some(f) = t.next_stream_frame(1400) {
        frames.push((f.offset, f.len as u64));
    }
    assert_eq!(frames.len(), 2);
    assert!(!t.has_data_to_send(), "everything is sent and nothing is lost");
    t.on_lost(id, frames[0].0, frames[0].1, false);
    assert!(t.has_data_to_send(), "a lost range waits to be sent again");
    let again = t.next_stream_frame(1400).unwrap();
    assert!(!t.has_data_to_send());
    t.on_acked(&mut pool, id, again.offset, again.len as u64, false);
    t.on_acked(&mut pool, id, frames[1].0, frames[1].1, false);
    assert!(!t.has_data_to_send());
}

#[test]
fn sixty_four_holes_of_acknowledged_ranges_are_remembered_without_sending_any_again() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    t.write(&mut pool, id, &[1u8; 1400 * 130], 1 << 20).unwrap();
    let mut frames = Vec::new();
    while let Some(f) = t.next_stream_frame(1400) {
        frames.push((f.offset, f.len as u64));
    }
    assert_eq!(frames.len(), 130);
    // Every second frame is acknowledged first: 64 disjoint ranges above the hole at the start.
    for &(offset, len) in frames.iter().skip(1).step_by(2).take(64) {
        t.on_acked(&mut pool, id, offset, len, false);
    }
    assert!(
        !t.has_data_to_send(),
        "an acknowledged range was queued to be sent again"
    );
    for &(offset, len) in frames.iter().skip(1).step_by(2).take(64) {
        assert!(t.is_acked(id, offset, len));
    }
}

// ---- allocation ---------------------------------------------------------------------------------------------------

#[test]
fn hot_paths_do_not_allocate() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    let payload = [3u8; 1400];
    let mut buf = [0u8; 1500];
    let stats = measure(|| {
        for round in 0..200u64 {
            // Receive on a peer stream and read it back.
            t.on_stream_frame(&mut pool, 0, round * 1400, &payload, false).unwrap();
            while let Some(c) = t.read_chunk(&pool, 0) {
                let n = c.len();
                t.consume(&mut pool, 0, n, round * 1000, 500).unwrap();
            }
            // Write, build, copy, lose, rebuild, acknowledge.
            t.set_urgency(id, (round % 4) as u8).unwrap();
            assert_eq!(t.write(&mut pool, id, &payload, 1 << 20).unwrap(), 1400);
            assert!(t.granted_unreceived() <= pool.available_bytes());
            let frame = t.next_stream_frame(1400).unwrap();
            t.copy_out(&pool, &frame, &mut buf).unwrap();
            t.on_lost(id, frame.offset, frame.len as u64, false);
            let again = t.next_stream_frame(1400).unwrap();
            t.copy_out(&pool, &again, &mut buf).unwrap();
            t.on_acked(&mut pool, id, again.offset, again.len as u64, false);
            let _ = t.poll_writable(1 << 20);
            while next_control(&mut t).is_some() {}
        }
    });
    assert_eq!(stats.count(), 0);
}

#[test]
fn holding_a_stream_back_does_not_allocate() {
    let (mut pool, mut t) = setup(1024, |c| {
        c.max_streams = 1;
        c.initial_stream_window = 16 * 1024;
    });
    t.on_stream_frame(&mut pool, 0, 0, &[1; 10], false).unwrap();
    let stats = measure(|| {
        for _ in 0..100 {
            assert_eq!(
                t.on_stream_frame(&mut pool, 4, 0, &[1; 10], false),
                Err(StreamError::Exhausted)
            );
            assert!(next_control(&mut t).is_none());
        }
    });
    assert_eq!(stats.count(), 0);
}

#[test]
fn source_frame_building_does_not_allocate() {
    let data = vec![1u8; 100_000];
    struct Plain<'a>(&'a [u8]);
    impl StreamSource for Plain<'_> {
        fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
            let start = offset as usize;
            let n = dst.len().min(self.0.len().saturating_sub(start));
            dst[..n].copy_from_slice(&self.0[start..start + n]);
            n
        }
    }
    let pool = BufferPool::new_boxed(2);
    let mut config = Config::new(false);
    config.peer = peer();
    let mut t = Box::new(Streams::<Plain<'_>, 2, 65>::new(&config, &pool));
    let id = t.open_stream(&pool, false).unwrap();
    t.open_source(id, Plain(&data), data.len() as u64).unwrap();
    let mut buf = [0u8; 1500];
    let stats = measure(|| {
        while let Some(c) = t.next_stream_frame(1400) {
            assert_eq!(t.copy_out(&pool, &c, &mut buf).unwrap(), c.len);
        }
    });
    assert_eq!(stats.count(), 0);
}

#[test]
fn a_stop_request_is_one_control_frame_sent_again_only_when_lost() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 0, 0, b"hello", false).unwrap();
    t.stop_sending(0, 5).unwrap();
    let frame = ControlFrame::StopSending { id: 0, error_code: 5 };
    assert_eq!(drain_control(&mut t), [frame]);
    assert!(
        drain_control(&mut t).is_empty(),
        "the request was repeated without a loss"
    );
    t.stop_sending(0, 6).unwrap();
    assert!(drain_control(&mut t).is_empty(), "a second request replaced the first");
    t.on_control_lost(&frame);
    assert_eq!(drain_control(&mut t), [frame], "a lost request is not sent again");
    t.on_control_acked(&mut pool, &frame);
    t.on_control_lost(&frame);
    assert!(drain_control(&mut t).is_empty(), "an acknowledged request came back");
}

#[test]
fn a_stop_request_is_dropped_once_the_peer_ended_the_stream() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 4, 0, b"x", true).unwrap();
    t.stop_sending(4, 1).unwrap();
    assert!(drain_control(&mut t).is_empty(), "a finished stream was asked to stop");
    t.on_stream_frame(&mut pool, 8, 0, b"y", false).unwrap();
    t.stop_sending(8, 2).unwrap();
    let frame = ControlFrame::StopSending { id: 8, error_code: 2 };
    assert_eq!(drain_control(&mut t), [frame]);
    t.on_reset_stream(&mut pool, 8, 2, 1).unwrap();
    t.on_control_lost(&frame);
    assert!(
        drain_control(&mut t).is_empty(),
        "a reset stream was asked to stop again"
    );
}

#[test]
fn a_stop_request_resets_a_send_half_once_and_refuses_what_has_no_send_half() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    let id = t.open_stream(&pool, true).unwrap();
    t.write(&mut pool, id, b"data", NO_CAP).unwrap();
    assert_eq!(t.on_stop_sending(&mut pool, id, 9), Ok(true));
    assert_eq!(
        t.on_stop_sending(&mut pool, id, 10),
        Ok(false),
        "a second stop reset the stream again"
    );
    assert!(
        drain_control(&mut t)
            .iter()
            .any(|f| matches!(f, ControlFrame::ResetStream { id: i, error_code: 9, .. } if *i == id))
    );
    assert_eq!(t.write(&mut pool, id, b"more", NO_CAP), Err(StreamError::Finished));
    // A unidirectional stream of the peer has no send half here; one of ours has no receive half.
    assert_eq!(t.on_stop_sending(&mut pool, 2, 1), Err(StreamError::StreamState));
    let uni = t.open_stream(&pool, false).unwrap();
    assert_eq!(t.stop_sending(uni, 1), Err(StreamError::StreamState));
    assert_eq!(t.stop_sending(99, 1), Err(StreamError::UnknownStream));
    // A stream of the peer that was never heard of is opened by the stop (with the ones below it), and reset at once.
    assert_eq!(t.on_stop_sending(&mut pool, 8, 3), Ok(true));
    assert_eq!(t.peer_opened(8), 3);
}

#[test]
fn a_stop_request_for_a_stream_far_beyond_the_limit_is_a_violation() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    assert_eq!(
        t.on_stop_sending(&mut pool, 4 * 10_000, 1),
        Err(StreamError::StreamLimit)
    );
}

#[test]
fn a_local_stream_window_is_charged_to_the_ledger() {
    // Regression: a peer stream stored an eighth of the window and the application read it, so its window moved to a
    // span that is not chunk-aligned (three chunks, one held, two of credit). Opening a local stream then added two chunks of
    // credit the ledger never checked, and the credit granted exceeded what the pool could cover.
    let chunk = CHUNK_SIZE as u64;
    let (mut pool, mut t) = setup(4, |c| {
        c.initial_stream_window = 2 * chunk;
        c.max_stream_window = 3 * chunk;
    });
    let eighth = (2 * chunk / 8) as usize;
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; eighth], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), eighth);
    assert_eq!(t.granted_unreceived(), 2 * chunk);
    assert!(t.granted_unreceived() <= pool.available_bytes());
    assert_eq!(t.open_stream(&pool, true), Err(StreamError::Exhausted));
    assert!(t.granted_unreceived() <= pool.available_bytes());
    // A stream with no receive half takes no credit, so it opens.
    t.open_stream(&pool, false).unwrap();
    // The credit comes back when the peer stream ends: the local stream then opens and is counted.
    t.on_stream_frame(&mut pool, 0, eighth as u64, b"", true).unwrap();
    assert_eq!(t.recv_status(0), Some(RecvStatus::Finished));
    t.consume(&mut pool, 0, 0, 0, 0).unwrap();
    let id = t.open_stream(&pool, true).unwrap();
    assert_eq!(t.stream_recv_window(id), Some((2 * chunk, 2 * chunk)));
    assert!(t.granted_unreceived() <= pool.available_bytes());
}

// ---- stream credit --------------------------------------------------------------------------------------------

/// Move every frame `from` wants to send to `to`, as an honest network would.
fn deliver(from: &mut Table, from_pool: &BufferPool<'_>, to: &mut Table, to_pool: &mut BufferPool<'_>) {
    while let Some(c) = from.next_stream_frame(1200) {
        let mut buf = vec![0u8; c.len];
        assert_eq!(from.copy_out(from_pool, &c, &mut buf).unwrap(), c.len);
        assert_eq!(
            to.on_stream_frame(to_pool, c.id, c.offset, &buf, c.fin),
            Ok(()),
            "a stream inside the credit was held back"
        );
    }
}

#[test]
fn the_opener_stops_at_the_credit_and_resumes_on_a_raise() {
    // The receiver: 20 chunks, windows of 4 chunks: five windows fit, two are credit (three stay free), so it tells the opener 2.
    let (mut rpool, mut rx) = setup_credit(20, |c| c.initial_stream_window = 64 * 1024);
    assert_eq!(rx.advertised_streams(), 2);
    let mut opener = Config::new(true);
    opener.peer = PeerLimits {
        window: 64 * 1024,
        max_streams: rx.advertised_streams(),
    };
    let mut opool = BufferPool::new_boxed(16);
    let mut tx = Box::new(Table::new(&opener, &opool));
    let first = [
        tx.open_stream(&opool, false).unwrap(),
        tx.open_stream(&opool, false).unwrap(),
    ];
    assert_eq!(
        tx.open_stream(&opool, false),
        Err(StreamError::StreamLimit),
        "no credit for a third"
    );
    for id in first {
        tx.write(&mut opool, id, &[7; 100], NO_CAP).unwrap();
        tx.finish(id).unwrap();
    }
    deliver(&mut tx, &opool, &mut rx, &mut rpool);
    assert_eq!(rx.open_streams(), 2);
    // The receiver reads both to their end: the streams end and it has room for two more.
    for id in first {
        assert_eq!(read_all(&mut rx, &mut rpool, id).len(), 100);
    }
    assert_eq!(rx.open_streams(), 0);
    rx.regrant(&rpool);
    let raise = std::iter::from_fn(|| rx.pending_control()).find_map(|f| match f {
        ControlFrame::MaxStreams { limit } => Some(limit),
        _ => None,
    });
    assert_eq!(raise, Some(4), "two admitted plus room for two more");
    tx.on_max_streams(4);
    let more = [
        tx.open_stream(&opool, false).unwrap(),
        tx.open_stream(&opool, false).unwrap(),
    ];
    assert_eq!(tx.open_stream(&opool, false), Err(StreamError::StreamLimit));
    for id in more {
        tx.write(&mut opool, id, &[9; 50], NO_CAP).unwrap();
        tx.finish(id).unwrap();
    }
    deliver(&mut tx, &opool, &mut rx, &mut rpool);
    assert_eq!(rx.open_streams(), 2);
}

#[test]
fn the_credit_given_to_the_peer_keeps_its_windows_in_the_pool() {
    // 20 chunks, windows of 4 chunks, credit for 2 streams: 8 chunks stay free for them.
    let (mut pool, mut t) = setup_credit(20, |c| c.initial_stream_window = 64 * 1024);
    assert_eq!(t.advertised_streams(), 2);
    // Our own streams may take the rest only: 12 chunks, then the next would touch the reserved 8.
    for _ in 0..3 {
        t.open_stream(&pool, true).unwrap();
    }
    assert_eq!(t.open_stream(&pool, true), Err(StreamError::Exhausted));
    assert!(t.granted_unreceived() <= pool.available_bytes());
    // The two streams the peer may open are admitted, and nothing is held back.
    t.on_stream_frame(&mut pool, 0, 0, &[1; 10], false).unwrap();
    t.on_stream_frame(&mut pool, 4, 0, &[1; 10], false).unwrap();
    assert_eq!(t.open_streams(), 5);
}
