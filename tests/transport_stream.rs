//! The transport stream layer: reassembly, flow control, window autotuning, the send queue, source-backed streams,
//! stream limits and resets, with the pool accounting checked at every end.
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
type Table = Streams<NoSource, 8, 1025>;

fn peer() -> PeerLimits {
    PeerLimits {
        max_data: 64 * MIB,
        max_stream_data_bidi_local: 5 * MIB / 4,
        max_stream_data_bidi_remote: 5 * MIB / 4,
        max_stream_data_uni: 5 * MIB / 4,
        max_streams_bidi: 100,
        max_streams_uni: 100,
    }
}

/// A server-side table over a heap pool of `chunks` chunks.
fn setup(chunks: usize, edit: impl FnOnce(&mut Config)) -> (BufferPool<'static>, Box<Table>) {
    let pool = BufferPool::new_boxed(chunks);
    let mut config = Config::new(false);
    config.peer = peer();
    edit(&mut config);
    let table = Box::new(Table::new(&config, &pool));
    (pool, table)
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

fn drain_control(t: &mut Table) -> Vec<ControlFrame> {
    std::iter::from_fn(|| t.pending_control()).collect()
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
    let (mut pool, mut t) = setup(64, |_| {});
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
    let (mut pool, mut t) = setup(64, |_| {});
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
    let (mut pool, mut t) = setup(64, |_| {});
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
        let (mut pool, mut t) = setup(64, |_| {});
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
    let (mut pool, mut t) = setup(64, |_| {});
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
    let (mut pool, mut t) = setup(64, |_| {});
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
    let (mut pool, mut t) = setup(64, |_| {});
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
    let (mut pool, mut t) = setup(64, |c| c.initial_stream_window = 4096);
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
fn connection_credit_is_enforced_across_streams() {
    let (mut pool, mut t) = setup(64, |c| c.initial_conn_window = 3000);
    t.on_stream_frame(&mut pool, 0, 0, &[1; 2000], false).unwrap();
    let used = pool.used_chunks();
    assert_eq!(
        t.on_stream_frame(&mut pool, 4, 0, &[2; 1500], false),
        Err(StreamError::FlowControl)
    );
    assert_eq!(pool.used_chunks(), used, "a refused frame stores nothing");
    t.on_stream_frame(&mut pool, 4, 0, &[2; 1000], false).unwrap();
    // A duplicate does not count twice.
    t.on_stream_frame(&mut pool, 0, 0, &[1; 2000], false).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 4, 1000, &[2; 1], false),
        Err(StreamError::FlowControl)
    );
}

#[test]
fn an_empty_pool_refuses_data_without_storing_any() {
    let (mut pool, mut t) = setup(4, |_| {});
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
fn credit_is_not_granted_beyond_what_the_pool_can_hold() {
    // 64 chunks: windows clamp to half of the pool, 512 KiB.
    let (mut pool, mut t) = setup(64, |_| {});
    assert_eq!(t.recv_window(), 512 * 1024);
    let hog: Vec<_> = (0..60).map(|_| pool.alloc_chunk().unwrap()).collect();
    t.on_stream_frame(&mut pool, 0, 0, &[1; 40_000], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 40_000);
    assert!(
        !drain_control(&mut t)
            .iter()
            .any(|f| matches!(f, ControlFrame::MaxData(_))),
        "no new connection credit while the pool is nearly empty"
    );
    for c in hog {
        pool.free_chunk(c);
    }
    t.on_stream_frame(&mut pool, 0, 40_000, &[1; 40_000], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), 40_000);
    let frames = drain_control(&mut t);
    assert!(
        frames
            .iter()
            .any(|f| matches!(f, ControlFrame::MaxData(m) if *m > 512 * 1024))
    );
}

// ---- flow-control credit ------------------------------------------------------------------------------------------

#[test]
fn max_stream_data_is_sent_after_an_eighth_of_the_window() {
    let (mut pool, mut t) = setup(256, |_| {});
    let window = 1_310_720u64;
    let eighth = (window / 8) as usize;
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; eighth + 100], false)
        .unwrap();
    // srtt 0 disables autotuning, so only the 1/8 rule is visible.
    t.consume(&mut pool, 0, eighth - 1, 10, 0).unwrap();
    assert!(drain_control(&mut t).is_empty());
    t.consume(&mut pool, 0, 1, 10, 0).unwrap();
    let frames = drain_control(&mut t);
    let credit = eighth as u64 + window;
    assert_eq!(
        frames,
        [
            ControlFrame::MaxData(credit),
            ControlFrame::MaxStreamData { id: 0, max: credit }
        ]
    );
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
    t.on_control_lost(&frames[1]);
    assert_eq!(drain_control(&mut t), [frames[1]]);
}

#[test]
fn a_window_consumed_in_under_two_round_trips_doubles_up_to_the_caps() {
    let (mut pool, mut t) = setup(4096, |_| {});
    let rtt = 1_000_000u64;
    let piece = vec![7u8; 64 * 1024];
    let mut sent = 0u64;
    let mut now = 0u64;
    let mut stream_sizes = vec![t.stream_recv_window(0).map_or(1_310_720, |w| w.0)];
    let mut conn_sizes = vec![t.recv_window()];
    while sent < 80 * MIB {
        let limit = t.stream_recv_window(0).map_or(1_310_720, |w| w.1).min(t.recv_limit());
        let n = (limit - sent).min(piece.len() as u64) as usize;
        assert!(n > 0, "the peer must always have credit while we read promptly");
        t.on_stream_frame(&mut pool, 0, sent, &piece[..n], false).unwrap();
        sent += n as u64;
        now += 1000;
        while let Some(chunk) = t.read_chunk(&pool, 0) {
            let len = chunk.len();
            t.consume(&mut pool, 0, len, now, rtt).unwrap();
        }
        drain_control(&mut t);
        let (s, _) = t.stream_recv_window(0).unwrap();
        stream_sizes.push(s);
        conn_sizes.push(t.recv_window());
    }
    assert_eq!(
        *stream_sizes.last().unwrap(),
        16 * MIB,
        "the stream window caps at 16 MiB"
    );
    assert_eq!(
        *conn_sizes.last().unwrap(),
        24 * MIB,
        "the connection window caps at 24 MiB"
    );
    assert!(stream_sizes.iter().all(|&s| s <= 16 * MIB) && conn_sizes.iter().all(|&s| s <= 24 * MIB));
    assert!(
        stream_sizes
            .windows(2)
            .all(|w| w[1] == w[0] || w[1] == (w[0] * 2).min(16 * MIB)),
        "growth is by doubling"
    );
    assert_eq!(pool.used_chunks(), 0);
}

#[test]
fn a_slowly_consumed_window_does_not_grow() {
    let (mut pool, mut t) = setup(256, |_| {});
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
fn write_is_bounded_by_credit_and_blocked_frames_follow() {
    let (mut pool, mut t) = setup(64, |c| {
        c.peer.max_stream_data_bidi_remote = 5000;
        c.peer.max_data = 8000;
    });
    let id = t.open_stream(true).unwrap();
    assert_eq!(id, 1);
    assert_eq!(t.write(&mut pool, id, &[1; 8000]).unwrap(), 5000);
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::StreamDataBlocked { id, limit: 5000 }]
    );
    assert_eq!(t.write(&mut pool, id, &[1; 10]).unwrap(), 0);
    assert!(drain_control(&mut t).is_empty(), "blocked is sent once per limit");
    t.on_max_stream_data(id, 20_000).unwrap();
    assert_eq!(
        t.write(&mut pool, id, &[1; 10_000]).unwrap(),
        3000,
        "the connection limit binds next"
    );
    assert_eq!(drain_control(&mut t), [ControlFrame::DataBlocked(8000)]);
    t.on_max_data(100_000);
    assert_eq!(t.write(&mut pool, id, &[1; 10_000]).unwrap(), 10_000);
    t.finish(id).unwrap();
    assert_eq!(t.write(&mut pool, id, &[1]), Err(StreamError::Finished));
}

#[test]
fn write_stops_when_the_pool_is_empty() {
    let (mut pool, mut t) = setup(2, |_| {});
    let id = t.open_stream(false).unwrap();
    assert_eq!(
        t.write(&mut pool, id, &vec![1; 3 * CHUNK_SIZE]).unwrap(),
        2 * CHUNK_SIZE
    );
    assert_eq!(t.write(&mut pool, id, &[1]).unwrap(), 0);
    assert_eq!(pool.available_chunks(), 0);
}

#[test]
fn lost_ranges_go_first_lowest_hole_first() {
    let (mut pool, mut t) = setup(64, |_| {});
    let id = t.open_stream(true).unwrap();
    let data = pattern(6000, 3);
    t.write(&mut pool, id, &data).unwrap();
    let frames = drain_frames(&mut t, &pool, 1000);
    assert_eq!(frames.len(), 6);
    assert!(frames.iter().all(|(_, d)| !d.is_empty()));
    let at = |i: usize| (frames[i].0.offset, frames[i].0.len as u64);
    // Loss reports arrive out of order; the retransmission order is by offset.
    t.on_lost(id, at(3).0, at(3).1, false);
    t.on_lost(id, at(1).0, at(1).1, false);
    t.write(&mut pool, id, &pattern(500, 4)).unwrap();
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
    let (mut pool, mut t) = setup(64, |_| {});
    let id = t.open_stream(true).unwrap();
    t.write(&mut pool, id, &pattern(3000, 5)).unwrap();
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
    let (mut pool, mut t) = setup(64, |_| {});
    let id = t.open_stream(false).unwrap();
    let data = pattern(3 * CHUNK_SIZE + 100, 6);
    assert_eq!(t.write(&mut pool, id, &data).unwrap(), data.len());
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
    let (mut pool, mut t) = setup(64, |_| {});
    let id = t.open_stream(false).unwrap();
    t.write(&mut pool, id, &[1; 100]).unwrap();
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
    let id = t.open_stream(false).unwrap();
    t.open_source(id, Src { data: &data, log: &log }, data.len() as u64)
        .unwrap();
    assert_eq!(t.write(&mut pool, id, &[1]), Err(StreamError::WrongKind));
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
    let id = t.open_stream(false).unwrap();
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
    config.peer.max_stream_data_uni = 3000;
    let mut t = Box::new(Streams::<Src<'_>, 2, 65>::new(&config, &pool));
    let id = t.open_stream(false).unwrap();
    t.open_source(id, Src { data: &data, log: &log }, 10_000).unwrap();
    let mut total = 0;
    while let Some(c) = t.next_stream_frame(1200) {
        total += c.len;
    }
    assert_eq!(total, 3000);
    assert_eq!(
        t.pending_control(),
        Some(ControlFrame::StreamDataBlocked { id, limit: 3000 })
    );
    t.on_lost(id, 0, 1200, false);
    assert_eq!(
        t.next_stream_frame(1200).unwrap().len,
        1200,
        "retransmissions need no credit"
    );
    t.on_max_stream_data(id, 6000).unwrap();
    assert_eq!(t.next_stream_frame(5000).unwrap().len, 3000);
    let _ = &mut pool;
}

// ---- reset and stop -----------------------------------------------------------------------------------------------

#[test]
fn reset_drops_buffers_and_closes_when_acknowledged() {
    let (mut pool, mut t) = setup(64, |_| {});
    let id = t.open_stream(false).unwrap();
    t.write(&mut pool, id, &vec![1; 40_000]).unwrap();
    assert!(pool.used_chunks() > 0);
    t.reset(&mut pool, id, 77).unwrap();
    assert_eq!(pool.used_chunks(), 0);
    let frame = t.pending_control().unwrap();
    assert_eq!(
        frame,
        ControlFrame::ResetStream {
            id,
            error_code: 77,
            final_size: 40_000
        }
    );
    assert!(t.next_stream_frame(1000).is_none());
    assert_eq!(t.write(&mut pool, id, &[1]), Err(StreamError::Finished));
    t.on_control_lost(&frame);
    assert_eq!(t.pending_control(), Some(frame));
    assert_eq!(t.open_streams(), 1);
    t.on_control_acked(&mut pool, &frame);
    assert_eq!(t.open_streams(), 0);
}

#[test]
fn stop_sending_from_the_peer_resets_the_send_side() {
    let (mut pool, mut t) = setup(64, |_| {});
    let id = t.open_stream(true).unwrap();
    t.write(&mut pool, id, &[1; 5000]).unwrap();
    drain_frames(&mut t, &pool, 1000);
    t.on_stop_sending(&mut pool, id, 9).unwrap();
    assert_eq!(pool.used_chunks(), 0);
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::ResetStream {
            id,
            error_code: 9,
            final_size: 5000
        }]
    );
    t.on_acked(&mut pool, id, 0, 1000, false);
}

#[test]
fn a_peer_reset_frees_the_buffer_and_credits_the_connection() {
    let (mut pool, mut t) = setup(64, |c| c.initial_conn_window = 100_000);
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
    // The unread bytes count as consumed, so the connection credit slides.
    assert!(
        drain_control(&mut t)
            .iter()
            .any(|f| matches!(f, ControlFrame::MaxData(m) if *m >= 160_000))
    );
    assert_eq!(t.consume(&mut pool, 2, 0, 0, 0), Ok(RecvStatus::Reset(5)));
    assert_eq!(t.open_streams(), 0);
}

#[test]
fn stop_sending_discards_what_the_peer_still_sends() {
    let (mut pool, mut t) = setup(64, |_| {});
    t.on_stream_frame(&mut pool, 2, 0, &[1; 20_000], false).unwrap();
    t.stop_sending(&mut pool, 2, 4).unwrap();
    assert_eq!(pool.used_chunks(), 0);
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::StopSending { id: 2, error_code: 4 }]
    );
    t.on_stream_frame(&mut pool, 2, 20_000, &[1; 20_000], false).unwrap();
    assert_eq!(pool.used_chunks(), 0, "discarded bytes are never stored");
    t.on_stream_frame(&mut pool, 2, 40_000, &[1; 10], true).unwrap();
    assert_eq!(t.open_streams(), 0);
}

// ---- stream ids and limits ----------------------------------------------------------------------------------------

#[test]
fn stream_ids_follow_the_quic_bit_layout() {
    let pool = BufferPool::new_boxed(8);
    let mut client = Config::new(true);
    client.peer = peer();
    let mut c = Box::new(Table::new(&client, &pool));
    let mut server = Config::new(false);
    server.peer = peer();
    let mut s = Box::new(Table::new(&server, &pool));
    assert_eq!([c.open_stream(true), c.open_stream(true)], [Ok(0), Ok(4)]);
    assert_eq!([c.open_stream(false), c.open_stream(false)], [Ok(2), Ok(6)]);
    assert_eq!([s.open_stream(true), s.open_stream(true)], [Ok(1), Ok(5)]);
    assert_eq!([s.open_stream(false), s.open_stream(false)], [Ok(3), Ok(7)]);
}

#[test]
fn peer_stream_limits_are_enforced_and_credited_as_streams_close() {
    let (mut pool, mut t) = setup(64, |c| {
        c.max_streams_uni = 2;
        c.max_streams_bidi = 2;
    });
    t.on_stream_frame(&mut pool, 2, 0, &[1; 10], true).unwrap();
    t.on_stream_frame(&mut pool, 6, 0, &[1; 10], false).unwrap();
    assert_eq!(
        t.on_stream_frame(&mut pool, 10, 0, &[1], false),
        Err(StreamError::StreamLimit)
    );
    assert_eq!(t.open_streams(), 2);
    // Consuming the last byte lets the application see the end, which closes the stream.
    assert_eq!(read_all(&mut t, &mut pool, 2).len(), 10);
    assert_eq!(t.open_streams(), 1);
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::MaxStreams { bidi: false, max: 3 }]
    );
    t.on_stream_frame(&mut pool, 10, 0, &[1], false).unwrap();
    // A frame for a closed stream is ignored.
    t.on_stream_frame(&mut pool, 2, 0, &[1; 10], true).unwrap();
    // The first bidirectional stream implicitly opens the lower numbered ones.
    t.on_stream_frame(&mut pool, 4, 0, &[1], false).unwrap();
    assert_eq!(t.open_streams(), 4);
}

#[test]
fn frames_for_the_wrong_direction_or_unopened_local_streams_are_errors() {
    let (mut pool, mut t) = setup(64, |_| {});
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
    assert_eq!(t.on_max_stream_data(2, 100), Err(StreamError::StreamState));
    assert_eq!(t.write(&mut pool, 2, &[1]), Err(StreamError::StreamState));
}

#[test]
fn opening_beyond_the_peer_limit_queues_a_streams_blocked_once() {
    let (_pool, mut t) = setup(8, |c| c.peer.max_streams_uni = 1);
    assert_eq!(t.open_stream(false), Ok(3));
    assert_eq!(t.open_stream(false), Err(StreamError::StreamLimit));
    assert_eq!(
        drain_control(&mut t),
        [ControlFrame::StreamsBlocked { bidi: false, limit: 1 }]
    );
    assert_eq!(t.open_stream(false), Err(StreamError::StreamLimit));
    assert!(drain_control(&mut t).is_empty());
    t.on_max_streams(false, 2);
    assert_eq!(t.open_stream(false), Ok(7));
}

#[test]
fn the_table_is_bounded() {
    let (mut pool, mut t) = setup(64, |c| c.max_streams_bidi = 100);
    // The peer's stream limit is clamped to the table size.
    assert_eq!(
        t.on_stream_frame(&mut pool, 4 * 8, 0, &[1], false),
        Err(StreamError::StreamLimit)
    );
    for _ in 0..8 {
        t.open_stream(true).unwrap();
    }
    assert_eq!(t.open_stream(true), Err(StreamError::TableFull));
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 0, &[1], false),
        Err(StreamError::TableFull)
    );
    assert_eq!(t.open_streams(), 8);
}

#[test]
fn closing_every_stream_returns_every_chunk() {
    let (mut pool, mut t) = setup(256, |_| {});
    for sid in [0u64, 4, 8] {
        t.on_stream_frame(&mut pool, sid, 5, &pattern(30_000, sid), false)
            .unwrap();
    }
    let a = t.open_stream(true).unwrap();
    let b = t.open_stream(false).unwrap();
    t.write(&mut pool, a, &pattern(50_000, 1)).unwrap();
    t.write(&mut pool, b, &pattern(50_000, 2)).unwrap();
    assert!(pool.used_chunks() > 0);
    t.close_all(&mut pool);
    assert_eq!(t.open_streams(), 0);
    assert_eq!(pool.used_chunks(), 0);
}

// ---- allocation ---------------------------------------------------------------------------------------------------

#[test]
fn hot_paths_do_not_allocate() {
    let (mut pool, mut t) = setup(256, |_| {});
    let id = t.open_stream(true).unwrap();
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
            assert_eq!(t.write(&mut pool, id, &payload).unwrap(), 1400);
            let frame = t.next_stream_frame(1400).unwrap();
            t.copy_out(&pool, &frame, &mut buf).unwrap();
            t.on_lost(id, frame.offset, frame.len as u64, false);
            let again = t.next_stream_frame(1400).unwrap();
            t.copy_out(&pool, &again, &mut buf).unwrap();
            t.on_acked(&mut pool, id, again.offset, again.len as u64, false);
            while t.pending_control().is_some() {}
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
    let id = t.open_stream(false).unwrap();
    t.open_source(id, Plain(&data), data.len() as u64).unwrap();
    let mut buf = [0u8; 1500];
    let stats = measure(|| {
        while let Some(c) = t.next_stream_frame(1400) {
            assert_eq!(t.copy_out(&pool, &c, &mut buf).unwrap(), c.len);
        }
    });
    assert_eq!(stats.count(), 0);
}
