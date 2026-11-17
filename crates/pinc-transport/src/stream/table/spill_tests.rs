//! Unit tests of the stream table where a stream's range sets spill into a pool chunk, give it back once they fit
//! inline again, and where the chunk is missing.

use alloc::vec::Vec;

use super::*;
use crate::stream::StreamChunk;
use crate::stream::pool::CHUNK_SIZE;

type T = Streams<NoSource, 72, 65>;

/// The bytes of every frame the tests send.
const FRAME: usize = 10;

fn sender(pool: &BufferPool<'_>) -> (T, StreamId) {
    let mut cfg = Config::new(true);
    cfg.peer = PeerLimits {
        window: 64 * 1024,
        max_streams: 16,
    };
    let mut t = T::new(&cfg, pool);
    let id = t.open_stream(pool, true).unwrap();
    (t, id)
}

/// Write `frames` frames of 10 bytes (the last carries the end when `fin`) and send them all.
fn sent(t: &mut T, pool: &mut BufferPool<'_>, id: StreamId, frames: usize, fin: bool) -> Vec<StreamChunk> {
    let data = alloc::vec![1u8; frames * FRAME];
    assert_eq!(t.write(pool, id, &data, u64::MAX).unwrap(), data.len());
    if fin {
        t.finish(id).unwrap();
    }
    let out: Vec<StreamChunk> = core::iter::from_fn(|| t.next_stream_frame(pool, FRAME)).collect();
    assert_eq!(out.len(), frames);
    out
}

fn lose(t: &mut T, pool: &mut BufferPool<'_>, c: &StreamChunk) {
    t.on_lost(pool, c.id, c.offset, c.len as u64, c.fin);
}

fn ack(t: &mut T, pool: &mut BufferPool<'_>, c: &StreamChunk) {
    t.on_acked(pool, c.id, c.offset, c.len as u64, c.fin);
}

/// Send again what is queued, as the connection does.
fn resent(t: &mut T, pool: &mut BufferPool<'_>) -> Vec<StreamChunk> {
    core::iter::from_fn(|| {
        let c = t.next_stream_frame(pool, FRAME)?;
        t.copy_out(pool, &c, &mut [0u8; FRAME]).unwrap();
        Some(c)
    })
    .collect()
}

/// while the stream stays open.
#[test]
fn a_loss_burst_spills_the_lost_set_and_the_repair_gives_the_chunk_back() {
    let mut pool = BufferPool::new_boxed(64);
    let (mut t, id) = sender(&pool);
    let frames = sent(&mut t, &mut pool, id, 40, false);
    let free = pool.available_chunks();
    let lost: Vec<&StreamChunk> = frames.iter().step_by(2).take(17).collect();
    for c in &lost {
        lose(&mut t, &mut pool, c);
    }
    assert_eq!(t.stats().range_spills, 1, "the spill is counted once");
    assert_eq!(t.stats().range_overflows, 0, "nothing was widened");
    assert_eq!(pool.available_chunks(), free - 1, "the lost set took a chunk");
    let again = resent(&mut t, &mut pool);
    let offsets: Vec<u64> = again.iter().map(|c| c.offset).collect();
    assert_eq!(
        offsets,
        lost.iter().map(|c| c.offset).collect::<Vec<_>>(),
        "only the lost ranges are sent again"
    );
    assert!(t.send_view(id).is_some_and(|v| !v.done), "the stream is still open");
    assert_eq!(
        pool.available_chunks(),
        free,
        "the chunk is back before the stream ends"
    );
}

/// loss makes.
#[test]
fn a_frame_queued_again_by_a_failed_copy_counts_the_spill_it_causes() {
    let mut pool = BufferPool::new_boxed(64);
    let (mut t, id) = sender(&pool);
    // One whole chunk written and sent as one frame, then 16 disjoint ranges declared lost.
    t.write(&mut pool, id, &alloc::vec![1u8; CHUNK_SIZE], u64::MAX).unwrap();
    assert_eq!(
        t.next_stream_frame(&mut pool, CHUNK_SIZE).map(|c| c.len),
        Some(CHUNK_SIZE)
    );
    for k in 0..16 {
        t.on_lost(&mut pool, id, 20 * k, 10, false);
    }
    assert_eq!(t.stats().range_spills, 0, "16 ranges fit inline");
    // Ten bytes asked at 16380, of which four lie in the chunk held: the copy falls short and queues 16380..16384, the
    // 17th range.
    let short = StreamChunk {
        id,
        offset: CHUNK_SIZE as u64 - 4,
        len: FRAME,
        fin: false,
    };
    assert_eq!(
        t.copy_out(&mut pool, &short, &mut [0u8; FRAME]),
        Err(StreamError::DataUnavailable)
    );
    assert_eq!(t.stats().range_spills, 1);
}

/// The acknowledged set spills at 65 disjoint ranges and gives its chunk back when the holes are filled.
#[test]
fn the_acknowledged_set_gives_its_chunk_back_when_the_holes_are_filled() {
    let mut pool = BufferPool::new_boxed(64);
    let (mut t, id) = sender(&pool);
    let frames = sent(&mut t, &mut pool, id, 140, false);
    let base = pool.used_chunks();
    for c in frames.iter().step_by(2) {
        ack(&mut t, &mut pool, c);
    }
    assert_eq!(t.stats().range_spills, 1);
    assert_eq!(pool.used_chunks(), base + 1, "the acknowledged set took a chunk");
    for c in frames.iter().skip(1).step_by(2) {
        ack(&mut t, &mut pool, c);
    }
    assert_eq!(
        pool.used_chunks(),
        base,
        "one range again: the chunk is back, the stream is open"
    );
    assert!(t.send_view(id).is_some_and(|v| !v.done));
}

/// the receive half is done too.
#[test]
fn a_finished_send_half_holds_no_range_chunk_before_its_slot_is_freed() {
    let mut pool = BufferPool::new_boxed(64);
    let (mut t, id) = sender(&pool);
    let frames = sent(&mut t, &mut pool, id, 140, true);
    for c in frames.iter().step_by(2) {
        ack(&mut t, &mut pool, c);
    }
    assert_eq!(t.stats().range_spills, 1);
    for c in frames.iter().skip(1).step_by(2) {
        ack(&mut t, &mut pool, c);
    }
    assert!(t.send_view(id).is_some_and(|v| v.done), "the send half is finished");
    assert_eq!(t.open_streams(), 1, "the slot is held by the receive half");
    assert_eq!(pool.used_chunks(), 0, "neither a ring chunk nor a range chunk is held");
}

/// and nothing was read.
#[test]
fn the_received_set_gives_its_chunk_back_when_the_holes_are_filled() {
    let mut pool = BufferPool::new_boxed(64);
    let mut cfg = Config::new(false);
    cfg.initial_stream_window = 64 * 1024;
    let mut t = T::new(&cfg, &pool);
    let holes = crate::stream::RECV_RANGES as u64 + 1;
    t.on_stream_frame(&mut pool, 0, 10, &[7; 10], false).unwrap();
    let base = pool.used_chunks();
    for k in 1..holes {
        t.on_stream_frame(&mut pool, 0, 20 * k + 10, &[7; 10], false).unwrap();
    }
    assert_eq!(t.stats().range_spills, 1);
    assert_eq!(pool.used_chunks(), base + 1, "the received set took a chunk");
    for k in 0..holes {
        t.on_stream_frame(&mut pool, 0, 20 * k, &[7; 10], false).unwrap();
    }
    assert_eq!(
        pool.used_chunks(),
        base,
        "one range again: the chunk is back, the stream is open"
    );
    assert_eq!(t.stored_after(&pool, 0, 0), Some(0..20 * (holes - 1) + 20));
}
