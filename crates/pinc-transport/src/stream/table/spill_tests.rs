//! Unit tests of the stream table where a stream's range sets spill into a slot of the endpoint's arena, give it back
//! once they fit inline again, and where no slot is free. A spill never takes a pool chunk.

use alloc::vec::Vec;

use super::*;
use crate::stream::pool::{CHUNK_SIZE, Chunk};
use crate::stream::spill::SpillArena;
use crate::stream::{RECV_RANGES, StreamChunk};

type T = Streams<NoSource, 72, 65>;

/// The bytes of every frame the tests send.
const FRAME: usize = 10;

/// A pool of 64 chunks lent an arena of `slots` slots, as the endpoint lends it for a call.
fn lent(slots: usize) -> BufferPool<'static> {
    let mut pool = BufferPool::new_boxed(64);
    pool.lend_spill(SpillArena::new_boxed(slots));
    pool
}

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

fn receiver(pool: &BufferPool<'_>) -> T {
    let mut cfg = Config::new(false);
    cfg.initial_stream_window = 64 * 1024;
    T::new(&cfg, pool)
}

/// `holes` received ranges of ten bytes on peer stream `id`, ten bytes apart.
fn scatter(t: &mut T, pool: &mut BufferPool<'_>, id: StreamId, holes: u64) -> Vec<Result<(), StreamError>> {
    (0..holes)
        .map(|k| t.on_stream_frame(pool, id, 20 * k + 10, &[7; 10], false))
        .collect()
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

/// Take every chunk the pool has left, so the next one asked for is refused.
fn hog(pool: &mut BufferPool<'_>) -> Vec<Chunk> {
    let held: Vec<Chunk> = core::iter::from_fn(|| pool.alloc_chunk().ok()).collect();
    assert_eq!(pool.available_chunks(), 0);
    held
}

/// Every other frame of a 140-frame stream acknowledged (70 disjoint ranges, past the 64 inline) and 17 of the frames
/// between them lost, so both send range sets hold a slot.
fn both_sets_spilled(t: &mut T, pool: &mut BufferPool<'_>, id: StreamId) -> Vec<StreamChunk> {
    let frames = sent(t, pool, id, 140, false);
    for c in frames.iter().step_by(2) {
        ack(t, pool, c);
    }
    for c in frames.iter().skip(1).step_by(2).take(17) {
        lose(t, pool, c);
    }
    assert_eq!(t.stats().range_spills, 2);
    assert_eq!(
        (pool.used_chunks(), pool.spill_held()),
        (1, 2),
        "the ring chunk, and a slot for each send range set"
    );
    frames
}

/// One burst of 17 disjoint losses (the inline set holds 16) spills the lost set into a slot, takes no chunk, and
/// counts it; the bytes sent again are exactly the lost ones; and once the repair has emptied the set the slot is back
/// while the stream stays open.
#[test]
fn a_loss_burst_spills_the_lost_set_and_the_repair_gives_the_slot_back() {
    let mut pool = lent(8);
    let (mut t, id) = sender(&pool);
    let frames = sent(&mut t, &mut pool, id, 40, false);
    let free = pool.available_chunks();
    let lost: Vec<&StreamChunk> = frames.iter().step_by(2).take(17).collect();
    for c in &lost {
        lose(&mut t, &mut pool, c);
    }
    assert_eq!(t.stats().range_spills, 1, "the spill is counted once");
    assert_eq!(t.stats().range_overflows, 0, "nothing was widened");
    assert_eq!(
        (pool.available_chunks(), pool.spill_held()),
        (free, 1),
        "the lost set took a slot, not a chunk"
    );
    let again = resent(&mut t, &mut pool);
    let offsets: Vec<u64> = again.iter().map(|c| c.offset).collect();
    assert_eq!(
        offsets,
        lost.iter().map(|c| c.offset).collect::<Vec<_>>(),
        "only the lost ranges are sent again"
    );
    assert!(t.send_view(id).is_some_and(|v| !v.done), "the stream is still open");
    assert_eq!(pool.spill_held(), 0, "the slot is back before the stream ends");
}

/// With no slot free the lost set widens as it did before the spill existed, and both the widening and the refused
/// spill are counted.
#[test]
fn without_a_free_slot_the_lost_set_widens_and_the_widening_is_counted() {
    let mut pool = lent(0);
    let (mut t, id) = sender(&pool);
    let frames = sent(&mut t, &mut pool, id, 40, false);
    for c in frames.iter().step_by(2).take(17) {
        lose(&mut t, &mut pool, c);
    }
    assert_eq!(t.stats().range_spills, 0, "no slot to spill into");
    assert_eq!(t.stats().range_overflows, 1, "the 17th range widened its neighbour");
    assert_eq!(pool.spill_refused(), 1);
    // 15 ranges of 10 bytes and the last two (300..310 and 320..330) as one of 30.
    let bytes: usize = resent(&mut t, &mut pool).iter().map(|c| c.len).sum();
    assert_eq!(bytes, 180);
}

/// A frame that cannot be copied is queued again; when that spills the lost set, the spill is counted like the one a
/// loss makes.
#[test]
fn a_frame_queued_again_by_a_failed_copy_counts_the_spill_it_causes() {
    let mut pool = lent(8);
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
    assert_eq!((t.stats().range_spills, pool.spill_held()), (1, 1));
}

/// The acknowledged set spills at 65 disjoint ranges and gives its slot back when the holes are filled.
#[test]
fn the_acknowledged_set_gives_its_slot_back_when_the_holes_are_filled() {
    let mut pool = lent(8);
    let (mut t, id) = sender(&pool);
    let frames = sent(&mut t, &mut pool, id, 140, false);
    let base = pool.used_chunks();
    for c in frames.iter().step_by(2) {
        ack(&mut t, &mut pool, c);
    }
    assert_eq!(t.stats().range_spills, 1);
    assert_eq!(
        (pool.used_chunks(), pool.spill_held()),
        (base, 1),
        "the acknowledged set took a slot, not a chunk"
    );
    for c in frames.iter().skip(1).step_by(2) {
        ack(&mut t, &mut pool, c);
    }
    assert_eq!(
        pool.spill_held(),
        0,
        "one range again: the slot is back, the stream is open"
    );
    assert!(t.send_view(id).is_some_and(|v| !v.done));
}

/// A send half that finished (its end and every byte acknowledged) holds no slot, though its stream slot stays until
/// the receive half is done too.
#[test]
fn a_finished_send_half_holds_no_spill_slot_before_its_stream_slot_is_freed() {
    let mut pool = lent(8);
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
    assert_eq!(
        (pool.used_chunks(), pool.spill_held()),
        (0, 0),
        "neither a ring chunk nor a spill slot is held"
    );
}

/// A reset gives back the send ring chunk and both range sets' slots.
#[test]
fn a_reset_returns_the_send_range_slots() {
    let mut pool = lent(8);
    let (mut t, id) = sender(&pool);
    both_sets_spilled(&mut t, &mut pool, id);
    t.reset(&mut pool, id, 7).unwrap();
    assert_eq!((pool.used_chunks(), pool.spill_held()), (0, 0));
}

/// A stop request from the peer resets the send half and gives back its chunk and slots.
#[test]
fn a_stop_request_returns_the_send_range_slots() {
    let mut pool = lent(8);
    let (mut t, id) = sender(&pool);
    both_sets_spilled(&mut t, &mut pool, id);
    assert_eq!(t.on_stop_sending(&mut pool, id, 7), Ok(true));
    assert_eq!((pool.used_chunks(), pool.spill_held()), (0, 0));
}

/// Closing the table gives back the send chunks and slots of every stream.
#[test]
fn closing_the_table_returns_the_send_range_slots() {
    let mut pool = lent(8);
    let (mut t, id) = sender(&pool);
    both_sets_spilled(&mut t, &mut pool, id);
    t.close_all(&mut pool);
    assert_eq!((pool.used_chunks(), pool.spill_held()), (0, 0));
}

/// A frame that needs a new received range while the inline set is full is stored with the pool full: its range set
/// spills into an arena slot, never a chunk, so spill memory never makes a frame `Exhausted` (#635 review point 2).
#[test]
fn a_frame_that_spills_is_stored_while_the_pool_is_full() {
    let mut pool = lent(8);
    let mut t = receiver(&pool);
    let inline = RECV_RANGES as u64;
    assert!(scatter(&mut t, &mut pool, 0, inline).iter().all(Result::is_ok));
    assert_eq!(t.stats().range_spills, 0, "the inline set is full, not spilled");
    let _held = hog(&mut pool);
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 20 * inline + 10, &[7; 10], false),
        Ok(())
    );
    assert_eq!(t.stats().held_back, 0);
    assert_eq!((t.stats().range_spills, pool.spill_held()), (1, 1));
}

/// The received set gives its slot back once the holes are filled and the ranges merge, while the stream stays open
/// and nothing was read.
#[test]
fn the_received_set_gives_its_slot_back_when_the_holes_are_filled() {
    let mut pool = lent(8);
    let mut t = receiver(&pool);
    let holes = RECV_RANGES as u64 + 1;
    t.on_stream_frame(&mut pool, 0, 10, &[7; 10], false).unwrap();
    let base = pool.used_chunks();
    for k in 1..holes {
        t.on_stream_frame(&mut pool, 0, 20 * k + 10, &[7; 10], false).unwrap();
    }
    assert_eq!(t.stats().range_spills, 1);
    assert_eq!(
        (pool.used_chunks(), pool.spill_held()),
        (base, 1),
        "the received set took a slot, not a chunk"
    );
    let arena = pool.return_spill();
    assert_eq!(
        t.stored_after(&arena, 0, 30),
        Some(30..40),
        "a spilled set reads from the endpoint's arena"
    );
    pool.lend_spill(arena);
    for k in 0..holes {
        t.on_stream_frame(&mut pool, 0, 20 * k, &[7; 10], false).unwrap();
    }
    assert_eq!(
        pool.spill_held(),
        0,
        "one range again: the slot is back, the stream is open"
    );
    let arena = pool.return_spill();
    assert_eq!(t.stored_after(&arena, 0, 0), Some(0..20 * (holes - 1) + 20));
}

/// With no slot left the received ranges refuse the frame that needs one more (`Fragmented`), as before the arena, and
/// both the overflow and the refused spill are counted; a frame that fills a hole needs no new range and is stored.
#[test]
fn an_empty_arena_refuses_the_frame_fragmented_and_counts_it() {
    let mut pool = lent(0);
    let mut t = receiver(&pool);
    let k = RECV_RANGES as u64;
    assert!(scatter(&mut t, &mut pool, 0, k).iter().all(Result::is_ok));
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 20 * k + 10, &[7; 10], false),
        Err(StreamError::Fragmented)
    );
    assert_eq!((t.stats().range_overflows, pool.spill_refused()), (1, 1));
    assert_eq!(t.on_stream_frame(&mut pool, 0, 0, &[7; 10], false), Ok(()));
    assert_eq!(t.read_chunk(&pool, 0).map(<[u8]>::len), Some(20));
}

/// A session holds at most half of the arena: with two slots its first spilled stream takes one, its second is
/// refused though a slot is free, and another session takes that one; a third finds the arena empty and is refused.
/// The one arena is lent to each session's pool in turn, as the endpoint lends it call by call.
#[test]
fn a_session_holds_at_most_half_of_the_arena() {
    let holes = RECV_RANGES as u64 + 1;
    let mut arena = SpillArena::new_boxed(2);
    let mut call = |t: &mut T, pool: &mut BufferPool<'static>, id: StreamId| {
        pool.lend_spill(core::mem::take(&mut arena));
        let _ = scatter(t, pool, id, holes);
        arena = pool.return_spill();
        (t.stats().range_spills, pool.spill_refused(), arena.held())
    };
    let (mut one, mut two, mut three) = (
        BufferPool::new_boxed(64),
        BufferPool::new_boxed(64),
        BufferPool::new_boxed(64),
    );
    let (mut t1, mut t2, mut t3) = (receiver(&one), receiver(&two), receiver(&three));
    assert_eq!(call(&mut t1, &mut one, 0), (1, 0, 1));
    assert_eq!(call(&mut t1, &mut one, 4), (1, 1, 1), "the session holds its share");
    assert_eq!(call(&mut t2, &mut two, 0), (1, 0, 2));
    assert_eq!(
        call(&mut t3, &mut three, 0),
        (0, 1, 2),
        "the arena holds no more than its slots"
    );
}
