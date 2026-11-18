//! Unit tests of the stream table that read its private state.

use super::*;
use crate::stream::{ControlFrame, StreamChunk};

fn written<const N: usize, const C: usize>(t: &mut Streams<NoSource, N, C>) -> usize {
    t.slots.written_iter_mut().count()
}

/// The next frame to send, copied out as the connection would.
fn next(t: &mut Streams<NoSource, 72, 65>, pool: &mut BufferPool<'_>) -> Option<StreamChunk> {
    let c = t.next_stream_frame(pool, 1200)?;
    t.copy_out(pool, &c, &mut [0u8; 1200]).unwrap();
    Some(c)
}

/// A table of 72 slots writes only the slots its streams took, the lowest first, and a new connection's reset makes
/// every slot blank again without writing any.
#[test]
fn only_the_slots_streams_took_are_written() {
    // Room for the windows of the streams opened here beside the credit the peer was given.
    let pool = BufferPool::new_boxed(512);
    let mut cfg = Config::new(true);
    cfg.peer = PeerLimits {
        window: 64 * 1024,
        max_streams: 16,
    };
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&cfg, &pool);
    assert_eq!(written(&mut t), 0);
    assert_eq!(t.slots.iter().count(), 72);
    let first = t.open_stream(&pool, true).unwrap();
    t.open_stream(&pool, true).unwrap();
    t.open_stream(&pool, false).unwrap();
    assert_eq!(written(&mut t), 3);
    assert_eq!(t.open_streams(), 3);
    assert!(t.send_view(first).is_some());
    t.reinit(&cfg, &pool);
    assert_eq!((written(&mut t), t.open_streams()), (0, 0));
    assert!(t.send_view(first).is_none());
    t.open_stream(&pool, true).unwrap();
    assert_eq!(written(&mut t), 1);
}

/// The scans for frames to send stop at the mark, one past the highest live slot. The highest slot keeps its
/// retransmission and its reset after every slot below it was freed; a reused slot below the mark is found; when
/// the top stream ends the mark falls to the highest one still live, though the slots above stay written; after a
/// reset of the table it is 0.
#[test]
fn the_highest_slot_ever_used_is_scanned_after_the_slots_below_it_are_freed() {
    let mut pool = BufferPool::new_boxed(512);
    let mut cfg = Config::new(true);
    cfg.peer = PeerLimits {
        window: 64 * 1024,
        max_streams: 16,
    };
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&cfg, &pool);
    for _ in 0..4 {
        let id = t.open_stream(&pool, false).unwrap();
        t.write(&mut pool, id, &[1; 10], u64::MAX).unwrap();
        t.finish(id).unwrap();
    }
    let sent: alloc::vec::Vec<StreamChunk> = core::iter::from_fn(|| next(&mut t, &mut pool)).collect();
    assert_eq!(sent.len(), 4);
    for c in sent.get(..3).unwrap() {
        t.on_acked(&mut pool, c.id, c.offset, c.len as u64, c.fin);
    }
    assert_eq!(
        (t.open_streams(), t.used()),
        (1, 4),
        "the lower three are freed, the mark stays at the top slot"
    );
    let top = *sent.get(3).unwrap();
    t.on_lost(&mut pool, top.id, top.offset, top.len as u64, top.fin);
    assert_eq!(
        next(&mut t, &mut pool).map(|c| c.id),
        Some(top.id),
        "the retransmission on the top slot is sent"
    );
    let reused = t.open_stream(&pool, false).unwrap();
    t.write(&mut pool, reused, &[2; 10], u64::MAX).unwrap();
    assert_eq!(t.used(), 4, "a reused slot sits below the mark");
    assert_eq!(next(&mut t, &mut pool).map(|c| c.id), Some(reused));
    t.reset(&mut pool, top.id, 9).unwrap();
    let reset = t.pending_control();
    assert!(
        matches!(reset, Some(ControlFrame::ResetStream { id, .. }) if id == top.id),
        "the reset of the top slot is sent"
    );
    t.on_control_acked(&mut pool, &reset.unwrap());
    assert_eq!(
        (t.used(), written(&mut t)),
        (1, 4),
        "the top stream ended: the mark falls to the reused slot, the slots above stay written"
    );
    t.on_lost(&mut pool, reused, 0, 10, false);
    assert_eq!(
        next(&mut t, &mut pool).map(|c| c.id),
        Some(reused),
        "the slot under the fallen mark is still scanned"
    );
    let mut fresh = BufferPool::new_boxed(512);
    t.reinit(&cfg, &fresh);
    assert_eq!((written(&mut t), t.used()), (0, 0));
    let id = t.open_stream(&fresh, false).unwrap();
    t.write(&mut fresh, id, &[3; 10], u64::MAX).unwrap();
    assert_eq!((t.used(), next(&mut t, &mut fresh).map(|c| c.id)), (1, Some(id)));
}

/// A stream the peer opened stops counting against its limit when its answer has left, but it holds its slot until
/// the answer is acknowledged. While it is the top slot the mark stays on it, so a lost answer is still found and
/// sent again; the mark falls only when the acknowledgement frees the slot.
#[test]
fn a_peer_stream_whose_place_was_given_back_stays_under_the_mark_until_it_is_acknowledged() {
    let mut pool = BufferPool::new_boxed(512);
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&Config::new(false), &pool);
    // Three requests on streams of the peer (a client: ids 0, 4, 8), each read and answered.
    for id in [0u64, 4, 8] {
        t.on_stream_frame(&mut pool, id, 0, &[7; 20], true).unwrap();
        while let Some(k) = t.read_chunk(&pool, id).map(<[u8]>::len) {
            t.consume(&mut pool, id, k, 0, 0).unwrap();
        }
        t.consume(&mut pool, id, 0, 0, 0).unwrap();
        t.write(&mut pool, id, &[9; 30], u64::MAX).unwrap();
        t.finish(id).unwrap();
    }
    let live = t.remote_live;
    let sent: alloc::vec::Vec<StreamChunk> = core::iter::from_fn(|| next(&mut t, &mut pool)).collect();
    assert_eq!(
        (sent.len(), live, t.remote_live),
        (3, 3, 0),
        "every place is given back"
    );
    assert_eq!(
        (t.open_streams(), t.used()),
        (3, 3),
        "the slots are held for the acknowledgements"
    );
    for c in sent.get(..2).unwrap() {
        t.on_acked(&mut pool, c.id, c.offset, c.len as u64, c.fin);
    }
    assert_eq!(
        (t.open_streams(), t.used()),
        (1, 3),
        "the mark stays on the unacknowledged top stream"
    );
    let top = *sent.get(2).unwrap();
    t.on_lost(&mut pool, top.id, top.offset, top.len as u64, top.fin);
    let again = next(&mut t, &mut pool).unwrap();
    assert_eq!(
        (again.id, again.offset, again.fin),
        (top.id, top.offset, top.fin),
        "the lost answer is sent again"
    );
    t.on_acked(&mut pool, again.id, again.offset, again.len as u64, again.fin);
    assert_eq!(
        (t.open_streams(), t.used()),
        (0, 0),
        "acknowledged: the slot is free and the mark falls"
    );
}

/// The stream control frames queued now, in the order they would be sent.
fn stream_controls(t: &mut Streams<NoSource, 8, 65>) -> alloc::vec::Vec<ControlFrame> {
    core::iter::from_fn(|| t.pending_control())
        .filter(|f| !matches!(f, ControlFrame::MaxStreams { .. }))
        .collect()
}

/// A reset and a stop request on a stream opened past the peer's limit wait for the limit as its data does: the peer
/// does not know the stream before its limit covers it.
#[test]
fn control_frames_of_streams_opened_before_the_peers_limit_wait_for_it() {
    let mut pool = BufferPool::new_boxed(512);
    let mut t: Streams<NoSource, 8, 65> = Streams::new(&Config::new(true), &pool);
    t.set_early(true);
    t.set_peer_limits(&PeerLimits {
        window: 16 * 1024,
        max_streams: 0,
    });
    let first = t.open_stream(&pool, true).unwrap();
    let second = t.open_stream(&pool, true).unwrap();
    t.reset(&mut pool, first, 1).unwrap();
    t.stop_sending(&mut pool, second, 2).unwrap();
    assert!(
        stream_controls(&mut t).is_empty(),
        "a control frame went out before the peer's limit was known"
    );
    t.set_peer_limits(&PeerLimits {
        window: 16 * 1024,
        max_streams: 1,
    });
    t.set_early(false);
    let sent = stream_controls(&mut t);
    assert!(
        matches!(sent.as_slice(), [ControlFrame::ResetStream { id, error_code: 1, .. }] if *id == first),
        "only the stream the limit covers sends its control frame: {sent:?}"
    );
    t.on_max_streams(2);
    let more = stream_controls(&mut t);
    assert!(
        matches!(more.as_slice(), [ControlFrame::StopSending { id, error_code: 2 }] if *id == second),
        "the stream past the limit sends its control frame once credit covers it: {more:?}"
    );
}

/// Streams opened before the peer's limits are known send nothing; when the limit arrives the ones it covers go out in
/// the order they were opened, and the rest wait for credit. After the limits are known an open past them is refused.
#[test]
fn streams_opened_before_the_peers_limit_wait_for_it_in_order() {
    let mut pool = BufferPool::new_boxed(512);
    let mut t: Streams<NoSource, 8, 65> = Streams::new(&Config::new(true), &pool);
    t.set_early(true);
    t.set_peer_limits(&PeerLimits {
        window: 16 * 1024,
        max_streams: 0,
    });
    let ids: alloc::vec::Vec<StreamId> = (0..3)
        .map(|_| {
            let id = t.open_stream(&pool, false).unwrap();
            assert_eq!(t.write(&mut pool, id, &[7; 10], u64::MAX).unwrap(), 10);
            t.finish(id).unwrap();
            id
        })
        .collect();
    assert!(
        t.next_stream_frame(&mut pool, 1200).is_none(),
        "a stream went out before the peer's limit was known"
    );
    assert!(!t.has_data_to_send());
    t.set_peer_limits(&PeerLimits {
        window: 64 * 1024,
        max_streams: 2,
    });
    t.set_early(false);
    let sent: alloc::vec::Vec<StreamId> =
        core::iter::from_fn(|| t.next_stream_frame(&mut pool, 1200).map(|c| c.id)).collect();
    assert_eq!(
        sent,
        ids.get(..2).unwrap(),
        "the streams within the limit go out in the order they were opened"
    );
    assert!(!t.has_data_to_send());
    assert!(matches!(t.open_stream(&pool, false), Err(StreamError::StreamLimit)));
    t.on_max_streams(3);
    let more: alloc::vec::Vec<StreamId> =
        core::iter::from_fn(|| t.next_stream_frame(&mut pool, 1200).map(|c| c.id)).collect();
    assert_eq!(
        more,
        ids.get(2..).unwrap(),
        "the stream past the limit goes out once credit covers it"
    );
}

/// A stream's window follows what its own reader drains. Before #159 one meter measured the whole connection and every
/// stream that read a byte took twice that rate as its window: sixteen streams on a long path asked the pool for sixteen
/// times the credit the connection moved, grants were deferred, and the last streams crawled at one window per round
/// trip. Here stream 0 drains 32 KiB in a round trip and grows to 64 KiB; stream 4 reads 16 bytes and keeps its
/// initial window.
#[test]
fn a_window_follows_the_rate_of_its_own_stream() {
    const KIB: u64 = 1024;
    const SRTT: u64 = 1_000;
    fn read(t: &mut Streams<NoSource, 72, 65>, pool: &mut BufferPool<'_>, id: u64, now: u64) {
        while let Some(k) = t.read_chunk(pool, id).map(<[u8]>::len) {
            t.consume(pool, id, k, now, SRTT).unwrap();
        }
    }
    let mut pool = BufferPool::new_boxed(1024);
    let mut cfg = Config::new(false);
    cfg.initial_stream_window = 16 * KIB;
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&cfg, &pool);
    let block = [5u8; 16 * 1024];
    t.on_stream_frame(&mut pool, 0, 0, &block, false).unwrap();
    read(&mut t, &mut pool, 0, 0);
    t.on_stream_frame(&mut pool, 0, 16 * KIB, &block, false).unwrap();
    read(&mut t, &mut pool, 0, SRTT);
    t.on_stream_frame(&mut pool, 4, 0, &block[..16], false).unwrap();
    read(&mut t, &mut pool, 4, SRTT);
    let size = |t: &Streams<NoSource, 72, 65>, id| t.stream_recv_window(id).unwrap().0;
    assert_eq!(size(&t, 0), 2 * 32 * KIB, "stream 0 drained 32 KiB in a round trip");
    assert_eq!(
        size(&t, 4),
        16 * KIB,
        "stream 4 has drained 16 bytes: it keeps the initial window"
    );
}

/// The bytes a table reserves are the table and the room of its slots.
#[cfg(feature = "alloc")]
#[test]
fn the_bytes_a_table_reserves_are_its_own_size_and_its_slots() {
    let own = core::mem::size_of::<Streams<NoSource, 4, 5>>();
    let slot = core::mem::size_of::<Slot<NoSource, 5>>();
    assert!(slot > 0);
    assert_eq!(Streams::<NoSource, 4, 5>::BYTES, own + 4 * slot);
}

/// Scattered drops leave a stream more holes than its inline range set holds. Before #478 the frame that needed one
/// more range was refused (`Fragmented`) and its packet went unacknowledged, so the sender declared it lost and sent it
/// again though it had arrived. Now the set spills into one arena slot: every frame is stored, the stream reads through
/// once the holes fill, and the slot is back in the arena when the stream ends.
#[test]
fn a_stream_with_more_holes_than_its_inline_ranges_spills_into_one_arena_slot() {
    let mut pool = BufferPool::new_boxed(64);
    pool.lend_spill(crate::stream::spill::SpillArena::new_boxed(8));
    let mut cfg = Config::new(false);
    cfg.initial_stream_window = 64 * 1024;
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&cfg, &pool);
    let holes = crate::stream::RECV_RANGES as u64 + 32;
    for k in 0..holes {
        let got = t.on_stream_frame(&mut pool, 0, 20 * k + 10, &[7; 10], false);
        assert_eq!(got, Ok(()), "frame {k} of {holes} refused");
    }
    assert_eq!(
        (pool.used_chunks(), pool.spill_held()),
        (1, 1),
        "one ring chunk, and the spill slot"
    );
    assert_eq!(t.stats().range_spills, 1, "the spill is counted once");
    assert_eq!(t.stats().range_overflows, 0);
    for k in 0..holes {
        t.on_stream_frame(&mut pool, 0, 20 * k, &[7; 10], false).unwrap();
    }
    t.on_stream_frame(&mut pool, 0, 20 * holes, &[], true).unwrap();
    let mut read = 0;
    while let Some(k) = t.read_chunk(&pool, 0).map(<[u8]>::len) {
        t.consume(&mut pool, 0, k, 0, 0).unwrap();
        read += k as u64;
    }
    t.consume(&mut pool, 0, 0, 0, 0).unwrap();
    assert_eq!(read, 20 * holes);
    assert_eq!(
        (pool.used_chunks(), pool.spill_held()),
        (0, 0),
        "the ring chunk and the spill slot are back"
    );
}

/// The spill slot is the bound: a stream holds at most `SLOT_RANGES` (512) received ranges. The frame that would need
/// one more is refused (`Fragmented`) and counted, and the set is as it was, so a later frame that fills a hole
/// is stored.
#[test]
fn a_stream_whose_spilled_ranges_are_full_refuses_the_next_hole_and_counts_it() {
    let mut pool = BufferPool::new_boxed(64);
    pool.lend_spill(crate::stream::spill::SpillArena::new_boxed(8));
    let mut cfg = Config::new(false);
    cfg.initial_stream_window = 64 * 1024;
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&cfg, &pool);
    let full = crate::stream::spill::SLOT_RANGES as u64;
    for k in 0..full {
        let got = t.on_stream_frame(&mut pool, 0, 20 * k + 10, &[7; 10], false);
        assert_eq!(got, Ok(()), "frame {k} of {full} refused");
    }
    assert_eq!(t.stats().range_overflows, 0);
    let got = t.on_stream_frame(&mut pool, 0, 20 * full + 10, &[7; 10], false);
    assert_eq!(
        got,
        Err(StreamError::Fragmented),
        "range {} is past the spill slot",
        full + 1
    );
    assert_eq!(t.stats().range_overflows, 1, "the refusal is counted");
    assert_eq!(t.stats().range_spills, 1);
    assert_eq!(
        t.on_stream_frame(&mut pool, 0, 0, &[7; 10], false),
        Ok(()),
        "filling a hole needs no new range"
    );
    assert_eq!(t.read_chunk(&pool, 0).map(<[u8]>::len), Some(20));
}

/// A grant deferred for want of pool room goes out when a sibling's read frees the room, though the waiting stream has
/// nothing left to read. Stream 0 reads its whole 32 KiB window while two chunks are held elsewhere (as the datagram
/// queues hold them), so its next window does not fit and is deferred at its limit. Stream 4 then reads its 32 KiB and
/// ends: its chunks go back, and stream 0's grant is retried in that same read. A grant retried only for the stream
/// that read would leave stream 0 at its limit for good; the two-stream spill model never reaches this state in a
/// config small enough to check, so this test covers it.
#[test]
fn a_deferred_grant_goes_out_when_a_sibling_read_frees_room() {
    const KIB: u64 = 1024;
    let mut pool = BufferPool::new_boxed(6);
    let mut cfg = Config::new(false);
    cfg.initial_stream_window = 32 * KIB;
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&cfg, &pool);
    let block = alloc::vec![5u8; 32 * 1024];
    t.on_stream_frame(&mut pool, 4, 0, &block, true).unwrap();
    t.on_stream_frame(&mut pool, 0, 0, &block, false).unwrap();
    let held = [pool.alloc_chunk().unwrap(), pool.alloc_chunk().unwrap()];
    let read = |t: &mut Streams<NoSource, 72, 65>, pool: &mut BufferPool<'_>, id| {
        while let Some(k) = t.read_chunk(pool, id).map(<[u8]>::len) {
            t.consume(pool, id, k, 0, 0).unwrap();
        }
    };
    read(&mut t, &mut pool, 0);
    assert_eq!(
        t.stream_recv_window(0),
        Some((32 * KIB, 32 * KIB)),
        "stream 0 waits at its limit"
    );
    assert!(
        t.slot(t.find(0).unwrap()).unwrap().recv.win.deferred,
        "its grant is deferred"
    );
    read(&mut t, &mut pool, 4);
    assert_eq!(
        t.stream_recv_window(0),
        Some((32 * KIB, 64 * KIB)),
        "the sibling's read freed room and stream 0's grant went out"
    );
    for c in held {
        pool.free_chunk(c);
    }
}
