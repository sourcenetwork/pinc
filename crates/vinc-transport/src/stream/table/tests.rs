//! Unit tests of the stream table that read its private state.

use super::*;
use crate::stream::{ControlFrame, StreamChunk};

fn written<const N: usize, const C: usize>(t: &mut Streams<NoSource, N, C>) -> usize {
    t.slots.written_iter_mut().count()
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
    let next = |t: &mut Streams<NoSource, 72, 65>, pool: &BufferPool<'_>| {
        let c = t.next_stream_frame(1200)?;
        t.copy_out(pool, &c, &mut [0u8; 1200]).unwrap();
        Some(c)
    };
    for _ in 0..4 {
        let id = t.open_stream(&pool, false).unwrap();
        t.write(&mut pool, id, &[1; 10], u64::MAX).unwrap();
        t.finish(id).unwrap();
    }
    let sent: alloc::vec::Vec<StreamChunk> = core::iter::from_fn(|| next(&mut t, &pool)).collect();
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
    t.on_lost(top.id, top.offset, top.len as u64, top.fin);
    assert_eq!(
        next(&mut t, &pool).map(|c| c.id),
        Some(top.id),
        "the retransmission on the top slot is sent"
    );
    let reused = t.open_stream(&pool, false).unwrap();
    t.write(&mut pool, reused, &[2; 10], u64::MAX).unwrap();
    assert_eq!(t.used(), 4, "a reused slot sits below the mark");
    assert_eq!(next(&mut t, &pool).map(|c| c.id), Some(reused));
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
    t.on_lost(reused, 0, 10, false);
    assert_eq!(
        next(&mut t, &pool).map(|c| c.id),
        Some(reused),
        "the slot under the fallen mark is still scanned"
    );
    let mut fresh = BufferPool::new_boxed(512);
    t.reinit(&cfg, &fresh);
    assert_eq!((written(&mut t), t.used()), (0, 0));
    let id = t.open_stream(&fresh, false).unwrap();
    t.write(&mut fresh, id, &[3; 10], u64::MAX).unwrap();
    assert_eq!((t.used(), next(&mut t, &fresh).map(|c| c.id)), (1, Some(id)));
}

/// A stream the peer opened stops counting against its limit when its answer has left, but it holds its slot until
/// the answer is acknowledged. While it is the top slot the mark stays on it, so a lost answer is still found and
/// sent again; the mark falls only when the acknowledgement frees the slot.
#[test]
fn a_peer_stream_whose_place_was_given_back_stays_under_the_mark_until_it_is_acknowledged() {
    let mut pool = BufferPool::new_boxed(512);
    let mut t: Streams<NoSource, 72, 65> = Streams::new(&Config::new(false), &pool);
    let next = |t: &mut Streams<NoSource, 72, 65>, pool: &BufferPool<'_>| {
        let c = t.next_stream_frame(1200)?;
        t.copy_out(pool, &c, &mut [0u8; 1200]).unwrap();
        Some(c)
    };
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
    let sent: alloc::vec::Vec<StreamChunk> = core::iter::from_fn(|| next(&mut t, &pool)).collect();
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
    t.on_lost(top.id, top.offset, top.len as u64, top.fin);
    let again = next(&mut t, &pool).unwrap();
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
