//! The send ring never gives a released chunk's slot to a resend: a frame whose chunk was acknowledged and released is
//! refused or cut, never filled with the bytes of the chunk that took the slot.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

#[path = "transport_stream_common.rs"]
mod common;

use common::{MIB, NO_CAP, pattern};
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use vinc_transport::stream::{Config, NoSource, PeerLimits, StreamError, Streams};

const FRAME: usize = 256;

fn table<const C: usize>() -> (BufferPool<'static>, Box<Streams<NoSource, 8, C>>) {
    let pool = BufferPool::new_boxed(C + 8);
    let mut config = Config::new(false);
    config.peer = PeerLimits {
        window: 64 * MIB,
        max_streams: 100,
    };
    config.credit = false;
    let table = Box::new(Streams::new(&config, &pool));
    (pool, table)
}

/// A resend queued by an acknowledgement that could not cut the full retransmission queue is still queued when the
/// ring wraps over its released chunk; it must not carry the bytes written `C` chunks later.
fn overflow_route<const C: usize>() {
    let (mut pool, mut t) = table::<C>();
    let id = t.open_stream(&pool, true).unwrap();
    let data = pattern((C + 1) * CHUNK_SIZE, 7);
    // One chunk is written and sent as frames of FRAME bytes; the rest waits for room in the ring.
    assert_eq!(t.write(&mut pool, id, &data[..CHUNK_SIZE], NO_CAP).unwrap(), CHUNK_SIZE);
    let mut frames = Vec::new();
    while let Some(c) = t.next_stream_frame(&mut pool, FRAME) {
        let mut buf = vec![0u8; c.len];
        t.copy_out(&mut pool, &c, &mut buf).unwrap();
        frames.push(c);
    }
    let at = |i: usize| (frames[i].offset, frames[i].len as u64);
    // Frames 1 to 3 are one lost range and 15 more at every second frame fill the 16 ranges of the queue.
    for i in (1..4).chain((5..35).step_by(2)) {
        t.on_lost(&mut pool, id, at(i).0, at(i).1, false);
    }
    // The acknowledgement of frame 2 would split the range of frames 1 to 3: it stays queued, acknowledged byte and all.
    t.on_acked(&mut pool, id, at(2).0, at(2).1, false);
    // Everything else of the chunk is acknowledged and the chunk is released.
    for i in (0..frames.len()).filter(|&i| i != 2) {
        t.on_acked(&mut pool, id, at(i).0, at(i).1, false);
    }
    assert_eq!(t.buffered(), 0);
    // The application writes C more chunks over the released slot.
    let mut done = CHUNK_SIZE;
    while done < data.len() {
        let n = t.write(&mut pool, id, &data[done..], NO_CAP).unwrap();
        assert!(n > 0, "the ring must have room after the release");
        done += n;
    }
    while let Some(c) = t.next_stream_frame(&mut pool, FRAME) {
        let mut buf = vec![0u8; c.len];
        match t.copy_out(&mut pool, &c, &mut buf) {
            Ok(_) => assert_eq!(
                buf,
                data[c.offset as usize..][..c.len],
                "a resend must carry the byte written at its offset"
            ),
            Err(e) => assert_eq!(e, StreamError::DataUnavailable),
        }
        assert!(c.offset >= CHUNK_SIZE as u64, "an acknowledged range is not sent again");
    }
}

#[test]
fn overflow_route_ring_of_2() {
    overflow_route::<2>();
}

#[test]
fn overflow_route_ring_of_1025() {
    overflow_route::<1025>();
}

/// A frame across a chunk boundary whose first part is acknowledged on its own: its chunk is released and the ring
/// wraps. Copying the frame again must be refused, never filled with the next chunk's bytes.
#[test]
fn repair_route_ring_of_2() {
    let (mut pool, mut t) = table::<2>();
    let id = t.open_stream(&pool, true).unwrap();
    let data = pattern(3 * CHUNK_SIZE, 9);
    let first = CHUNK_SIZE + 600;
    assert_eq!(t.write(&mut pool, id, &data[..first], NO_CAP).unwrap(), first);
    // The frame that crosses the boundary of chunks 0 and 1.
    let across = loop {
        let c = t.next_stream_frame(&mut pool, 1000).unwrap();
        let mut buf = vec![0u8; c.len];
        t.copy_out(&mut pool, &c, &mut buf).unwrap();
        if c.offset < CHUNK_SIZE as u64 && c.offset + c.len as u64 > CHUNK_SIZE as u64 {
            break c;
        }
    };
    // Its first part is acknowledged through another frame, which releases chunk 0; chunk 2 takes its slot.
    t.on_acked(&mut pool, id, 0, CHUNK_SIZE as u64, false);
    let mut done = first;
    while done < 2 * CHUNK_SIZE + 100 {
        let n = t.write(&mut pool, id, &data[done..], NO_CAP).unwrap();
        assert!(n > 0);
        done += n;
    }
    let mut buf = vec![0u8; across.len];
    assert_eq!(
        t.copy_out(&mut pool, &across, &mut buf),
        Err(StreamError::DataUnavailable),
        "a copy of the same frame must carry the same bytes"
    );
}
