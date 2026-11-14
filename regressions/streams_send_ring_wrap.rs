//! A buffered stream copies out bytes that are not the frame's once its ring has wrapped over a released chunk.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    missing_docs
)]

use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use vinc_transport::stream::{Config, NoSource, PeerLimits, StreamSource, Streams};

const CH: usize = CHUNK_SIZE;

fn table<const C: usize>(chunks: usize) -> (BufferPool<'static>, Box<Streams<NoSource, 4, C>>) {
    let pool = BufferPool::new_boxed(chunks);
    let mut config = Config::new(false);
    config.peer = PeerLimits {
        window: 1 << 40,
        max_streams: 100,
    };
    config.credit = false;
    let t = Box::new(Streams::<NoSource, 4, C>::new(&config, &pool));
    (pool, t)
}

/// Byte `i` of the stream: a pattern with period 251, so offsets one chunk apart (16384 = 65 * 251 + 69) differ.
fn byte(i: usize) -> u8 {
    (i % 251) as u8
}

fn bytes(from: usize, len: usize) -> Vec<u8> {
    (from..from + len).map(byte).collect()
}

fn copy<S: StreamSource, const N: usize, const C: usize>(
    t: &mut Streams<S, N, C>,
    pool: &BufferPool<'_>,
    f: &vinc_transport::stream::StreamChunk,
) -> (Result<usize, vinc_transport::stream::StreamError>, Vec<u8>) {
    let mut buf = vec![0u8; f.len];
    let r = t.copy_out(pool, f, &mut buf);
    (r, buf)
}

/// Route 1: an acknowledgement whose cut would split a full retransmission queue leaves the acknowledged byte
/// queued ("sent once more, harmlessly"); the prefix then passes its chunk, the chunk is released, the ring wraps,
/// and the queued resend copies a later chunk's byte as the byte at offset 2.
fn overflow_route<const C: usize>() {
    let (mut pool, mut t) = table::<C>(C + 64);
    let id = t.open_stream(&pool, true).unwrap();
    assert_eq!(t.write(&mut pool, id, &bytes(0, CH), u64::MAX).unwrap(), CH);
    for i in 0..64u64 {
        let f = t.next_stream_frame(1).unwrap();
        assert_eq!((f.offset, f.len), (i, 1));
    }
    let rest = t.next_stream_frame(1 << 20).unwrap();
    assert_eq!((rest.offset, rest.len), (64, CH - 64));
    t.on_acked(&mut pool, id, 64, (CH - 64) as u64, false);
    // 16 lost runs [4j + 1, 4j + 4) (RANGES = 16), the bytes 4j acknowledged.
    for j in 0..16u64 {
        for b in 1..4 {
            t.on_lost(id, 4 * j + b, 1, false);
        }
        t.on_acked(&mut pool, id, 4 * j, 1, false);
    }
    // Byte 2 is acknowledged late: cutting it out of [1, 4) would make 17 runs, so it stays queued.
    t.on_late_acked(&mut pool, id, 2, 1, false);
    assert_eq!(t.stats().range_overflows, 1);
    for j in 0..16u64 {
        for b in 1..4 {
            if (j, b) != (0, 2) {
                t.on_late_acked(&mut pool, id, 4 * j + b, 1, false);
            }
        }
    }
    assert!(t.is_acked(id, 0, CH as u64), "all of chunk 0 is acknowledged");
    assert_eq!(t.send_view(id).unwrap().lost, Some(2), "byte 2 is still queued");
    // Chunk 0 is released; C more chunks fill the ring, chunk C in chunk 0's place.
    let more = C * CH;
    assert_eq!(t.write(&mut pool, id, &bytes(CH, more), u64::MAX).unwrap(), more);
    let f = t.next_stream_frame(1 << 20).unwrap();
    assert_eq!((f.offset, f.len), (2, 1), "the queued resend goes first");
    let (r, got) = copy(&mut t, &pool, &f);
    assert_eq!(r, Ok(1), "the copy reports success");
    assert_eq!(got, bytes(C * CH + 2, 1), "it carries the byte written at offset C * 16384 + 2");
    assert_eq!(got, bytes(2, 1), "a resend must carry the byte written at its offset");
}

#[test]
fn overflow_route_ring_of_2() {
    overflow_route::<2>();
}

#[test]
fn overflow_route_ring_of_1025() {
    overflow_route::<1025>();
}

/// Route 2, no range-map overflow: a retransmission F of a lost range straddling a chunk boundary is in flight; the
/// original frame of its first half is acknowledged late, the prefix passes the chunk, the ring wraps; copying F again
/// (what the connection's tail repair does with the frames of an unacknowledged packet that are not acknowledged in
/// full) yields a later chunk's bytes for F's first half.
#[test]
fn repair_route_ring_of_2() {
    let (mut pool, mut t) = table::<2>(16);
    let id = t.open_stream(&pool, true).unwrap();
    assert_eq!(t.write(&mut pool, id, &bytes(0, 2 * CH), u64::MAX).unwrap(), 2 * CH);
    let g1 = t.next_stream_frame(CH - 10).unwrap();
    let g2a = t.next_stream_frame(10).unwrap();
    let g2b = t.next_stream_frame(10).unwrap();
    assert_eq!((g1.offset, g2a.offset, g2b.offset, g2b.len), (0, CH as u64 - 10, CH as u64, 10));
    t.on_lost(id, g2a.offset, 10, false);
    t.on_lost(id, g2b.offset, 10, false);
    let f = t.next_stream_frame(1 << 20).unwrap();
    assert_eq!((f.offset, f.len), (CH as u64 - 10, 20), "the retransmission spans the chunk boundary");
    let (r, first) = copy(&mut t, &pool, &f);
    assert_eq!((r, first.clone()), (Ok(20), bytes(CH - 10, 20)));
    // The original first half and everything before it are acknowledged: chunk 0 is released.
    t.on_late_acked(&mut pool, id, g2a.offset, 10, false);
    t.on_acked(&mut pool, id, 0, (CH - 10) as u64, false);
    assert!(!t.is_acked(id, f.offset, f.len as u64), "F is not acknowledged in full");
    // One more chunk fits the ring: chunk 2, in chunk 0's place.
    assert_eq!(t.write(&mut pool, id, &bytes(2 * CH, CH), u64::MAX).unwrap(), CH);
    let (r, again) = copy(&mut t, &pool, &f);
    assert_eq!(r, Ok(20), "the copy reports success");
    assert_eq!(&again[..10], &bytes(3 * CH - 10, 10)[..], "its first half is chunk 2's bytes");
    assert_eq!(again, first, "a copy of the same frame must carry the same bytes");
}
