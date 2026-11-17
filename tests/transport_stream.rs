//! The transport stream layer, receive side: reassembly, receive windows charged to the pool, credit grants, and the
//! rate-sized window, with the pool accounting checked at every end.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::large_stack_arrays,
    clippy::assert_is_empty,
    clippy::items_after_statements
)]

#[path = "transport_stream_common.rs"]
mod common;

use common::{MIB, NO_CAP, drain_control, drain_frames, pattern, read_all, setup};
use proptest::prelude::*;
use vinc_tests::SplitMix64;
use vinc_transport::stream::pool::CHUNK_SIZE;
use vinc_transport::stream::{ControlFrame, RecvStatus, StreamError};

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
                Ok(_) => {}
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
