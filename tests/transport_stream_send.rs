//! The transport stream layer, send side: the peer window and send buffer cap, lost ranges and retransmission,
//! source-backed streams, resets, and urgency order.
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
use std::cell::RefCell;

use common::{NO_CAP, Src, drain_control, drain_frames, next_control, pattern, peer, setup};
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use vinc_transport::stream::{Config, ControlFrame, RecvStatus, StreamError, Streams};

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
