//! The transport stream layer, limits: stream ids and caps, held-back streams, stop requests, and the stream credit
//! between two tables.
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

use common::{NO_CAP, Table, drain_control, next_control, pattern, peer, read_all, setup, setup_credit};
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{Config, ControlFrame, NoSource, PeerLimits, StreamError, Streams};

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

#[test]
fn a_stop_request_is_one_control_frame_sent_again_only_when_lost() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 0, 0, b"hello", false).unwrap();
    t.stop_sending(&mut pool, 0, 5).unwrap();
    let frame = ControlFrame::StopSending { id: 0, error_code: 5 };
    assert_eq!(drain_control(&mut t), [frame]);
    assert!(
        drain_control(&mut t).is_empty(),
        "the request was repeated without a loss"
    );
    t.stop_sending(&mut pool, 0, 6).unwrap();
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
    t.stop_sending(&mut pool, 4, 1).unwrap();
    assert!(drain_control(&mut t).is_empty(), "a finished stream was asked to stop");
    t.on_stream_frame(&mut pool, 8, 0, b"y", false).unwrap();
    t.stop_sending(&mut pool, 8, 2).unwrap();
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
    assert_eq!(t.stop_sending(&mut pool, uni, 1), Err(StreamError::StreamState));
    assert_eq!(t.stop_sending(&mut pool, 99, 1), Err(StreamError::UnknownStream));
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

/// A peer stream whose end arrived after a hole is dropped at once when the application gives it up: no stop request
/// goes, its chunks come back, it leaves the table and the peer's stream credit is raised; the retransmission of the
/// missing bytes is taken and dropped.
#[test]
fn a_stop_request_on_a_stream_whose_end_arrived_after_a_hole_frees_it_at_once() {
    let (mut pool, mut rx) = setup_credit(20, |c| c.initial_stream_window = 64 * 1024);
    assert_eq!(rx.advertised_streams(), 2);
    let body = pattern(3000, 5);
    rx.on_stream_frame(&mut pool, 2, 1000, &body[1000..], true).unwrap();
    assert!(rx.read_chunk(&pool, 2).is_none(), "bytes past the hole were readable");
    assert_eq!(rx.open_streams(), 1);
    rx.stop_sending(&mut pool, 2, 9).unwrap();
    // The credit raise is a control frame too, so every frame is read once (`drain_control` leaves raises out).
    let frames: Vec<ControlFrame> = std::iter::from_fn(|| rx.pending_control()).collect();
    assert_eq!(
        frames,
        [ControlFrame::MaxStreams { limit: 3 }],
        "no stop request, and one raise: one admitted plus room for two more"
    );
    assert_eq!(rx.recv_status(2), None, "the stopped stream is still in the table");
    assert_eq!(rx.open_streams(), 0);
    assert_eq!(pool.used_chunks(), 0, "the bytes past the hole are still held");
    rx.on_stream_frame(&mut pool, 2, 0, &body[..1000], false).unwrap();
    assert_eq!(pool.used_chunks(), 0, "the retransmission was stored");
    assert!(rx.read_chunk(&pool, 2).is_none());
}

/// A peer stream we answered with a reset and gave up after its end arrived after a hole leaves the table once the
/// reset is acknowledged.
#[test]
fn a_stopped_stream_with_its_end_and_a_reset_answer_leaves_when_the_reset_is_acknowledged() {
    let (mut pool, mut rx) = setup_credit(20, |c| c.initial_stream_window = 64 * 1024);
    let body = pattern(3000, 6);
    rx.on_stream_frame(&mut pool, 4, 1000, &body[1000..], true).unwrap();
    rx.reset(&mut pool, 4, 5).unwrap();
    rx.stop_sending(&mut pool, 4, 5).unwrap();
    let reset = ControlFrame::ResetStream {
        id: 4,
        error_code: 5,
        final_size: 0,
    };
    assert_eq!(drain_control(&mut rx), [reset], "only our reset goes");
    assert_eq!(pool.used_chunks(), 0, "the bytes past the hole are still held");
    rx.on_control_acked(&mut pool, &reset);
    assert_eq!(rx.recv_status(4), None, "the stream is still in the table");
    assert_eq!(
        rx.open_streams(),
        1,
        "only stream 0, opened with it and never used, is left"
    );
    rx.on_stream_frame(&mut pool, 4, 0, &body[..1000], false).unwrap();
    assert_eq!(pool.used_chunks(), 0, "the retransmission was stored");
}

/// A stream asked to stop whose end then arrives, with no reset to follow, is dropped when the end arrives.
#[test]
fn the_end_arriving_on_a_stream_asked_to_stop_frees_it() {
    let (mut pool, mut rx) = setup_credit(20, |c| c.initial_stream_window = 64 * 1024);
    rx.on_stream_frame(&mut pool, 2, 0, b"abc", false).unwrap();
    rx.stop_sending(&mut pool, 2, 9).unwrap();
    assert_eq!(
        drain_control(&mut rx),
        [ControlFrame::StopSending { id: 2, error_code: 9 }]
    );
    rx.on_stream_frame(&mut pool, 2, 3, b"def", true).unwrap();
    assert_eq!(
        rx.recv_status(2),
        None,
        "the stream waits for a reset that will not come"
    );
    assert_eq!(rx.open_streams(), 0);
    assert_eq!(pool.used_chunks(), 0);
}

/// A stop request not yet sent when the end arrives is never sent: every byte arrived, there is nothing to stop.
#[test]
fn a_stop_not_yet_sent_is_dropped_when_the_end_arrives() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 8, 0, b"y", false).unwrap();
    t.stop_sending(&mut pool, 8, 2).unwrap();
    t.on_stream_frame(&mut pool, 8, 1, b"z", true).unwrap();
    assert!(
        drain_control(&mut t).is_empty(),
        "a stream whose end arrived was asked to stop"
    );
}

/// A stop request reported lost after the end arrived is not sent again.
#[test]
fn a_lost_stop_is_not_sent_again_once_the_end_arrived() {
    let (mut pool, mut t) = setup(1024, |c| c.initial_stream_window = 64 * 1024);
    t.on_stream_frame(&mut pool, 8, 0, b"y", false).unwrap();
    t.stop_sending(&mut pool, 8, 2).unwrap();
    let frame = ControlFrame::StopSending { id: 8, error_code: 2 };
    assert_eq!(drain_control(&mut t), [frame]);
    t.on_stream_frame(&mut pool, 8, 1, b"z", true).unwrap();
    t.on_control_lost(&frame);
    assert!(
        drain_control(&mut t).is_empty(),
        "a stop for a finished stream came back"
    );
}
