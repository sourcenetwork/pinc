//! The transport stream layer, pool accounting: the pool grant property, acknowledged-range memory, allocation-free hot
//! paths, and the ledger charge of a local stream window.
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

use common::{Table, next_control, peer, read_all, setup};
use proptest::prelude::*;
use vinc_tests::measure;
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use vinc_transport::stream::{Config, ControlFrame, RecvStatus, StreamError, StreamSource, Streams};

vinc_tests::install_counting_allocator!();

// ---- pool grant property --------------------------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum Op {
    /// An empty frame that opens stream `k` (or does nothing if it exists).
    Open(usize),
    Frame(usize, usize),
    Consume(usize),
    Hog,
    Unhog,
}

fn op() -> impl Strategy<Value = Op> {
    prop_oneof![
        (0usize..6).prop_map(Op::Open),
        (0usize..6, 1usize..30_000).prop_map(|(k, n)| Op::Frame(k, n)),
        (0usize..6).prop_map(Op::Consume),
        Just(Op::Hog),
        Just(Op::Unhog),
    ]
}

proptest! {
    /// Whenever a stream is admitted or a window grows, the pool bytes promised to the peer (the credit granted and not
    /// yet received, and the first charges kept for the streams it may still open) fit the pool, or are no more than
    /// they were before the operation: another user of the pool taking chunks (a `Hog`: the send buffers and the datagram
    /// queues do) can put the promises past what is left, and no admission or grant may add to that.
    ///
    /// This is not a weaker guarantee for the peer's data. A frame that arrives inside a granted window when the pool
    /// has no chunk left for it (another holder took it) is refused by `Recv::on_data` as `StreamError::Exhausted`
    /// before anything is stored; the connection treats that as a shortage, drops the packet unacknowledged and counts
    /// it in `held_back`, and the peer sends it again once chunks are free. Nothing is lost, and the pool is never over
    /// its budget.
    #[test]
    fn granted_credit_fits_the_pool_at_every_admission_and_grant(ops in prop::collection::vec(op(), 1..150)) {
        let mut pool = BufferPool::new_boxed(24);
        let mut config = Config::new(false);
        config.initial_stream_window = 48 * 1024;
        config.max_streams = 4;
        config.peer = peer();
        let mut t = Box::new(Table::new(&config, &pool));
        let mut sent = [0u64; 6];
        let mut hogs = Vec::new();
        let mut now = 0u64;
        for op in ops {
            now += 1000;
            let limits = |t: &Table| -> Vec<Option<u64>> {
                (0..6u64).map(|k| t.stream_recv_window(4 * k).map(|w| w.1)).collect()
            };
            let before = limits(&t);
            let opened_before = t.open_streams();
            let promised_before = t.promised();
            match op {
                Op::Open(k) => {
                    match t.on_stream_frame(&mut pool, 4 * k as u64, sent[k], &[], false) {
                        Ok(()) | Err(StreamError::Exhausted | StreamError::StreamLimit) => {}
                        Err(e) => prop_assert!(false, "unexpected {e}"),
                    }
                    if t.open_streams() > opened_before {
                        prop_assert!(t.promised() <= pool.available_bytes().max(promised_before));
                    }
                }
                Op::Frame(k, n) => {
                    let data = vec![1u8; n];
                    match t.on_stream_frame(&mut pool, 4 * k as u64, sent[k], &data, false) {
                        Ok(()) => sent[k] += n as u64,
                        Err(StreamError::Exhausted | StreamError::StreamLimit
                            | StreamError::FlowControl | StreamError::Fragmented) => {}
                        Err(e) => prop_assert!(false, "unexpected {e}"),
                    }
                }
                Op::Consume(k) => {
                    let id = 4 * k as u64;
                    let n = t.read_chunk(&pool, id).map_or(0, <[u8]>::len);
                    let _ = t.consume(&mut pool, id, n, now, 2000);
                    let after = limits(&t);
                    if before.iter().zip(&after).any(|(b, a)| a > b && b.is_some()) {
                        prop_assert!(t.promised() <= pool.available_bytes().max(promised_before));
                    }
                }
                Op::Hog => {
                    if let Ok(c) = pool.alloc_chunk() {
                        hogs.push(c);
                    }
                }
                Op::Unhog => {
                    if let Some(c) = hogs.pop() {
                        pool.free_chunk(c);
                    }
                }
            }
            // Acknowledge refusals so the queue turns over.
            while let Some(f) = next_control(&mut t) {
                if matches!(f, ControlFrame::ResetStream { .. }) {
                    t.on_control_acked(&mut pool, &f);
                }
            }
        }
        t.close_all(&mut pool);
        prop_assert_eq!(pool.used_chunks(), hogs.len());
    }
}

#[test]
fn a_stream_has_data_to_send_while_new_bytes_or_a_retransmission_wait() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    assert!(!t.has_data_to_send());
    t.write(&mut pool, id, &[1u8; 2800], 1 << 20).unwrap();
    assert!(t.has_data_to_send(), "new bytes wait");
    let mut frames = Vec::new();
    while let Some(f) = t.next_stream_frame(1400) {
        frames.push((f.offset, f.len as u64));
    }
    assert_eq!(frames.len(), 2);
    assert!(!t.has_data_to_send(), "everything is sent and nothing is lost");
    t.on_lost(id, frames[0].0, frames[0].1, false);
    assert!(t.has_data_to_send(), "a lost range waits to be sent again");
    let again = t.next_stream_frame(1400).unwrap();
    assert!(!t.has_data_to_send());
    t.on_acked(&mut pool, id, again.offset, again.len as u64, false);
    t.on_acked(&mut pool, id, frames[1].0, frames[1].1, false);
    assert!(!t.has_data_to_send());
}

#[test]
fn sixty_four_holes_of_acknowledged_ranges_are_remembered_without_sending_any_again() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
    t.write(&mut pool, id, &[1u8; 1400 * 130], 1 << 20).unwrap();
    let mut frames = Vec::new();
    while let Some(f) = t.next_stream_frame(1400) {
        frames.push((f.offset, f.len as u64));
    }
    assert_eq!(frames.len(), 130);
    // Every second frame is acknowledged first: 64 disjoint ranges above the hole at the start.
    for &(offset, len) in frames.iter().skip(1).step_by(2).take(64) {
        t.on_acked(&mut pool, id, offset, len, false);
    }
    assert!(
        !t.has_data_to_send(),
        "an acknowledged range was queued to be sent again"
    );
    for &(offset, len) in frames.iter().skip(1).step_by(2).take(64) {
        assert!(t.is_acked(id, offset, len));
    }
}

// ---- allocation ---------------------------------------------------------------------------------------------------

#[test]
fn hot_paths_do_not_allocate() {
    let (mut pool, mut t) = setup(1024, |_| {});
    let id = t.open_stream(&pool, true).unwrap();
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
            t.set_urgency(id, (round % 4) as u8).unwrap();
            assert_eq!(t.write(&mut pool, id, &payload, 1 << 20).unwrap(), 1400);
            assert!(t.granted_unreceived() <= pool.available_bytes());
            let frame = t.next_stream_frame(1400).unwrap();
            t.copy_out(&pool, &frame, &mut buf).unwrap();
            t.on_lost(id, frame.offset, frame.len as u64, false);
            let again = t.next_stream_frame(1400).unwrap();
            t.copy_out(&pool, &again, &mut buf).unwrap();
            t.on_acked(&mut pool, id, again.offset, again.len as u64, false);
            let _ = t.poll_writable(1 << 20);
            while next_control(&mut t).is_some() {}
        }
    });
    assert_eq!(stats.count(), 0);
}

#[test]
fn holding_a_stream_back_does_not_allocate() {
    let (mut pool, mut t) = setup(1024, |c| {
        c.max_streams = 1;
        c.initial_stream_window = 16 * 1024;
    });
    t.on_stream_frame(&mut pool, 0, 0, &[1; 10], false).unwrap();
    let stats = measure(|| {
        for _ in 0..100 {
            assert_eq!(
                t.on_stream_frame(&mut pool, 4, 0, &[1; 10], false),
                Err(StreamError::Exhausted)
            );
            assert!(next_control(&mut t).is_none());
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
    let id = t.open_stream(&pool, false).unwrap();
    t.open_source(id, Plain(&data), data.len() as u64).unwrap();
    let mut buf = [0u8; 1500];
    let stats = measure(|| {
        while let Some(c) = t.next_stream_frame(1400) {
            assert_eq!(t.copy_out(&pool, &c, &mut buf).unwrap(), c.len);
        }
    });
    assert_eq!(stats.count(), 0);
}

#[test]
fn a_local_stream_window_is_charged_to_the_ledger() {
    // Regression: a peer stream stored an eighth of the window and the application read it, so its window moved to a
    // span that is not chunk-aligned (three chunks, one held, two of credit). Opening a local stream then added two chunks of
    // credit the ledger never checked, and the credit granted exceeded what the pool could cover.
    let chunk = CHUNK_SIZE as u64;
    let (mut pool, mut t) = setup(4, |c| {
        c.initial_stream_window = 2 * chunk;
        c.max_stream_window = 3 * chunk;
    });
    let eighth = (2 * chunk / 8) as usize;
    t.on_stream_frame(&mut pool, 0, 0, &vec![1; eighth], false).unwrap();
    assert_eq!(read_all(&mut t, &mut pool, 0).len(), eighth);
    assert_eq!(t.granted_unreceived(), 2 * chunk);
    assert!(t.granted_unreceived() <= pool.available_bytes());
    assert_eq!(t.open_stream(&pool, true), Err(StreamError::Exhausted));
    assert!(t.granted_unreceived() <= pool.available_bytes());
    // A stream with no receive half takes no credit, so it opens.
    t.open_stream(&pool, false).unwrap();
    // The credit comes back when the peer stream ends: the local stream then opens and is counted.
    t.on_stream_frame(&mut pool, 0, eighth as u64, b"", true).unwrap();
    assert_eq!(t.recv_status(0), Some(RecvStatus::Finished));
    t.consume(&mut pool, 0, 0, 0, 0).unwrap();
    let id = t.open_stream(&pool, true).unwrap();
    assert_eq!(t.stream_recv_window(id), Some((2 * chunk, 2 * chunk)));
    assert!(t.granted_unreceived() <= pool.available_bytes());
}
