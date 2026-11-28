//! Reproductions of bugs the `transport*` properties found in `pinc-transport`. Each test fails on the code it was
//! found on and names the bug.
#![allow(clippy::unwrap_used, clippy::cast_possible_truncation)]

use pinc_transport::recovery::{FrameRef, FrameRefs, Recovery, SECOND, Sent};
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{Config, ControlFrame, NoSource, PeerLimits, RecvStatus, Streams};

/// The probe timer near the end of the clock: after it fires at its deadline, it must move to a later deadline.
///
/// Expected: `recovery::deadline_after` documents the rule every timer of the module follows: "A deadline saturated
/// at u64::MAX could never be later than a call made at u64::MAX, so it would fire on every call." A timer that fired
/// at `t` is next due after `t`, so a driver that waits for `next_timeout()` makes progress.
///
/// Actual: `Recovery::pto_deadline` (crates/pinc-transport/src/recovery/pto.rs:57) adds the backed-off probe timeout
/// to the send time with `saturating_add`. When that sum passes `u64::MAX` the deadline is `u64::MAX`; firing at
/// `u64::MAX` leaves `next_timeout() == Some(u64::MAX)`, so every further call fires again at the same instant and
/// each firing declares another packet lost and bumps the probe count. The shrunk counterexample of
/// `recovery_matches_the_model_near_the_end_of_the_clock` is the same: replay `EPHYRA_REPLAY=18109605289167201268:1`.
///
/// Who can trigger it: the local application, through the clock it passes to the connection (a clock within a probe
/// timeout of `u64::MAX` nanoseconds, for example a monotonic clock with a large base). A remote peer cannot.
#[test]
fn probe_timer_stays_due_after_firing_at_the_end_of_the_clock() {
    let mut rec = Recovery::<48>::new(1200);
    let start = u64::MAX - SECOND / 2;
    for _ in 0..5 {
        let pn = rec.next_pn();
        let mut frames = FrameRefs::new();
        frames
            .push(FrameRef::Stream {
                id: 0,
                offset: pn * 100,
                len: 100,
                fin: false,
            })
            .unwrap();
        rec.on_packet_sent(Sent {
            pn,
            time: start,
            size: 100,
            path: 0,
            is_repair: false,
            is_mtu_probe: false,
            frames,
        })
        .unwrap();
    }
    let mut fired = Vec::new();
    for _ in 0..4 {
        let Some(t) = rec.next_timeout() else { break };
        rec.on_timeout(t, |_| {});
        fired.push(t);
        let next = rec.next_timeout();
        assert!(
            next.is_none_or(|n| n > t),
            "the timer fired at {t} and is still due at {next:?} (fired at {fired:?})"
        );
    }
}

fn pattern(len: usize, seed: u64) -> Vec<u8> {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

/// Two streams whose windows ran out stay at zero credit for good on a receiver whose pool has free chunks, with
/// nothing in flight, nothing buffered and the application reading as fast as data comes.
///
/// Expected: the `stream` module docs: "A window grant is made only while the ledger, with it, fits the bytes the
/// pool has left", and `Streams::regrant`: a deferred grant is tried again on every release of pool chunks and every
/// change of the credit ledger, "so a grant is never left waiting for the application to read something: with nothing
/// readable it never would". With the reader drained and pool room left (4 of 6 chunks free here), a stream that
/// still has bytes to receive gets credit again, and an honest transfer completes.
///
/// Actual: after stream 10 ends, streams 6 and 14 sit at their limits (80,000 and 60,000) with every byte received
/// and read; the receiver queues no MAX_STREAM_DATA again, in any number of rounds. `Streams::grant`
/// (crates/pinc-transport/src/stream/table.rs:736-762) only ever asks for the whole candidate `read_off + win.size`
/// (`Recv::due`, recv.rs:219), and `consume` (table.rs:725) grew `win.size` to the ceiling, half the pool (3 chunks
/// here). That demand plus `reserved()` (the first charge kept for the one stream the raised stream credit still
/// promises, 2 chunks) passes the free bytes, so the grant is deferred; nothing ever frees a chunk, and a smaller
/// grant that fits is never tried. The window size never shrinks, so the stall is permanent.
///
/// Who can trigger it: the local configuration (a small buffer pool, as a memory-bound node or `BufferPool::from_slab`
/// gives) together with any peer that sends a few streams in parallel: the honest peer's transfer hangs.
#[test]
fn a_stream_at_the_end_of_its_window_is_never_granted_more_on_a_small_pool() {
    let mut rpool = BufferPool::new_boxed(6);
    let mut spool = BufferPool::new_boxed(6);
    let mut rcfg = Config::new(false);
    rcfg.initial_stream_window = 20_000;
    rcfg.max_streams = 4;
    let mut r = Box::new(Streams::<NoSource, 8, 1025>::new(&rcfg, &rpool));
    let mut scfg = Config::new(true);
    scfg.peer = PeerLimits {
        window: r.recv_window(),
        max_streams: r.advertised_streams(),
    };
    let mut s = Box::new(Streams::<NoSource, 8, 1025>::new(&scfg, &spool));
    let lens = [0usize, 102_653, 174_953, 76_185];
    let data: Vec<Vec<u8>> = lens
        .iter()
        .enumerate()
        .map(|(i, &n)| pattern(n, i as u64 + 1))
        .collect();
    let mut ids: Vec<u64> = Vec::new();
    let mut written = [0usize; 4];
    let mut finished = [false; 4];
    let mut read: Vec<Vec<u8>> = vec![Vec::new(); 4];
    let mut ended = [false; 4];
    let mut now = 1_000_000_000u64;
    for _ in 0..2000 {
        if ids.len() < lens.len()
            && let Ok(id) = s.open_stream(&spool, false)
        {
            ids.push(id);
        }
        for (i, &id) in ids.iter().enumerate() {
            if !finished[i] {
                written[i] += s.write(&mut spool, id, &data[i][written[i]..], u64::MAX).unwrap();
                if written[i] == lens[i] {
                    s.finish(id).unwrap();
                    finished[i] = true;
                }
            }
        }
        for _ in 0..64 {
            let Some(chunk) = s.next_stream_frame(&mut spool, 1200) else {
                break;
            };
            let mut buf = vec![0u8; chunk.len];
            s.copy_out(&mut spool, &chunk, &mut buf).unwrap();
            let len = chunk.len as u64;
            if r.on_stream_frame(&mut rpool, chunk.id, chunk.offset, &buf, chunk.fin)
                .is_ok()
            {
                s.on_acked(&mut spool, chunk.id, chunk.offset, len, chunk.fin);
            } else {
                s.on_lost(&mut spool, chunk.id, chunk.offset, len, chunk.fin);
            }
        }
        for (i, &id) in ids.iter().enumerate() {
            while let Some(c) = r.read_chunk(&rpool, id) {
                let n = c.len();
                read[i].extend_from_slice(c);
                now += 1_000_000;
                if r.consume(&mut rpool, id, n, now, 10_000_000) == Ok(RecvStatus::Finished) {
                    ended[i] = true;
                }
            }
            if r.consume(&mut rpool, id, 0, now, 10_000_000) == Ok(RecvStatus::Finished) {
                ended[i] = true;
            }
        }
        r.regrant(&rpool);
        s.regrant(&spool);
        while let Some(f) = r.pending_control() {
            match f {
                ControlFrame::MaxStreamData { id, max } => s.on_max_stream_data(&spool, id, max).unwrap(),
                ControlFrame::MaxStreams { limit } => s.on_max_streams(limit),
                _ => {}
            }
            r.on_control_acked(&mut rpool, &f);
        }
        if ended.iter().all(|e| *e) {
            assert!(read == data, "the bytes read differ from those written");
            return;
        }
    }
    panic!(
        "the transfer stalled: read {:?} of {lens:?}, receiver pool chunks in use {}, stream credit {} for {} opened, windows {:?}",
        read.iter().map(Vec::len).collect::<Vec<_>>(),
        rpool.used_chunks(),
        r.advertised_streams(),
        ids.len(),
        ids.iter().map(|id| r.stream_recv_window(*id)).collect::<Vec<_>>()
    );
}
