//! Trace generation for the receive and credit path of the stream layer: seeded random runs of a real stream table
//! (`pinc-transport` `Streams`, built with the `trace` feature) over a small pool, recorded as ndjson
//! (`streams.ndjson`) for the TLA+ trace check (`TraceStreams.tla`) and the Lean replay (`Pinc/TraceStreams.lean`).
//!
//! A run opens a server-side table and drives it through the calls the connection makes: stream frames of an honest
//! peer (some out of order, overlapping, past the credit, after the final size, with differing bytes, tiny ones that
//! fragment the stored ranges), resets, consumes of the readable bytes, pending control frames that are then lost
//! or acknowledged, locally opened streams with writes, sends and acknowledgements that take and give back pool
//! chunks, other users of the pool, and the close of the table. After every call the table shows its state
//! (`trace_view`): slots, held chunks, stored ranges, credit, counters, each slot's delivery meter, the
//! ordinal of each stream we opened and whether opens may pass the peer's limit. Every drain of the stream frames is
//! recorded with the streams whose frames left. Runs 25 to 40 are an optimistic dial: opens pass the peer's limit
//! from the start (`set_early`), streams are opened past it with data queued, and the establishment raises the limit
//! and ends that; in runs 37 to 40 the last stream opened early is reset at once, before the limit covers it, so its
//! reset waits for the limit (#432) and leaves once the establishment covers it. The checkers replay each call with the
//! operators of the model (`StreamsOps.tla`, `Pinc.TransportStreams`) and require the state they compute to be the
//! state recorded, the error they compute to be the error returned, the control frame they give to be the one the
//! table gave, and every stream whose frame left to be one they let send.
//!
//! The test asserts what it can itself (the bytes read are the bytes stored, in order and once; the pool never
//! passes its budget; a granted limit never goes down; no stream frame and no control frame of a stream leaves for a
//! stream we opened before the peer's limit covers its ordinal) so it is meaningful without the proof tools. Times are
//! small ticks (the checker has 32-bit integers). The trace is written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_tests::{SplitMix64, big_stack, trace_cases};
use pinc_transport::stream::pool::{BufferPool, CHUNK_SIZE, Chunk};
use pinc_transport::stream::trace::{SlotView, TableView};
use pinc_transport::stream::{Config, ControlFrame, NoSource, PeerLimits, StreamError, Streams};

const N: usize = 4;
const C: usize = 7;
const POOL: usize = 20;
const CH: u64 = CHUNK_SIZE as u64;
/// The initial window: above the four chunks the ledger counts for a stream that has carried no data.
const WINDOW: u64 = 5 * CH;
type Table = Streams<NoSource, N, C>;

const REMOTE: [u64; 6] = [0, 4, 8, 12, 2, 6];
const LOCAL: [u64; 2] = [1, 5];

fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

fn err_name(e: StreamError) -> &'static str {
    match e {
        StreamError::StreamLimit => "StreamLimit",
        StreamError::StreamState => "StreamState",
        StreamError::FlowControl => "FlowControl",
        StreamError::FinalSize => "FinalSize",
        StreamError::Conflict => "Conflict",
        StreamError::TableFull => "TableFull",
        StreamError::Exhausted => "Exhausted",
        StreamError::Fragmented => "Fragmented",
        StreamError::UnknownStream => "UnknownStream",
        StreamError::InvalidConsume => "InvalidConsume",
        _ => "Other",
    }
}

fn opt(x: Option<u64>) -> i64 {
    x.map_or(-1, |v| i64::try_from(v).unwrap())
}

fn list(v: &[u64]) -> String {
    let s: Vec<String> = v.iter().map(ToString::to_string).collect();
    format!("[{}]", s.join(","))
}

fn slot_json(s: &SlotView) -> String {
    if s.id == u64::MAX {
        return r#"{"id":-1}"#.to_string();
    }
    let id = i64::try_from(s.id).unwrap();
    let rs: Vec<String> = s.ranges.iter().map(|(a, z)| format!("[{a},{z}]")).collect();
    format!(
        r#"{{"id":{id},"open":{},"held":{},"rs":[{}],"read":{},"hi":{},"contig":{},"fin":{},"limit":{},"size":{},"pend":{},"defer":{},"rst":{},"obs":{},"sdone":{},"srst":{},"stop":{},"qcode":{},"scode":{},"ord":{},"ms":{},"mb":{},"mr":{},"sp":{}}}"#,
        b(s.open),
        list(&s.held),
        rs.join(","),
        s.read,
        s.highest,
        s.contig,
        opt(s.fin),
        s.limit,
        s.size,
        b(s.pending),
        b(s.deferred),
        opt(s.reset),
        b(s.observed),
        b(s.send_done),
        s.send_reset,
        s.stop,
        opt(s.stop_code),
        opt(s.send_code),
        s.ordinal,
        opt(s.meter.0),
        s.meter.1,
        s.meter.2,
        b(s.spilled)
    )
}

fn view_json(v: &TableView) -> String {
    let slots: Vec<String> = v.slots.iter().map(slot_json).collect();
    format!(
        r#"{{"slots":[{}],"rn":[{},{}],"lo":[{},{}],"rl":{},"ll":{},"ext":{},"hw":{},"ad":[{},{}],"adp":{},"early":{}}}"#,
        slots.join(","),
        v.remote_next[0],
        v.remote_next[1],
        v.local_opened[0],
        v.local_opened[1],
        v.remote_live,
        v.local_live,
        v.ext,
        v.high_water,
        v.admit[0],
        v.admit[1],
        b(v.admit_pend),
        b(v.early)
    )
}

/// The byte the honest peer sends at `off` of stream `id`.
fn src(id: u64, off: u64) -> u8 {
    ((id.wrapping_mul(31) ^ off.wrapping_mul(7) ^ (off >> 5)) & 0xff) as u8
}

struct Run<'o> {
    t: Box<Table>,
    pool: BufferPool<'static>,
    rng: SplitMix64,
    out: &'o mut String,
    id: u32,
    now: u64,
    /// The bytes stored per stream id and offset.
    shadow: std::collections::HashMap<u64, Vec<Option<u8>>>,
    hog: Vec<Chunk>,
    control: Vec<ControlFrame>,
    inflight: Vec<(u64, u64, u64, bool)>,
    max_limit: std::collections::HashMap<u64, u64>,
    /// Peer streams whose frame was held back (no slot, answered `Exhausted`) and not admitted since.
    held: std::collections::HashSet<u64>,
    /// A frame opened a skipped lower stream with its own, inside the credit.
    jumped: bool,
    /// Streams we opened that a recorded table showed past the peer's limit.
    past: std::collections::HashSet<u64>,
    /// A stream once past the limit sent a frame after a raise covered it.
    released: bool,
    /// A control frame of a stream once past the limit left after a raise covered it.
    ctl_released: bool,
    /// The least limit the establishment gives: the ordinal of a stream reset while past the limit (0: any).
    cover: u64,
}

impl Run<'_> {
    fn below(&mut self, n: u64) -> u64 {
        self.rng.next_u64() % n.max(1)
    }

    fn view(&self) -> TableView {
        self.t.trace_view(&self.pool)
    }

    fn slot(&self, id: u64) -> Option<SlotView> {
        self.view().slots.into_iter().find(|s| s.id == id)
    }

    /// Record an event with the view after it, and check what the test can check itself.
    fn log(&mut self, head: &str) {
        let v = self.view();
        assert!(self.pool.used_chunks() <= POOL, "the pool passed its budget");
        for s in &v.slots {
            if s.id != u64::MAX && s.ordinal > v.admit[0] {
                self.past.insert(s.id);
            }
            if s.id != u64::MAX {
                let m = self.max_limit.entry(s.id).or_insert(0);
                assert!(s.limit >= *m, "a limit went down");
                *m = s.limit;
                if s.ranges.is_empty() {
                    self.shadow.remove(&s.id);
                }
            }
        }
        let run = self.id;
        let _ = writeln!(self.out, r#"{{"t":"st","run":{run},{head},"v":{}}}"#, view_json(&v));
    }

    fn note_stored(&mut self, id: u64, lo: u64, hi: u64) {
        let Some(s) = self.slot(id) else { return };
        let sh = self.shadow.entry(id).or_default();
        if sh.len() < hi as usize {
            sh.resize(hi as usize, None);
        }
        for o in lo..hi {
            if sh[o as usize].is_none() && s.ranges.iter().any(|&(a, z)| a <= o && o < z) {
                sh[o as usize] = Some(src(id, o));
            }
        }
    }

    fn frame(&mut self, id: u64, off: u64, len: usize, fin: bool, corrupt: bool) {
        let mut data: Vec<u8> = (0..len as u64).map(|i| src(id, off + i)).collect();
        if corrupt && len > 0 {
            let at = self.below(len as u64) as usize;
            data[at] ^= 0x5a;
        }
        let read = self.slot(id).map_or(0, |s| s.read);
        let lo = off.max(read);
        let diff = self.shadow.get(&id).is_some_and(|sh| {
            (lo..off + len as u64).any(|o| {
                sh.get(o as usize)
                    .copied()
                    .flatten()
                    .is_some_and(|stored| stored != data[(o - off) as usize])
            })
        });
        let before = self.view();
        let res = self.t.on_stream_frame(&mut self.pool, id, off, &data, fin);
        let err = res.as_ref().err().map_or("ok", |e| err_name(*e));
        let after = self.view();
        let class = usize::from(id & 2 != 0);
        let opened = after.remote_next[class] - before.remote_next[class];
        let admitted_before: u64 = before.remote_next.iter().sum();
        self.jumped |= res.is_ok() && opened >= 2 && admitted_before + opened <= before.admit[1];
        // A peer stream that does not fit is held back: nothing is stored, charged or counted, and the packet goes
        // unacknowledged; the opener's retransmission is admitted once there is room.
        let held_back = res == Err(StreamError::Exhausted) && after.slots.iter().all(|s| s.id != id);
        let mut admitted = false;
        if held_back && id & 1 == 0 {
            assert_eq!(before, after, "a held-back stream changed the table");
            self.held.insert(id);
        } else if res.is_ok() && self.held.remove(&id) {
            assert!(after.slots.iter().any(|s| s.id == id) || after.remote_next[class] > id >> 2);
            admitted = true;
        }
        if res.is_ok() && !corrupt {
            self.note_stored(id, lo, off + len as u64);
        } else if res.is_ok() {
            // a corrupted frame stored where nothing was: its bytes are what the peer sent
            self.note_corrupt(id, lo, off, &data);
        }
        self.log(&format!(
            r#""op":"frame","id":{id},"off":{off},"len":{len},"fin":{},"diff":{},"err":"{err}","opened":{opened},"admitted":{}"#,
            b(fin),
            b(diff),
            b(admitted)
        ));
    }

    fn note_corrupt(&mut self, id: u64, lo: u64, off: u64, data: &[u8]) {
        let Some(s) = self.slot(id) else { return };
        let sh = self.shadow.entry(id).or_default();
        let hi = off + data.len() as u64;
        if sh.len() < hi as usize {
            sh.resize(hi as usize, None);
        }
        for o in lo..hi {
            if sh[o as usize].is_none() && s.ranges.iter().any(|&(a, z)| a <= o && o < z) {
                sh[o as usize] = Some(data[(o - off) as usize]);
            }
        }
    }

    fn pick_frame(&mut self) {
        let ids: Vec<u64> = REMOTE.iter().chain(LOCAL.iter()).copied().collect();
        let id = ids[self.below(ids.len() as u64) as usize];
        let s = self.slot(id);
        let (read, limit) = s.as_ref().map_or((0, WINDOW), |s| (s.read, s.limit));
        let (off, len) = match self.below(10) {
            0 => (limit.saturating_sub(self.below(64)), 1 + self.below(200)),
            1 => (read + self.below(4 * CH), 1 + self.below(32)),
            2 => (read + self.below(2 * CH), 1 + self.below(3 * CH / 2)),
            _ => {
                let hi = s.as_ref().map_or(0, |s| s.highest).max(read);
                (
                    hi.min(limit) - self.below(hi.min(limit).saturating_sub(read) + 1).min(200),
                    1 + self.below(CH / 2),
                )
            }
        };
        let fin = self.below(8) == 0;
        let corrupt = self.below(30) == 0;
        self.frame(id, off, len as usize, fin, corrupt);
    }

    fn burst(&mut self) {
        // Many one-byte frames at even offsets of one stream fragment its stored ranges past the 96 it can track.
        let id = REMOTE[self.below(4) as usize];
        let limit = self.slot(id).map_or(WINDOW, |s| s.limit);
        for k in 0..110u64 {
            let off = 2 * k + 8;
            if off < limit {
                self.frame(id, off, 1, false, false);
            }
        }
    }

    fn consume(&mut self) {
        let ids: Vec<u64> = self
            .view()
            .slots
            .iter()
            .filter(|s| s.id != u64::MAX)
            .map(|s| s.id)
            .collect();
        if ids.is_empty() {
            return;
        }
        let id = ids[self.below(ids.len() as u64) as usize];
        self.now += self.below(30);
        let srtt = [0u64, 10, 20][self.below(3) as usize];
        let mut n = 0usize;
        let (pick, part) = (self.below(4), 1 + self.below(64) as usize);
        if let Some(chunk) = self.t.read_chunk(&self.pool, id) {
            let s = self.slot(id).unwrap();
            let sh = self.shadow.get(&id);
            for (i, byte) in chunk.iter().enumerate() {
                let stored = sh.and_then(|sh| sh.get(s.read as usize + i)).copied().flatten();
                assert_eq!(
                    Some(*byte),
                    stored,
                    "stream {id}: a byte read is not the byte stored at that offset"
                );
            }
            n = if pick == 0 { chunk.len().min(part) } else { chunk.len() };
        } else if self.below(10) == 0 {
            n = 1 + self.below(8) as usize;
        }
        let before = self.slot(id).map_or(0, |s| s.read);
        let res = self.t.consume(&mut self.pool, id, n, self.now, srtt);
        let err = res.as_ref().err().map_or("ok", |e| err_name(*e));
        if res.is_ok() {
            assert!(
                self.slot(id)
                    .is_none_or(|s| s.read == before + n as u64 || s.reset.is_some())
            );
        }
        let now = self.now;
        self.log(&format!(
            r#""op":"consume","id":{id},"n":{n},"now":{now},"srtt":{srtt},"err":"{err}""#
        ));
    }

    fn pending(&mut self) {
        let v = self.view();
        let f = self.t.pending_control();
        // A control frame of a stream leaves only once the peer's limit covers its ordinal (#432).
        if let Some(
            ControlFrame::ResetStream { id, .. }
            | ControlFrame::StopSending { id, .. }
            | ControlFrame::MaxStreamData { id, .. },
        ) = f
        {
            let ord = v.slots.iter().find(|s| s.id == id).map_or(0, |s| s.ordinal);
            assert!(
                ord <= v.admit[0],
                "a control frame of stream {id} left before the peer's limit of {} covered its ordinal {ord}",
                v.admit[0]
            );
            self.ctl_released |= self.past.contains(&id);
        }
        let head = match f {
            None => r#""op":"pending","kind":"none","fid":-1,"max":0"#.to_string(),
            Some(ControlFrame::MaxStreamData { id, max }) => {
                self.control.push(ControlFrame::MaxStreamData { id, max });
                format!(r#""op":"pending","kind":"msd","fid":{id},"max":{max}"#)
            }
            Some(ControlFrame::ResetStream {
                id,
                error_code,
                final_size,
            }) => {
                self.control.push(ControlFrame::ResetStream {
                    id,
                    error_code,
                    final_size,
                });
                format!(r#""op":"pending","kind":"reset","fid":{id},"max":{error_code}"#)
            }
            Some(ControlFrame::StopSending { id, error_code }) => {
                self.control.push(ControlFrame::StopSending { id, error_code });
                format!(r#""op":"pending","kind":"stop","fid":{id},"max":{error_code}"#)
            }
            Some(ControlFrame::MaxStreams { limit }) => {
                self.control.push(ControlFrame::MaxStreams { limit });
                format!(r#""op":"pending","kind":"msts","fid":-1,"max":{limit}"#)
            }
        };
        self.log(&head);
    }

    fn settle_control(&mut self) {
        if self.control.is_empty() {
            return;
        }
        let k = self.below(self.control.len() as u64) as usize;
        let f = self.control.swap_remove(k);
        let lose = self.below(3) == 0;
        match (f, lose) {
            (ControlFrame::MaxStreamData { id, max }, true) => {
                self.t.on_control_lost(&f);
                self.log(&format!(r#""op":"lostmsd","id":{id},"max":{max}"#));
            }
            (ControlFrame::ResetStream { id, .. }, true) => {
                self.t.on_control_lost(&f);
                self.log(&format!(r#""op":"lostreset","id":{id}"#));
            }
            (ControlFrame::ResetStream { id, .. }, false) => {
                self.t.on_control_acked(&mut self.pool, &f);
                self.log(&format!(r#""op":"ackedreset","id":{id}"#));
            }
            (ControlFrame::StopSending { id, .. }, true) => {
                self.t.on_control_lost(&f);
                self.log(&format!(r#""op":"loststop","id":{id}"#));
            }
            (ControlFrame::StopSending { id, .. }, false) => {
                self.t.on_control_acked(&mut self.pool, &f);
                self.log(&format!(r#""op":"ackedstop","id":{id}"#));
            }
            (ControlFrame::MaxStreams { limit }, true) => {
                self.t.on_control_lost(&f);
                self.log(&format!(r#""op":"lostmsts","limit":{limit}"#));
            }
            (ControlFrame::MaxStreamData { .. } | ControlFrame::MaxStreams { .. }, false) => {}
        }
    }

    fn peer_reset(&mut self) {
        let id = REMOTE[self.below(REMOTE.len() as u64) as usize];
        let hi = self.slot(id).map_or(0, |s| s.highest);
        let fs = hi + [0, 0, 1, 100][self.below(4) as usize];
        let res = self.t.on_reset_stream(&mut self.pool, id, 1, fs);
        let err = res.as_ref().err().map_or("ok", |e| err_name(*e));
        self.log(&format!(r#""op":"reset","id":{id},"code":1,"fs":{fs},"err":"{err}""#));
    }

    /// Ask the peer to stop sending on a stream we receive on (code 7).
    fn stop_request(&mut self) {
        let ids = self.live_ids();
        if ids.is_empty() {
            return;
        }
        let id = ids[self.below(ids.len() as u64) as usize];
        let res = self.t.stop_sending(&mut self.pool, id, 7);
        let err = res.as_ref().err().map_or("ok", |e| err_name(*e));
        self.log(&format!(r#""op":"stopreq","id":{id},"code":7,"err":"{err}""#));
    }

    /// A stop request arrived for a stream we send on: the send half is reset with the peer's code (7), a writer
    /// sees the stream finished, and the reset frame that follows carries the code.
    fn peer_stop(&mut self) {
        let ids: Vec<u64> = REMOTE.iter().chain(LOCAL.iter()).copied().collect();
        let id = ids[self.below(ids.len() as u64) as usize];
        let res = self.t.on_stop_sending(&mut self.pool, id, 7);
        let err = res.as_ref().err().map_or("ok", |e| err_name(*e));
        let fresh = res == Ok(true);
        if fresh {
            assert_eq!(
                self.t.write(&mut self.pool, id, b"x", u64::MAX),
                Err(StreamError::Finished),
                "a stopped stream still takes writes"
            );
        }
        self.log(&format!(
            r#""op":"onstop","id":{id},"code":7,"err":"{err}","fresh":{}"#,
            b(fresh)
        ));
    }

    /// The peer raised the number of streams we may open (`MAX_STREAMS`).
    fn max_streams(&mut self) {
        let limit = 2 + self.below(3);
        self.t.on_max_streams(limit);
        self.log(&format!(r#""op":"maxstreams","limit":{limit}"#));
    }

    fn open_local(&mut self) {
        let _ = self.t.open_stream(&self.pool, true);
        self.log(r#""op":"open""#);
    }

    fn live_ids(&self) -> Vec<u64> {
        self.view()
            .slots
            .iter()
            .filter(|s| s.id != u64::MAX)
            .map(|s| s.id)
            .collect()
    }

    fn send_side(&mut self) {
        let ids = self.live_ids();
        if ids.is_empty() {
            return;
        }
        let id = ids[self.below(ids.len() as u64) as usize];
        match self.below(6) {
            0 | 1 => {
                let n = (1 + self.below(3 * CH)) as usize;
                let data = vec![0xab; n];
                let _ = self.t.write(&mut self.pool, id, &data, u64::MAX);
                let ext = self.view().ext;
                self.log(&format!(r#""op":"ext","ext":{ext}"#));
            }
            2 => {
                let _ = self.t.finish(id);
            }
            3 => self.drain(),
            4 => {
                if self.inflight.is_empty() {
                    return;
                }
                let k = self.below(self.inflight.len() as u64) as usize;
                let (fid, off, len, fin) = self.inflight.swap_remove(k);
                self.t.on_acked(&mut self.pool, fid, off, len, fin);
                let v = self.view();
                let done = v.slots.iter().find(|s| s.id == fid).is_none_or(|s| s.send_done);
                self.log(&format!(r#""op":"finish","id":{fid},"done":{}"#, b(done)));
            }
            _ => {
                let _ = self.t.reset(&mut self.pool, id, 9);
                self.log(&format!(r#""op":"appreset","id":{id},"code":9"#));
            }
        }
    }

    /// Send every stream frame the table gives, and record which streams they were for. A stream we opened sends
    /// nothing before the peer's limit covers its ordinal.
    fn drain(&mut self) {
        let v = self.view();
        let mut ids = Vec::new();
        while let Some(ch) = self.t.next_stream_frame(&mut self.pool, 1 << 20) {
            let ord = v.slots.iter().find(|s| s.id == ch.id).map_or(0, |s| s.ordinal);
            assert!(
                ord <= v.admit[0],
                "stream {} left before the peer's limit of {} covered its ordinal {ord}",
                ch.id,
                v.admit[0]
            );
            self.released |= self.past.contains(&ch.id);
            let mut buf = vec![0u8; ch.len];
            let _ = self.t.copy_out(&mut self.pool, &ch, &mut buf);
            self.inflight.push((ch.id, ch.offset, ch.len as u64, ch.fin));
            ids.push(ch.id);
        }
        self.log(&format!(r#""op":"sent","ids":{}"#, list(&ids)));
    }

    /// While opens may pass the peer's limit: open a few streams and queue data on each, as an application does on an
    /// optimistic dial.
    fn early_burst(&mut self) {
        for _ in 0..4 {
            let before = self.view().local_opened[0];
            self.open_local();
            let after = self.view().local_opened[0];
            if after > before {
                // the bidirectional stream just opened, on the server side
                let id = before * 4 + 1;
                let _ = self.t.write(&mut self.pool, id, &[0xab; 10], u64::MAX);
                let ext = self.view().ext;
                self.log(&format!(r#""op":"ext","ext":{ext}"#));
            }
        }
    }

    /// The peer's record arrives: its limits are applied and opens no longer pass them; then the table sends. After an
    /// early reset the limit covers the stream reset, and the control frames are asked for.
    fn establish(&mut self) {
        let limit = (self.view().admit[0] + self.below(4)).max(self.cover);
        self.t.set_peer_limits(&PeerLimits {
            window: 1 << 20,
            max_streams: limit,
        });
        self.t.set_early(false);
        self.log(&format!(r#""op":"establish","limit":{limit}"#));
        self.drain();
        if self.cover > 0 {
            for _ in 0..4 {
                self.pending();
            }
        }
    }

    /// Reset the last stream opened while it is past the peer's limit, and ask for the control frames: its reset waits
    /// for the limit as its data does (#432).
    fn reset_last_early(&mut self) {
        let v = self.view();
        let Some(last) = v
            .slots
            .iter()
            .filter(|s| s.id != u64::MAX && s.ordinal > v.admit[0])
            .max_by_key(|s| s.ordinal)
        else {
            return;
        };
        let (id, ordinal) = (last.id, last.ordinal);
        let _ = self.t.reset(&mut self.pool, id, 9);
        self.log(&format!(r#""op":"appreset","id":{id},"code":9"#));
        self.cover = ordinal;
        for _ in 0..2 {
            self.pending();
        }
    }

    fn ext_users(&mut self) {
        if self.hog.is_empty() || self.below(2) == 0 {
            if let Ok(c) = self.pool.alloc_chunk() {
                self.hog.push(c);
            }
        } else if let Some(c) = self.hog.pop() {
            self.pool.free_chunk(c);
            self.t.regrant(&self.pool);
        }
        let ext = self.view().ext;
        self.log(&format!(r#""op":"ext","ext":{ext}"#));
    }

    fn step(&mut self) {
        match self.below(100) {
            0..=39 => self.pick_frame(),
            40..=59 => self.consume(),
            60..=69 => self.pending(),
            70..=77 => self.settle_control(),
            78..=81 => self.peer_reset(),
            82..=84 if self.view().early => self.early_burst(),
            82..=84 => self.open_local(),
            85..=91 => self.send_side(),
            92..=93 => self.stop_request(),
            94..=95 => self.peer_stop(),
            96..=97 => self.ext_users(),
            98 if self.below(2) == 0 => self.max_streams(),
            98 => self.burst(),
            _ => {
                self.t.close_all(&mut self.pool);
                self.shadow.clear();
                self.inflight.clear();
                self.control.clear();
                self.max_limit.clear();
                self.log(r#""op":"close""#);
                if self.view().early {
                    self.early_burst();
                }
            }
        }
    }
}

/// What a run reached: a frame that opened a skipped lower stream inside the credit, a stream we opened past the
/// peer's limit, such a stream sending once a raise covered it, and a control frame of one leaving then.
#[allow(clippy::struct_excessive_bools, reason = "independent things a run may reach")]
struct Reached {
    jumped: bool,
    past: bool,
    released: bool,
    ctl_released: bool,
}

/// A run's table and pool on the test's own constants, with nothing logged yet.
fn new_run(seed: u64, out: &mut String, run: u32) -> Run<'_> {
    let mut config = Config::new(false);
    config.initial_stream_window = WINDOW;
    config.max_stream_window = 6 * CH;
    config.max_streams = 2;
    config.peer = PeerLimits {
        window: 1 << 20,
        max_streams: 2,
    };
    let pool = BufferPool::new_boxed(POOL);
    let t = Box::new(Table::new(&config, &pool));
    Run {
        t,
        pool,
        rng: SplitMix64::traced(seed),
        out,
        id: run,
        now: 0,
        shadow: std::collections::HashMap::new(),
        hog: Vec::new(),
        control: Vec::new(),
        inflight: Vec::new(),
        max_limit: std::collections::HashMap::new(),
        held: std::collections::HashSet::new(),
        jumped: false,
        past: std::collections::HashSet::new(),
        released: false,
        ctl_released: false,
        cover: 0,
    }
}

/// One seeded run; `early` makes it an optimistic dial, and `reset_early` resets its last early stream at once.
fn run(seed: u64, out: &mut String, run: u32, early: bool, reset_early: bool) -> Reached {
    let mut r = new_run(seed, out, run);
    r.log(r#""op":"init""#);
    // An optimistic dial: the application opens streams and queues data before the peer's limits are known
    // (`Connection::allow_early_streams`), and the establishment applies them some time later.
    let establish_at = if early {
        r.t.set_early(true);
        r.t.set_peer_limits(&PeerLimits {
            window: 16 * 1024,
            max_streams: 0,
        });
        r.log(r#""op":"early""#);
        r.early_burst();
        if reset_early {
            r.reset_last_early();
        }
        20 + r.below(100)
    } else {
        u64::MAX
    };
    for k in 0..220 {
        if k == establish_at {
            r.establish();
        }
        r.step();
    }
    r.log(r#""op":"end""#);
    Reached {
        jumped: r.jumped,
        past: !r.past.is_empty(),
        released: r.released,
        ctl_released: r.ctl_released,
    }
}

impl Run<'_> {
    /// Consume `n` bytes of stream `id` at tick 0 with no rate (the window stays its initial size).
    fn eat(&mut self, id: u64, n: usize) {
        let res = self.t.consume(&mut self.pool, id, n, 0, 0);
        let err = res.as_ref().err().map_or("ok", |e| err_name(*e));
        self.log(&format!(
            r#""op":"consume","id":{id},"n":{n},"now":0,"srtt":0,"err":"{err}""#
        ));
    }

    /// Other users of the pool take `k` chunks, one `ext` event each.
    fn take(&mut self, k: usize) {
        for _ in 0..k {
            self.hog.push(self.pool.alloc_chunk().unwrap());
            let ext = self.view().ext;
            self.log(&format!(r#""op":"ext","ext":{ext}"#));
        }
    }

    /// The first steps of both scripted runs: peer stream 0 sends 10340 bytes in chunk 0 and the reader takes them all
    /// (an eighth of the window, so the grant moves and the stream is charged 5 chunks, of which the first charge
    /// counts 4); then peer stream 4 opens with an empty frame, with the end when `fin`.
    fn script_open(&mut self, fin: bool) {
        self.log(r#""op":"init""#);
        self.frame(0, 0, 10340, false, false);
        self.eat(0, 10340);
        self.frame(4, 0, 0, fin, false);
        assert!(self.slot(4).is_some(), "the empty frame did not open stream 4");
    }
}

/// Run 41: a credit raise the stream admission rule makes and the rule before it (the whole ledger) does not. Stream
/// 4 ends and 11 chunks go to other users: 8 chunks are left, 4 of them beside the first charges counted, so one stream
/// fits (the whole ledger counts 5, and none does).
fn script_raise(out: &mut String) {
    let mut r = new_run(41, out, 41);
    r.script_open(true);
    r.take(11);
    r.eat(4, 0);
    let _ = r.t.finish(4);
    r.drain();
    let k = r.inflight.iter().position(|e| e.0 == 4).unwrap();
    let (fid, off, len, fin) = r.inflight.swap_remove(k);
    r.t.on_acked(&mut r.pool, fid, off, len, fin);
    r.log(&format!(r#""op":"finish","id":{fid},"done":true"#));
    for _ in 0..4 {
        r.pending();
    }
    assert!(
        r.control
            .iter()
            .any(|f| matches!(f, ControlFrame::MaxStreams { limit: 3 })),
        "no MAX_STREAMS of 3 was queued"
    );
    r.log(r#""op":"end""#);
}

/// Run 42: a local stream the stream admission rule opens and the rule before it refuses. Stream 4 holds its first
/// charge, other users take 7 chunks, 12 are left: four chunks for each of streams 0, 4 and the new one fit (the
/// whole ledger counts 5 for stream 0 and 13 do not).
fn script_open_local(out: &mut String) {
    let mut r = new_run(42, out, 42);
    r.script_open(false);
    r.take(7);
    r.open_local();
    assert_eq!(r.view().local_opened[0], 1, "the local stream was refused");
    assert!(r.slot(1).is_some(), "the local stream has no slot");
    r.log(r#""op":"end""#);
}

#[test]
fn stream_table_runs_match_the_models() {
    big_stack(|| {
        let mut out = String::new();
        let (mut jumped, mut past, mut released, mut ctl_released) = (false, false, false, false);
        // every few runs in the quick profile: the early-dial runs (ids above 24) and the reset ones (above 36) stay
        let every = trace_cases(3, 1) as u32;
        for run_id in (1..=40u32).filter(|id| id % every == 0) {
            let r = run(
                0x5354_5245_414d_0000 + u64::from(run_id),
                &mut out,
                run_id,
                run_id > 24,
                run_id > 36,
            );
            jumped |= r.jumped;
            past |= r.past;
            released |= r.released;
            ctl_released |= r.ctl_released;
        }
        script_raise(&mut out);
        script_open_local(&mut out);
        assert!(jumped, "no frame opened a skipped stream inside the credit");
        assert!(
            pinc_tests::soaking() || past,
            "no stream was opened past the peer's limit"
        );
        assert!(
            pinc_tests::soaking() || released,
            "no stream opened past the peer's limit sent once a raise covered it"
        );
        assert!(
            pinc_tests::soaking() || ctl_released,
            "no control frame of a stream opened past the peer's limit left once a raise covered it"
        );
        for op in [
            "frame",
            "consume",
            "pending",
            "lostmsd",
            "lostmsts",
            "maxstreams",
            "lostreset",
            "ackedreset",
            "reset",
            "open",
            "ext",
            "finish",
            "appreset",
            "stopreq",
            "onstop",
            "loststop",
            "ackedstop",
            "close",
            "early",
            "establish",
            "sent",
        ] {
            assert!(
                pinc_tests::soaking() || out.contains(&format!(r#""op":"{op}""#)),
                "no {op} event"
            );
        }
        // The runs reach the interesting steps: a peer stream held back and admitted later, stop requests sent and lost, implicit opens, a deferred grant, a conflict, a stream
        // whose ranges outgrew their inline array and spilled into a pool chunk, a limit raised, a reset acknowledged.
        for needle in [
            r#""kind":"stop""#,
            r#""fresh":true"#,
            r#""admitted":true"#,
            r#""opened":2"#,
            r#""err":"Conflict""#,
            r#""sp":true"#,
            r#""err":"FlowControl""#,
            r#""err":"Exhausted""#,
            r#""defer":true"#,
            r#""kind":"msd""#,
            r#""kind":"msts""#,
            r#""kind":"reset""#,
            // run 41: the credit raised to 3 once stream 4 ended; run 42: stream 1 opened beside two others
            r#""run":41,"op":"pending","kind":"msts","fid":-1,"max":3"#,
            r#""run":42,"op":"open","#,
        ] {
            assert!(
                pinc_tests::soaking() || out.contains(needle),
                "the runs never reach {needle}"
            );
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("streams.ndjson"), &out).unwrap();
        }
    });
}
