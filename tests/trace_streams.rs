//! Trace generation for the receive and credit path of the stream layer: seeded random runs of a real stream table
//! (`vinc-transport` `Streams`, built with the `trace` feature) over a small pool, recorded as ndjson
//! (`streams.ndjson`) for the TLA+ trace check (`TraceStreams.tla`) and the Lean replay (`Vinc/TraceStreams.lean`).
//!
//! A run opens a server-side table and drives it through the calls the connection makes: stream frames of an honest
//! peer (some out of order, overlapping, past the credit, after the final size, with differing bytes, tiny ones that
//! fragment the stored ranges), resets, consumes of the readable bytes, pending control frames that are then lost
//! or acknowledged, locally opened streams with writes, sends and acknowledgements that take and give back pool
//! chunks, other users of the pool, and the close of the table. After every call the table shows its state
//! (`trace_view`): slots, held chunks, stored ranges, credit, counters, the window target and the
//! delivery meter. The checkers replay each call with the operators of the model (`StreamsOps.tla`,
//! `Vinc.TransportStreams`) and require the state they compute to be the state recorded, and the error they compute
//! to be the error returned.
//!
//! The test asserts what it can itself (the bytes read are the bytes stored, in order and once; the pool never
//! passes its budget; a granted limit never goes down) so it is meaningful without the proof tools. Times are small
//! ticks (the checker has 32-bit integers). The trace is written to `VINC_TRACE_DIR` when it is set.
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

use vinc_tests::{SplitMix64, big_stack};
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE, Chunk};
use vinc_transport::stream::trace::{SlotView, TableView};
use vinc_transport::stream::{Config, ControlFrame, NoSource, PeerLimits, StreamError, Streams};

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
        r#"{{"id":{id},"open":{},"held":{},"rs":[{}],"read":{},"hi":{},"contig":{},"fin":{},"limit":{},"size":{},"pend":{},"defer":{},"rst":{},"obs":{},"sdone":{},"srst":{},"stop":{},"qcode":{},"scode":{}}}"#,
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
        opt(s.send_code)
    )
}

fn view_json(v: &TableView) -> String {
    let slots: Vec<String> = v.slots.iter().map(slot_json).collect();
    let (ms, mb, mr) = v.meter;
    format!(
        r#"{{"slots":[{}],"rn":[{},{}],"lo":[{},{}],"rl":{},"ll":{},"ext":{},"tgt":{},"hw":{},"ms":{},"mb":{mb},"mr":{mr},"ad":[{},{},{}],"adp":{}}}"#,
        slots.join(","),
        v.remote_next[0],
        v.remote_next[1],
        v.local_opened[0],
        v.local_opened[1],
        v.remote_live,
        v.local_live,
        v.ext,
        v.target,
        v.high_water,
        opt(ms),
        v.admit[0],
        v.admit[1],
        v.admit[2],
        b(v.admit_pend)
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
        let f = self.t.pending_control();
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
        let res = self.t.stop_sending(id, 7);
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
            3 => {
                while let Some(ch) = self.t.next_stream_frame(1 << 20) {
                    let mut buf = vec![0u8; ch.len];
                    let _ = self.t.copy_out(&self.pool, &ch, &mut buf);
                    self.inflight.push((ch.id, ch.offset, ch.len as u64, ch.fin));
                }
            }
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
            }
        }
    }
}

/// One seeded run; returns whether a frame opened a skipped lower stream inside the credit.
fn run(seed: u64, out: &mut String, run: u32) -> bool {
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
    let mut r = Run {
        t,
        pool,
        rng: SplitMix64::new(seed),
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
    };
    r.log(r#""op":"init""#);
    for _ in 0..220 {
        r.step();
    }
    r.log(r#""op":"end""#);
    r.jumped
}

#[test]
fn stream_table_runs_match_the_models() {
    big_stack(|| {
        let mut out = String::new();
        let mut jumped = false;
        for run_id in 1..=24u32 {
            jumped |= run(0x5354_5245_414d_0000 + u64::from(run_id), &mut out, run_id);
        }
        assert!(jumped, "no frame opened a skipped stream inside the credit");
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
        ] {
            assert!(out.contains(&format!(r#""op":"{op}""#)), "no {op} event");
        }
        // The runs reach the interesting steps: a peer stream held back and admitted later, stop requests sent and lost, implicit opens, a deferred grant, a conflict, a stream
        // that outgrew its ranges, a limit raised, a reset acknowledged.
        for needle in [
            r#""kind":"stop""#,
            r#""fresh":true"#,
            r#""admitted":true"#,
            r#""opened":2"#,
            r#""err":"Conflict""#,
            r#""err":"Fragmented""#,
            r#""err":"FlowControl""#,
            r#""err":"Exhausted""#,
            r#""defer":true"#,
            r#""kind":"msd""#,
            r#""kind":"msts""#,
            r#""kind":"reset""#,
        ] {
            assert!(out.contains(needle), "the runs never reach {needle}");
        }
        if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("streams.ndjson"), &out).unwrap();
        }
    });
}
