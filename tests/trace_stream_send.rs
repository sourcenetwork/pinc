//! Trace generation for the send half of a stream: real send halves (`pinc-transport` `Send`, through the `SendProbe`
//! of its `trace` feature) over a pool of 4 chunks and a ring of 3, driven through the calls the stream table makes:
//! writes against the window, the ring, the pool and the send buffer cap, finish, a source of application storage
//! (whole or short), resets (the application's, and the one a stop request from the peer makes), window raises, frames
//! taken for retransmission and for fresh data, copies of fresh, stale and clipped frames, losses and acknowledgements
//! in any order (past 16 lost and 64 acknowledged ranges), the reset frame taken, lost and acknowledged, and other
//! users of the pool. Fourteen scripted runs make each case the model names; 48 seeded runs follow. Every call is a
//! line of `stream_send.ndjson` for the TLA+ trace check (`TraceStreamSend.tla`): the call, its arguments and result,
//! and the whole state of the half after it.
//!
//! The test asserts the facts it relies on itself: every copy that succeeds returns the bytes written at its offsets,
//! every frame lies within the limit and the sent mark and a retransmission starts at the acknowledged prefix, every
//! end marker and reset frame carries one final size, a write never answers `Exhausted`, the pool's chunks add up in
//! every view, a lost range ends at or below the sent mark, and the acknowledged prefix never goes down while the half
//! is open and not reset. Unless the runs are soaking, the seeded and scripted runs must reach each branch listed at
//! the end. `send_half_at_the_offset_limits` records nothing: its numbers are past what the checker reads. The trace is
//! written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names,
    clippy::many_single_char_names,
    clippy::cognitive_complexity,
    unreachable_pub,
    clippy::expect_used,
    clippy::manual_is_multiple_of,
    clippy::trivially_copy_pass_by_ref
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;

use pinc_tests::{SplitMix64, soaking};
use pinc_transport::stream::pool::CHUNK_SIZE;
use pinc_transport::stream::trace::{SendHalfView, SendProbe};
use pinc_transport::stream::{ACKED_RANGES, ControlFrame, MAX_OFFSET, StreamChunk, StreamError, StreamSource};

type Probe = SendProbe<Src, 3>;

const POOL: usize = 4;
const CH: u64 = CHUNK_SIZE as u64;
const ID: u64 = 1;
const ROOM: u64 = 1 << 30;

/// Application storage of `av` bytes (the declared length may be more: past `av` it returns short).
struct Src {
    av: u64,
}

impl StreamSource for Src {
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
        let n = self.av.saturating_sub(offset).min(dst.len() as u64) as usize;
        for (j, b) in dst[..n].iter_mut().enumerate() {
            *b = pat(offset + j as u64);
        }
        n
    }
}

/// The byte at stream offset `o`, for both kinds of stream.
fn pat(o: u64) -> u8 {
    ((o.wrapping_mul(131) + 7) % 251) as u8
}

/// A recorded number: the checker reads 32-bit integers.
fn n(x: u64) -> u64 {
    assert!(x < 1 << 31, "a recorded number past what the checker reads: {x}");
    x
}

fn opt(x: Option<u64>) -> String {
    x.map_or_else(|| "-1".to_owned(), |v| n(v).to_string())
}

fn err_name(e: &StreamError) -> &'static str {
    match e {
        StreamError::StreamState => "StreamState",
        StreamError::WrongKind => "WrongKind",
        StreamError::Finished => "Finished",
        StreamError::FlowControl => "FlowControl",
        StreamError::DataUnavailable => "DataUnavailable",
        StreamError::BufferTooSmall => "BufferTooSmall",
        StreamError::Exhausted => "Exhausted",
        other => panic!("an error the model does not know: {other:?}"),
    }
}

fn res_name<T>(r: &Result<T, StreamError>) -> &'static str {
    r.as_ref().map_or_else(err_name, |_| "ok")
}

fn pairs(v: &[(u64, u64)]) -> String {
    let s: Vec<String> = v.iter().map(|(a, b)| format!("[{},{}]", n(*a), n(*b))).collect();
    format!("[{}]", s.join(","))
}

fn view_json(v: &SendHalfView) -> String {
    let fin = ["none", "pend", "sent", "acked"][usize::from(v.fin)];
    let held: Vec<String> = v.held.iter().map(|k| n(*k).to_string()).collect();
    format!(
        r#"{{"open":{},"src":{},"srcon":{},"wr":{},"smax":{},"limit":{},"lost":{},"acked":{},"ap":{},"fs":{},"fin":"{fin}","rst":{},"rcode":{},"rfs":{},"cut":{},"ext":{},"held":[{}],"avail":{},"buffered":{},"wants":[{},{}],"flushed":{},"done":{},"canstop":{},"ctlpend":{},"vlost":{},"vsent":{},"fdone":{}}}"#,
        v.open,
        v.is_source,
        v.has_source,
        n(v.written),
        n(v.sent_max),
        n(v.limit),
        pairs(&v.lost),
        pairs(&v.acked),
        n(v.acked_prefix),
        opt(v.final_size),
        v.reset,
        opt(v.reset_code),
        opt(v.reset_final),
        v.cap_cut,
        n(v.ext),
        held.join(","),
        n(v.available),
        n(v.buffered),
        v.wants.0,
        v.wants.1,
        v.flushed,
        v.done,
        v.can_stop,
        v.control_pending,
        opt(v.view.lost),
        n(v.view.sent),
        v.fin_done,
    )
}

/// The calls of the model, one per line.
const OPS: [&str; 16] = [
    "new", "write", "finish", "source", "reset", "raise", "next", "copy", "lost", "acked", "isacked", "clip",
    "takectl", "ctllost", "ctlacked", "ext",
];

struct Rec {
    p: Probe,
    out: String,
    run: u64,
    /// The first final size told in this run.
    told: Option<u64>,
    fs_seen: Option<u64>,
    last_ap: u64,
    /// The last reset frame `takectl` gave.
    ctl: Option<ControlFrame>,
    /// Every frame `next` gave in this run, and those not yet declared lost or acknowledged.
    all: Vec<StreamChunk>,
    live: Vec<StreamChunk>,
    /// What the runs reached.
    seen: BTreeSet<String>,
}

impl Rec {
    fn new() -> Self {
        Self {
            p: Probe::new(POOL, None),
            out: String::new(),
            run: 0,
            told: None,
            fs_seen: None,
            last_ap: 0,
            ctl: None,
            all: Vec::new(),
            live: Vec::new(),
            seen: BTreeSet::new(),
        }
    }

    fn see(&mut self, what: &str) {
        self.seen.insert(what.to_owned());
    }

    /// Record a call: its arguments and results (each starting with a comma) and the state after it.
    fn line(&mut self, op: &str, args: &str, res: &str) -> SendHalfView {
        let v = self.p.view();
        let _ = writeln!(
            self.out,
            r#"{{"t":"st","run":{},"op":"{op}"{args}{res},"v":{}}}"#,
            self.run,
            view_json(&v)
        );
        self.see(&format!("op:{op}"));
        assert_eq!(
            v.available + v.held.len() as u64 + v.ext,
            POOL as u64,
            "the pool's chunks do not add up"
        );
        assert!(
            v.lost.iter().all(|(_, e)| *e <= v.sent_max),
            "a lost range ends past the sent mark"
        );
        if let Some(f) = v.final_size {
            assert!(self.fs_seen.is_none_or(|s| s == f), "the final size changed");
            self.fs_seen = Some(f);
        }
        if v.open && v.reset == 0 {
            assert!(v.acked_prefix >= self.last_ap, "the acknowledged prefix went down");
            self.last_ap = v.acked_prefix;
        }
        if v.held.iter().any(|k| *k >= 3) {
            self.see("wrap");
        }
        if v.cap_cut {
            self.see("cut");
        }
        if v.reset == 3 {
            self.see("rst3");
        }
        v
    }

    fn new_run(&mut self, open: bool, limit: u64) {
        self.run += 1;
        self.p = Probe::new(POOL, open.then_some(limit));
        (self.told, self.fs_seen, self.last_ap, self.ctl) = (None, None, 0, None);
        self.all.clear();
        self.live.clear();
        self.line(
            "new",
            &format!(r#","open":{open},"limit":{}"#, n(if open { limit } else { 0 })),
            "",
        );
    }

    fn tag(&mut self, r: &Result<impl Sized, StreamError>) {
        if let Err(e) = r {
            self.see(&format!("err:{}", err_name(e)));
        }
    }

    fn write(&mut self, want: u64, room: u64) -> Result<usize, StreamError> {
        let w0 = self.p.view().written;
        let data: Vec<u8> = (0..want).map(|j| pat(w0 + j)).collect();
        let r = self.p.write(&data, room);
        assert!(r != Err(StreamError::Exhausted), "a write answered Exhausted");
        self.tag(&r);
        let got = r.as_ref().map_or(0, |x| *x as u64);
        self.line(
            "write",
            &format!(r#","want":{},"room":{}"#, n(want), n(room)),
            &format!(r#","err":"{}","n":{}"#, res_name(&r), n(got)),
        );
        r
    }

    fn finish(&mut self) -> Result<(), StreamError> {
        let r = self.p.finish();
        self.tag(&r);
        self.line("finish", "", &format!(r#","err":"{}""#, res_name(&r)));
        r
    }

    fn source(&mut self, len: u64, av: u64) -> Result<(), StreamError> {
        let r = self.p.open_source(Src { av }, len);
        self.tag(&r);
        self.line(
            "source",
            &format!(r#","len":{},"av":{}"#, n(len), n(av)),
            &format!(r#","err":"{}""#, res_name(&r)),
        );
        r
    }

    fn reset(&mut self, code: u64) -> Result<(), StreamError> {
        let r = self.p.reset(code);
        self.tag(&r);
        self.line(
            "reset",
            &format!(r#","code":{}"#, n(code)),
            &format!(r#","err":"{}""#, res_name(&r)),
        );
        r
    }

    fn raise(&mut self, limit: u64) {
        self.p.raise_limit(limit);
        self.line("raise", &format!(r#","limit":{}"#, n(limit)), "");
    }

    fn next(&mut self, retx: bool, budget: usize) -> Option<StreamChunk> {
        let v0 = self.p.view();
        let f = self.p.next_frame(ID, retx, budget);
        let v = self.line(
            "next",
            &format!(r#","retx":{retx},"budget":{}"#, n(budget as u64)),
            &match &f {
                Some(c) => format!(
                    r#","some":true,"off":{},"len":{},"fin":{}"#,
                    n(c.offset),
                    n(c.len as u64),
                    c.fin
                ),
                None => r#","some":false,"off":0,"len":0,"fin":false"#.to_owned(),
            },
        );
        if let Some(c) = &f {
            let end = c.offset + c.len as u64;
            assert!(end <= v0.limit, "a frame ends past the limit");
            assert!(end <= v.sent_max, "a frame ends past the sent mark");
            if retx {
                assert!(
                    c.offset >= v0.acked_prefix,
                    "a retransmitted frame starts below the acknowledged prefix"
                );
                if v0.lost.first().is_some_and(|r| c.offset > r.0) {
                    self.see("cutretx");
                }
            }
            if c.fin {
                let fs = v.final_size.unwrap();
                assert_eq!(end, fs, "a frame with the end marker does not end at the final size");
                assert!(self.told.is_none_or(|t| t == fs), "two final sizes told");
                self.told = Some(fs);
                if c.len == 0 {
                    self.see("fin0");
                }
            }
            self.all.push(*c);
            self.live.push(*c);
        }
        f
    }

    fn copy(&mut self, off: u64, len: u64, fin: bool, dst: u64) -> Result<usize, StreamError> {
        let v0 = self.p.view();
        let mut buf = vec![0u8; usize::try_from(dst).unwrap()];
        let chunk = StreamChunk {
            id: ID,
            offset: off,
            len: usize::try_from(len).unwrap(),
            fin,
        };
        let r = self.p.copy_out(&chunk, &mut buf);
        self.tag(&r);
        if let Ok(got) = r {
            assert_eq!(got as u64, len, "a copy returned a short frame as complete");
            assert!(
                buf[..got].iter().enumerate().all(|(j, b)| *b == pat(off + j as u64)),
                "a copy returned bytes other than those written at its offsets"
            );
        }
        if r == Err(StreamError::DataUnavailable) && !v0.is_source && off / CH < v0.acked_prefix / CH {
            self.see("belowprefix");
        }
        let got = r.as_ref().map_or(0, |x| *x as u64);
        self.line(
            "copy",
            &format!(r#","off":{},"len":{},"fin":{fin},"dst":{}"#, n(off), n(len), n(dst)),
            &format!(r#","err":"{}","got":{}"#, res_name(&r), n(got)),
        );
        r
    }

    fn copy_frame(&mut self, c: &StreamChunk) -> Result<usize, StreamError> {
        self.copy(c.offset, c.len as u64, c.fin, c.len as u64)
    }

    fn lost(&mut self, off: u64, len: u64, fin: bool) -> usize {
        let w = self.p.on_lost(off, len, fin);
        if w == 1 {
            self.see("w1:lost");
        }
        self.line(
            "lost",
            &format!(r#","off":{},"len":{},"fin":{fin}"#, n(off), n(len)),
            &format!(r#","w":{w}"#),
        );
        w
    }

    fn acked(&mut self, off: u64, len: u64, fin: bool) -> usize {
        let w = self.p.on_acked(off, len, fin);
        if w == 1 {
            self.see("w1:acked");
        }
        self.line(
            "acked",
            &format!(r#","off":{},"len":{},"fin":{fin}"#, n(off), n(len)),
            &format!(r#","w":{w}"#),
        );
        w
    }

    fn isacked(&mut self, off: u64, len: u64) -> bool {
        let res = self.p.is_acked(off, len);
        self.line(
            "isacked",
            &format!(r#","off":{},"len":{}"#, n(off), n(len)),
            &format!(r#","res":{res}"#),
        );
        res
    }

    fn clip(&mut self, off: u64) -> u64 {
        let res = self.p.clip(off);
        self.line(
            "clip",
            &format!(r#","off":{}"#, n(off)),
            &format!(r#","res":{}"#, n(res)),
        );
        res
    }

    fn takectl(&mut self) -> Option<ControlFrame> {
        let v0 = self.p.view();
        let f = self.p.take_control(ID);
        let res = match f {
            Some(ControlFrame::ResetStream {
                error_code, final_size, ..
            }) => {
                assert!(
                    final_size >= v0.sent_max && final_size <= v0.limit,
                    "a reset frame's final size is out of the window"
                );
                assert!(self.told.is_none_or(|t| t == final_size), "two final sizes told");
                self.told = Some(final_size);
                self.ctl = f;
                format!(r#","some":true,"code":{},"fs":{}"#, n(error_code), n(final_size))
            }
            Some(other) => panic!("a control frame that is not a reset: {other:?}"),
            None => r#","some":false,"code":-1,"fs":-1"#.to_owned(),
        };
        self.line("takectl", "", &res);
        f
    }

    fn ctllost(&mut self) {
        let f = self.ctl.expect("ctllost before takectl");
        let ControlFrame::ResetStream {
            error_code, final_size, ..
        } = f
        else {
            unreachable!()
        };
        self.p.control_lost(&f);
        self.line(
            "ctllost",
            &format!(r#","code":{},"fs":{}"#, n(error_code), n(final_size)),
            "",
        );
    }

    fn ctlacked(&mut self) {
        self.p.reset_acked();
        self.line("ctlacked", "", "");
    }

    fn ext(&mut self, count: usize) {
        self.p.set_ext(count);
        self.line("ext", &format!(r#","n":{count}"#), "");
    }

    /// The reset frame taken, lost, taken again, acknowledged twice, taken again (none). A reset after every byte and
    /// the end were acknowledged queues no frame (the stream is over), so there is none to lose.
    fn after_reset(&mut self) {
        if self.takectl().is_some() {
            self.ctllost();
            self.takectl();
        }
        self.ctlacked();
        self.ctlacked();
        assert!(self.takectl().is_none(), "a reset frame after its acknowledgement");
    }
}

fn scripted(r: &mut Rec) {
    // 1. window at zero
    r.new_run(true, 0);
    assert_eq!(r.write(10, ROOM), Ok(0));
    assert!(r.next(false, CHUNK_SIZE).is_none() && r.next(true, CHUNK_SIZE).is_none());
    r.raise(2 * CH);
    assert_eq!(r.write(3 * CH, ROOM), Ok(2 * CHUNK_SIZE));
    assert!(r.next(false, CHUNK_SIZE).is_some() && r.next(false, CHUNK_SIZE).is_some());

    // 2. pool taken
    r.new_run(true, 8 * CH);
    r.ext(4);
    assert_eq!(r.write(CH, ROOM), Ok(0));
    r.ext(0);
    assert_eq!(r.write(CH / 2, ROOM), Ok(CHUNK_SIZE / 2));
    r.ext(4);
    assert_eq!(r.write(CH, ROOM), Ok(CHUNK_SIZE / 2));
    r.ext(0);

    // 3. ring wrap and stale copies
    r.new_run(true, 10 * CH);
    assert_eq!(r.write(3 * CH, ROOM), Ok(3 * CHUNK_SIZE));
    let fr: Vec<StreamChunk> = (0..3).map(|_| r.next(false, CHUNK_SIZE).unwrap()).collect();
    for f in &fr {
        assert!(r.copy_frame(f).is_ok());
    }
    r.acked(0, CH / 2, false);
    assert!(r.copy_frame(&fr[0]).is_ok());
    assert_eq!(r.clip(0), CH / 2);
    r.acked(CH / 2, CH / 2, false);
    assert_eq!(r.write(CH, ROOM), Ok(CHUNK_SIZE));
    assert_eq!(r.copy_frame(&fr[0]), Err(StreamError::DataUnavailable));
    assert_eq!(r.copy(CH / 2, CH, false, CH), Err(StreamError::DataUnavailable));
    r.next(true, CHUNK_SIZE);
    r.lost(fr[1].offset, CH, false);
    let mut pieces = Vec::new();
    while let Some(f) = r.next(true, CHUNK_SIZE / 4) {
        pieces.push(f);
    }
    for f in &pieces {
        let _ = r.copy_frame(f);
    }
    let d = r.next(false, CHUNK_SIZE).unwrap();
    let _ = r.copy_frame(&d);
    r.acked(0, 4 * CH, false);
    assert!(r.finish().is_ok());
    let end = r.next(true, CHUNK_SIZE).unwrap();
    assert!(end.len == 0 && end.fin, "the end marker is not alone");
    r.acked(end.offset, 0, true);
    let v = r.p.view();
    assert!(
        v.done && v.held.is_empty(),
        "the half is not done after every byte and the end were acknowledged"
    );

    // 4. acknowledged ranges past capacity
    r.new_run(true, 4 * CH);
    assert_eq!(r.write(300, ROOM), Ok(300));
    for _ in 0..300 {
        r.next(false, 1);
    }
    for k in 0..=64u64 {
        let w = r.acked(1 + 2 * k, 1, false);
        assert_eq!(w, usize::from(k as usize >= ACKED_RANGES), "acknowledged range {k}");
    }
    assert!(r.isacked(1, 1));
    assert!(!r.isacked(2, 1));
    for k in 0..18u64 {
        r.lost(150 + 2 * k, 1, false);
    }
    while r.next(true, CHUNK_SIZE).is_some() {}
    r.acked(0, 300, false);

    // 5 to 11. a reset in every phase
    r.new_run(true, 4 * CH);
    r.reset(1).unwrap();
    r.after_reset();

    r.new_run(true, 4 * CH);
    r.write(1000, ROOM).unwrap();
    r.reset(1).unwrap();
    r.after_reset();

    r.new_run(true, 4 * CH);
    r.write(1000, ROOM).unwrap();
    let f = r.next(false, CHUNK_SIZE).unwrap();
    r.reset(1).unwrap();
    assert_eq!(r.copy_frame(&f), Err(StreamError::DataUnavailable));
    r.acked(f.offset, f.len as u64, false);
    r.lost(f.offset, f.len as u64, false);
    assert_eq!(r.write(10, ROOM), Err(StreamError::Finished));
    assert_eq!(r.finish(), Err(StreamError::Finished));
    assert!(r.next(false, CHUNK_SIZE).is_none() && r.next(true, CHUNK_SIZE).is_none());
    let _ = r.source(10, 10);
    r.after_reset();

    r.new_run(true, 4 * CH);
    r.write(1000, ROOM).unwrap();
    r.finish().unwrap();
    r.reset(1).unwrap();
    r.after_reset();

    r.new_run(true, 4 * CH);
    r.write(1000, ROOM).unwrap();
    r.finish().unwrap();
    r.next(false, CHUNK_SIZE).unwrap();
    r.reset(7).unwrap();
    r.after_reset();

    r.new_run(true, 4 * CH);
    r.write(1000, ROOM).unwrap();
    r.finish().unwrap();
    r.next(false, CHUNK_SIZE).unwrap();
    r.acked(1, 999, true);
    r.reset(1).unwrap();
    r.after_reset();

    r.new_run(true, 4 * CH);
    r.write(1000, ROOM).unwrap();
    r.finish().unwrap();
    r.next(false, CHUNK_SIZE).unwrap();
    r.acked(0, 1000, true);
    r.reset(1).unwrap();
    r.reset(1).unwrap();
    r.after_reset();

    // 12. source-backed
    r.new_run(true, 2 * CH);
    r.source(3 * CH + 5, 3 * CH + 5 - 10).unwrap();
    let mut frames = Vec::new();
    while let Some(f) = r.next(false, CHUNK_SIZE) {
        frames.push(f);
    }
    assert!(!r.p.view().wants.1, "fresh data waits at the window");
    r.raise(4 * CH);
    while let Some(f) = r.next(false, CHUNK_SIZE) {
        frames.push(f);
    }
    assert!(
        frames.last().is_some_and(|f| f.fin),
        "the last frame does not carry the end"
    );
    for f in &frames {
        let _ = r.copy_frame(f);
    }
    r.next(true, CHUNK_SIZE);
    r.reset(7).unwrap();

    // 13. unopened half
    r.new_run(false, 0);
    assert_eq!(r.write(1, ROOM), Err(StreamError::StreamState));
    assert_eq!(r.finish(), Err(StreamError::StreamState));
    assert_eq!(r.source(0, 0), Err(StreamError::StreamState));
    assert_eq!(r.reset(1), Err(StreamError::StreamState));
    assert!(r.next(false, CHUNK_SIZE).is_none());
    assert_eq!(r.copy(0, 0, false, 0), Ok(0));
    assert!(r.takectl().is_none());

    // 14. budget 0 and the send buffer cap
    r.new_run(true, CH);
    assert_eq!(r.write(100, 40), Ok(40));
    assert!(r.next(false, 0).is_none());
    let f = r.next(false, 40).unwrap();
    r.lost(f.offset, f.len as u64, false);
    assert!(r.next(true, 0).is_none());
    r.finish().unwrap();
    assert_eq!(
        r.copy(f.offset, f.len as u64, false, f.len as u64 - 1),
        Err(StreamError::BufferTooSmall)
    );
    let g = r.next(true, CHUNK_SIZE).unwrap();
    assert!(g.fin, "the retransmitted range does not carry the end");
    r.lost(g.offset, g.len as u64, true);
    r.acked(0, 40, false);
    assert!(r.next(true, CHUNK_SIZE).is_some_and(|e| e.len == 0 && e.fin));
}

/// A random source: the length and how much of it the storage holds.
fn random_source(r: &mut Rec, rng: &mut SplitMix64) {
    let len = rng.next_u64() % (6 * CH + 1);
    let av = if rng.next_u64() % 2 == 0 {
        len
    } else {
        len.saturating_sub(1 + rng.next_u64() % CH)
    };
    let _ = r.source(len, av);
}

#[derive(Clone, Copy, PartialEq)]
enum Op {
    Write,
    Next,
    Copy,
    Lost,
    Acked,
    Raise,
    Ext,
    IsAcked,
    Clip,
    Finish,
    TakeCtl,
    CtlLost,
    CtlAcked,
}

fn random_call(r: &mut Rec, rng: &mut SplitMix64, source: bool) {
    if rng.next_u64() % 40 == 0 {
        let code = if rng.next_u64() % 2 == 0 { 1 } else { 7 };
        let _ = r.reset(code);
        return;
    }
    if rng.next_u64() % 50 == 0 {
        random_source(r, rng);
        return;
    }
    let v = r.p.view();
    let mut table = vec![
        (6, Op::Write),
        (8, Op::Next),
        (6, Op::Copy),
        (4, Op::Lost),
        (5, Op::Acked),
        (2, Op::Raise),
        (1, Op::Ext),
        (1, Op::IsAcked),
        (1, Op::Clip),
    ];
    if !source {
        table.push((1, Op::Finish));
    }
    if v.reset != 0 {
        table.push((1, Op::TakeCtl));
        table.push((1, Op::CtlAcked));
        if r.ctl.is_some() {
            table.push((1, Op::CtlLost));
        }
    }
    let total: u64 = table.iter().map(|t| t.0).sum();
    let mut x = rng.next_u64() % total;
    let op = table
        .iter()
        .find(|(w, _)| {
            if x < *w {
                true
            } else {
                x -= *w;
                false
            }
        })
        .unwrap()
        .1;
    match op {
        Op::Write => {
            let want = match rng.next_u64() % 7 {
                0 => 0,
                1 => 1,
                2 => CH - 1,
                3 => CH,
                4 => CH + 1,
                5 => 3 * CH,
                _ => 1 + rng.next_u64() % (4 * CH),
            };
            let room = match rng.next_u64() % 10 {
                0 => 0,
                1 | 2 => rng.next_u64() % want.max(1),
                _ => ROOM,
            };
            let _ = r.write(want, room);
        }
        Op::Next => {
            let retx = rng.next_u64() % 2 == 0;
            let budget = match rng.next_u64() % 6 {
                0 => 0,
                1 => 1,
                2 => 100,
                3 => 1200,
                4 => CH,
                _ => 1 + rng.next_u64() % (2 * CH),
            };
            r.next(retx, budget as usize);
        }
        Op::Copy => {
            if r.all.is_empty() {
                return;
            }
            let i = usize::try_from(rng.next_u64() % r.all.len() as u64).unwrap();
            let mut f = match rng.next_u64() % 3 {
                0 => r.all[i],
                1 => r.all[i / 2],
                _ => {
                    // cut at the acknowledged prefix, as a retransmission is
                    let mut f = r.all[i];
                    let end = f.offset + f.len as u64;
                    let c = r.p.clip(f.offset).min(end);
                    f.len = (end - c) as usize;
                    f.offset = c;
                    f
                }
            };
            f.len = f.len.min(usize::try_from(6 * CH).unwrap());
            let dst = if f.len > 0 && rng.next_u64() % 10 == 0 {
                f.len - 1
            } else {
                f.len
            };
            let _ = r.copy(f.offset, f.len as u64, f.fin, dst as u64);
        }
        Op::Lost | Op::Acked => {
            let again = rng.next_u64() % 6 == 0;
            let f = if again || r.live.is_empty() {
                if r.all.is_empty() {
                    return;
                }
                r.all[usize::try_from(rng.next_u64() % r.all.len() as u64).unwrap()]
            } else {
                let i = usize::try_from(rng.next_u64() % r.live.len() as u64).unwrap();
                r.live.remove(i)
            };
            if op == Op::Lost {
                r.lost(f.offset, f.len as u64, f.fin);
            } else {
                r.acked(f.offset, f.len as u64, f.fin);
            }
        }
        Op::Raise => {
            let l = v.limit;
            let to = if rng.next_u64() % 4 == 0 {
                rng.next_u64() % (l + 1)
            } else {
                l + rng.next_u64() % (2 * CH + 1)
            };
            r.raise(to);
        }
        Op::Ext => r.ext(usize::try_from(rng.next_u64() % 5).unwrap()),
        Op::IsAcked => {
            let off = rng.next_u64() % (v.sent_max + 2);
            let len = rng.next_u64() % (CH + 1);
            r.isacked(off, len);
        }
        Op::Clip => {
            let off = rng.next_u64() % (v.sent_max + 2);
            r.clip(off);
        }
        Op::Finish => {
            let _ = r.finish();
        }
        Op::TakeCtl => {
            r.takectl();
        }
        Op::CtlLost => r.ctllost(),
        Op::CtlAcked => r.ctlacked(),
    }
}

fn seeded(r: &mut Rec, run: u64) {
    let mut rng = SplitMix64::traced(0x5345_4E44_0000_0000 + run);
    let source = run % 4 == 3;
    let limit = if run % 12 == 5 {
        0
    } else {
        CH + rng.next_u64() % (4 * CH)
    };
    r.new_run(true, limit);
    if source {
        random_source(r, &mut rng);
    }
    for _ in 0..250 {
        random_call(r, &mut rng, source);
    }
}

#[test]
fn send_half_runs_match_the_model() {
    let mut r = Rec::new();
    scripted(&mut r);
    for run in 0..48 {
        seeded(&mut r, run);
    }
    if !soaking() {
        for op in OPS {
            assert!(r.seen.contains(&format!("op:{op}")), "no run made the call {op}");
        }
        for tag in [
            "err:DataUnavailable",
            "err:BufferTooSmall",
            "err:WrongKind",
            "err:Finished",
            "err:StreamState",
            "w1:acked",
            "w1:lost",
            "fin0",
            "wrap",
            "cut",
            "rst3",
            "belowprefix",
            "cutretx",
        ] {
            assert!(r.seen.contains(tag), "no run reached {tag}");
        }
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("stream_send.ndjson"), &r.out).unwrap();
    }
}

#[test]
fn send_half_at_the_offset_limits() {
    let mut p = Probe::new(POOL, Some(MAX_OFFSET));
    let before = p.view();
    assert_eq!(
        p.open_source(Src { av: 0 }, MAX_OFFSET + 1),
        Err(StreamError::FlowControl)
    );
    assert_eq!(p.view(), before, "a refused source changed the half");
    assert_eq!(p.open_source(Src { av: u64::MAX }, MAX_OFFSET), Ok(()));
    assert_eq!(p.view().final_size, Some(MAX_OFFSET));
    let f = p.next_frame(ID, false, usize::MAX).unwrap();
    assert_eq!((f.offset, f.len as u64, f.fin), (0, MAX_OFFSET, true));
    let _ = p.on_lost(MAX_OFFSET - 5, u64::MAX, false);
    assert_eq!(p.view().lost, vec![(MAX_OFFSET - 5, MAX_OFFSET)]);
    let _ = p.on_acked(u64::MAX - 1, 10, false);
    assert!(
        !p.is_acked(u64::MAX, 5),
        "a range past the end of the offsets reads as acknowledged"
    );

    let mut b = Probe::new(POOL, Some(0));
    b.raise_limit(u64::MAX);
    assert_eq!(b.view().limit, u64::MAX);
    b.raise_limit(5);
    assert_eq!(b.view().limit, u64::MAX);
}
