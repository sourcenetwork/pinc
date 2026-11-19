//! Trace generation for the connection's event queue: seeded runs of real queues of 640 places (`pinc-transport`,
//! built with the `trace` feature, through `EvQueueProbe`), recorded as ndjson (`evqueue.ndjson`) for the TLA+ trace
//! check (`TraceEvQueue.tla`).
//!
//! The runs are repeats of queued events, a queue full of unrecoverable events pushed on (drops and losses), a queue
//! full of recoverable ones and then unrecoverable ones (each gives way the oldest, deep in the queue too), the head
//! taken round the ring, pops of the last event, and seeded mixes. After every call the record shows the head, the
//! length, the lost count and the written prefix; the queued events when at most 24 are queued, on every 101st call
//! and on the last event of a run.
//!
//! The test compares every call with a naive queue, so it is meaningful without the proof tools. The trace is written
//! to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub,
    clippy::manual_is_multiple_of
)]

use std::collections::VecDeque;
use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::conn::{EvQueueProbe, EvTuple, EvView};

/// The places of the queue.
const CAP: usize = 640;

/// The 19 kinds of event.
const KINDS: [&str; 19] = [
    "rd", "wr", "or", "dg", "ex", "op", "rs", "st", "pv", "pf", "kr", "cn", "tk", "ry", "as", "aw", "wu", "cl", "xu",
];

/// The kinds a notification the application can recover by polling state.
fn lossy(k: &str) -> bool {
    matches!(k, "rd" | "wr" | "or" | "dg" | "ex")
}

/// The model's `same`: a repeat of a queued event is not queued.
fn same(a: &EvTuple, b: &EvTuple) -> bool {
    match a.0 {
        "op" | "rs" | "st" | "rd" | "wr" | "pv" | "pf" => a.0 == b.0 && a.1 == b.1,
        "kr" | "cn" | "or" | "as" | "aw" | "wu" | "tk" | "ry" | "cl" => a.0 == b.0,
        _ => false,
    }
}

/// `["kind",key,payload]`.
fn tuple(t: &EvTuple) -> String {
    format!(r#"["{}",{},{}]"#, t.0, t.1, t.2)
}

/// One run: a real queue, the naive one and the record.
struct Run<'a> {
    p: EvQueueProbe,
    naive: VecDeque<EvTuple>,
    lost: u64,
    calls: u64,
    max_head: usize,
    max_len: usize,
    /// The last event, held until the next one shows it is not the last.
    pending: Option<(String, EvView, bool)>,
    out: &'a mut String,
}

impl<'a> Run<'a> {
    fn new(out: &'a mut String) -> Self {
        let mut r = Run {
            p: EvQueueProbe::new(),
            naive: VecDeque::new(),
            lost: 0,
            calls: 0,
            max_head: 0,
            max_len: 0,
            pending: None,
            out,
        };
        assert_eq!(EvQueueProbe::CAP, CAP);
        let v = r.p.view();
        r.emit(format!(r#"{{"t":"evq","op":"init","cap":{CAP},"v":"#), v, true);
        r
    }

    fn flush(&mut self, last: bool) {
        if let Some((prefix, v, with_q)) = self.pending.take() {
            let q = if with_q || last {
                let w: Vec<String> = v
                    .window
                    .iter()
                    .map(|e| e.as_ref().map_or_else(|| "[]".to_owned(), tuple))
                    .collect();
                format!(r#","q":[{}]"#, w.join(","))
            } else {
                String::new()
            };
            let _ = writeln!(
                self.out,
                r#"{prefix}{{"head":{},"len":{},"lost":{},"wlen":{}{q}}}}}"#,
                v.head, v.len, v.lost, v.wlen
            );
        }
    }

    fn emit(&mut self, prefix: String, v: EvView, with_q: bool) {
        self.flush(false);
        let with_q = with_q || v.len <= 24 || self.calls.is_multiple_of(101);
        self.pending = Some((prefix, v, with_q));
    }

    /// The run is over: the last event carries the queue.
    fn finish(mut self) -> (u64, usize, usize) {
        self.flush(true);
        (self.lost, self.max_head, self.max_len)
    }

    /// The state of the real queue against the naive one.
    fn check(&mut self) -> EvView {
        let v = self.p.view();
        assert_eq!(v.len, self.naive.len(), "the length differs");
        assert_eq!(v.lost, self.lost, "the lost count differs");
        assert!(v.wlen <= CAP, "the written prefix is past the room");
        let want: Vec<Option<EvTuple>> = self.naive.iter().copied().map(Some).collect();
        assert_eq!(v.window, want, "the queued events differ");
        self.max_head = self.max_head.max(v.head);
        self.max_len = self.max_len.max(v.len);
        v
    }

    fn push(&mut self, kind: &'static str, key: u64, payload: u64) {
        let e: EvTuple = (kind, key, payload);
        self.calls += 1;
        assert!(self.p.push(kind, key, payload), "an unknown kind");
        if !matches!(kind, "dg" | "ex" | "xu") && self.naive.iter().any(|q| same(q, &e)) {
        } else if self.naive.len() == CAP {
            if lossy(kind) {
            } else if let Some(at) = self.naive.iter().position(|q| lossy(q.0)) {
                self.naive.remove(at);
                self.naive.push_back(e);
            } else {
                self.lost += 1;
            }
        } else {
            self.naive.push_back(e);
        }
        let v = self.check();
        self.emit(format!(r#"{{"t":"evq","op":"push","ev":{},"v":"#, tuple(&e)), v, false);
    }

    fn pop(&mut self) -> Option<EvTuple> {
        self.calls += 1;
        let got = self.p.pop();
        assert_eq!(got, self.naive.pop_front(), "pop is not the front");
        let v = self.check();
        let out = got.as_ref().map_or_else(|| "[]".to_owned(), tuple);
        self.emit(format!(r#"{{"t":"evq","op":"pop","out":{out},"v":"#), v, false);
        got
    }

    fn drain(&mut self) {
        while self.pop().is_some() {}
    }

    /// A random event: kind uniform, key `1 + below(k)` for keyed kinds, a payload where the kind has one.
    fn any(&mut self, rng: &mut SplitMix64, k: usize) {
        let kind = KINDS[(rng.next_u64() % 19) as usize];
        let key = if matches!(kind, "rd" | "wr" | "op" | "rs" | "st" | "pv" | "pf" | "xu") {
            1 + rng.next_u64() % k as u64
        } else {
            0
        };
        let payload = match kind {
            "rs" | "st" | "xu" => rng.next_u64() % 10,
            "cn" => rng.next_u64() % 2,
            _ => 0,
        };
        self.push(kind, key, payload);
    }
}

#[test]
fn the_event_queue_matches_the_model() {
    let mut rng = SplitMix64::traced(0x6576_7175);
    let mut out = String::new();

    // 1. repeats
    let mut r = Run::new(&mut out);
    for _ in 0..400 {
        if rng.next_u64() % 4 == 0 {
            r.pop();
        } else {
            r.any(&mut rng, 3);
        }
    }
    let (lost, _, max_len) = r.finish();
    assert!(max_len < CAP && lost == 0, "run 1 reached the full queue");

    // 2. unrecoverable fill
    let mut r = Run::new(&mut out);
    for k in 1..=CAP as u64 {
        r.push("op", k, 0);
    }
    r.push("rd", 1, 0);
    r.push("dg", 0, 0);
    r.push("ex", 0, 0);
    for k in 641..=643 {
        r.push("op", k, 0);
    }
    r.push("xu", 1, 0);
    r.push("xu", 1, 0);
    r.pop();
    r.push("rd", 5, 0);
    r.push("op", 700, 0);
    r.drain();
    r.pop();
    assert!(r.finish().0 > 0, "run 2 lost nothing");

    // 3. recoverable fill
    let mut r = Run::new(&mut out);
    for k in 1..=CAP as u64 {
        r.push("rd", k, 0);
    }
    for k in 1..=700 {
        r.push("op", k, 0);
    }
    for _ in 0..100 {
        r.pop();
    }
    for _ in 0..50 {
        r.push("dg", 0, 0);
    }
    r.drain();
    assert!(r.finish().0 > 0, "run 3 lost nothing");

    // 4. interleaved fill
    let mut r = Run::new(&mut out);
    for k in 1..=320 {
        r.push("rd", k, 0);
        r.push("op", k, 0);
    }
    for k in 1..=200 {
        r.push("st", k, 1);
    }
    r.drain();
    r.finish();

    // 5. round the ring
    let mut r = Run::new(&mut out);
    for _ in 0..2000 {
        for _ in 0..3 {
            r.any(&mut rng, 50);
        }
        r.pop();
        r.pop();
    }
    r.drain();
    let (_, max_head, _) = r.finish();
    assert!(max_head > 600, "the head never passed place 600");

    // 6. seeded runs
    for _ in 0..10 {
        let mut r = Run::new(&mut out);
        for _ in 0..300 {
            if rng.next_u64() % 3 == 0 {
                r.pop();
            } else {
                r.any(&mut rng, 8);
            }
        }
        r.finish();
    }

    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("evqueue.ndjson"), &out).unwrap();
    }
}
