//! Trace generation for the set reconciliation: seeded sessions of the real `Initiator` and `Responder` through the
//! public API, recorded as ndjson (`reconcile.ndjson`, and `reconcile_big.ndjson` for sessions whose messages hold a
//! varint of 2^31 or more) for the TLA+ trace check (`TraceReconcile.tla`) and the Lean replay
//! (`Vinc/TraceReconcile.lean`).
//!
//! What is recorded is every handler call: who made it (`I` the initiator, `R` the responder), which (`start`,
//! `handle`, `resume`), the bytes delivered to it (after any tampering), and the step and the bytes it wrote, or the
//! error it returned. A case line carries the two sets, the limits of both sides, the set reference and the keyed
//! hash tables (the real `Fingerprint::of_item` of every item that can be hashed and the real `item_id` of every
//! item of the two sets), so the checkers run the model with the real hash. The families: empty, equal, cold,
//! tiny, dense, variable-length, prefix and empty items, differences of every size under the default limit and under
//! the smallest limits (chunked rounds, frames, narrowing), index and size errors, round and report limits, a forced
//! id collision, a lying answer to the final check, resets, a started-again initiator, and fault injection (one
//! changed message per session: a flipped bit, a cut, an extension, a dropped or doubled part, a changed tag or
//! count) on the messages of several honest sessions, with the objects reused from one session to the next.
//!
//! The test asserts everything itself (an honest session reports exactly the symmetric difference, once each, every
//! message body is within the frame cap), so it is meaningful without the proof tools. The trace is written to the
//! directory in `VINC_TRACE_DIR` when it is set; when it is not, nothing is formatted or kept.
#![allow(
    dead_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    unreachable_pub
)]

#[path = "reconcile_common.rs"]
mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use common::{Dir, Item, fixed_set, index, mutate, sorted, sym_diff, var_set};
use vinc_reconcile::{Error, Fingerprint, Initiator, Limits, MemError, MemIndex, Reason, Responder, Step, item_id};
use vinc_tests::SplitMix64;

#[path = "trace_reconcile_scan.rs"]
mod scanmod;
use scanmod::{fix_len, mutate_msg, scan};

type Err = Error<MemError>;

fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn list(bytes: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in bytes.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

fn items_json(v: &[Item]) -> String {
    let parts: Vec<String> = v.iter().map(|x| list(x)).collect();
    format!("[{}]", parts.join(","))
}

fn err_name(e: Err) -> &'static str {
    match e {
        Error::Index(_) => "index",
        Error::BadIndex => "badIndex",
        Error::Malformed(Reason::Frame) => "frame",
        Error::Malformed(Reason::Truncated) => "truncated",
        Error::Malformed(Reason::Tag) => "tag",
        Error::Malformed(Reason::Bound) => "bound",
        Error::Malformed(Reason::Count) => "count",
        Error::Malformed(Reason::Item) => "item",
        Error::Malformed(Reason::State) => "state",
        Error::MessageTooLarge => "messageTooLarge",
        Error::ItemTooLarge => "itemTooLarge",
        Error::ReportTooLarge => "reportTooLarge",
        Error::TooManyRounds => "tooManyRounds",
        Error::Mismatch => "mismatch",
    }
}

fn step_name(s: Step) -> &'static str {
    match s {
        Step::Send => "send",
        Step::Chunk => "chunk",
        Step::Last => "last",
        Step::Wait => "wait",
        Step::Done => "done",
    }
}

// ---- the trace of one case -----------------------------------------------------------------------------------------

#[derive(Default)]
struct Tr {
    on: bool,
    norm: String,
    big: String,
    stats: BTreeMap<String, usize>,
    next_id: u32,
}

struct Case {
    on: bool,
    id: u32,
    a: Vec<Item>,
    b: Vec<Item>,
    li: Limits,
    lr: Limits,
    rf: Vec<u8>,
    norm: String,
    big: String,
    norm_h: BTreeSet<Item>,
    big_h: BTreeSet<Item>,
    cur: String,
    cur_h: BTreeSet<Item>,
    cur_big: bool,
    r_fresh: bool,
    stats: BTreeMap<String, usize>,
}

fn lim_json(l: &Limits) -> String {
    format!("[{},{},{},{}]", l.max_item, l.max_message, l.max_report, l.max_rounds)
}

impl Case {
    fn new(tr: &mut Tr, a: &[Item], b: &[Item], li: Limits, lr: Limits, rf: &[u8]) -> Self {
        tr.next_id += 1;
        Self {
            on: tr.on,
            id: tr.next_id,
            a: a.to_vec(),
            b: b.to_vec(),
            li,
            lr,
            rf: rf.to_vec(),
            norm: String::new(),
            big: String::new(),
            norm_h: BTreeSet::new(),
            big_h: BTreeSet::new(),
            cur: String::new(),
            cur_h: BTreeSet::new(),
            cur_big: false,
            r_fresh: true,
            stats: BTreeMap::new(),
        }
    }

    fn begin(&mut self) {
        self.cur.clear();
        self.cur_h.clear();
        self.cur_big = false;
    }

    fn end(&mut self) {
        if !self.on {
            return;
        }
        let (out, h) = if self.cur_big {
            (&mut self.big, &mut self.big_h)
        } else {
            (&mut self.norm, &mut self.norm_h)
        };
        out.push_str(&self.cur);
        h.append(&mut self.cur_h);
    }

    fn stat(&mut self, k: String) {
        *self.stats.entry(k).or_insert(0) += 1;
    }

    fn reset(&mut self) {
        if self.on {
            writeln!(self.cur, r#"{{"t":"rc","e":"reset","id":{}}}"#, self.id).unwrap();
        }
        self.r_fresh = true;
    }

    /// Note a delivered message: the items it can push into an arena and whether it holds a huge varint.
    fn note(&mut self, m: &[u8], first: bool) {
        if self.on {
            let s = scan(m, first);
            self.cur_big |= s.big;
            self.cur_h.extend(s.items);
        }
    }

    fn ev(&mut self, who: &str, call: &str, inp: &[u8], res: Result<Step, Err>, out: &[u8]) {
        if !self.on {
            return;
        }
        let head = format!(
            r#"{{"t":"rc","e":"ev","id":{},"who":"{who}","call":"{call}","in":{},"#,
            self.id,
            list(inp)
        );
        match &res {
            Ok(s) => {
                let out = if matches!(s, Step::Wait | Step::Done) {
                    &[][..]
                } else {
                    out
                };
                writeln!(
                    self.cur,
                    r#"{head}"ok":true,"step":"{}","out":{}}}"#,
                    step_name(*s),
                    list(out)
                )
                .unwrap();
                self.stat(format!("{who}.{call} {}", step_name(*s)));
            }
            Err(e) => {
                writeln!(self.cur, r#"{head}"ok":false,"err":"{}"}}"#, err_name(*e)).unwrap();
                self.stat(format!("{who}.{call} err {}", err_name(*e)));
            }
        }
    }

    fn rep(&mut self, here: &[Item], there: &[Item]) {
        if self.on {
            writeln!(
                self.cur,
                r#"{{"t":"rc","e":"rep","id":{},"here":{},"there":{}}}"#,
                self.id,
                items_json(here),
                items_json(there)
            )
            .unwrap();
        }
    }

    /// Write the case into the trace.
    fn finish(self, tr: &mut Tr) {
        for (n, (body, extra)) in [(&self.norm, &self.norm_h), (&self.big, &self.big_h)]
            .into_iter()
            .enumerate()
        {
            if !self.on || body.is_empty() {
                continue;
            }
            let mut hs: BTreeSet<&Item> = extra.iter().collect();
            hs.extend(self.a.iter());
            hs.extend(self.b.iter());
            let h: Vec<String> = hs
                .iter()
                .map(|x| format!("[{},{}]", list(x), list(&Fingerprint::of_item(x).to_bytes())))
                .collect();
            let ids: Vec<String> = self
                .a
                .iter()
                .chain(&self.b)
                .collect::<BTreeSet<_>>()
                .iter()
                .map(|x| format!("[{},{}]", list(x), list(&item_id(x))))
                .collect();
            let out = if n == 0 { &mut tr.norm } else { &mut tr.big };
            writeln!(
                out,
                r#"{{"t":"rc","e":"case","id":{},"A":{},"B":{},"H":[{}],"ID":[{}],"limI":{},"limR":{},"ref":{}}}"#,
                self.id,
                items_json(&self.a),
                items_json(&self.b),
                h.join(","),
                ids.join(","),
                lim_json(&self.li),
                lim_json(&self.lr),
                list(&self.rf)
            )
            .unwrap();
            out.push_str(body);
        }
        for (k, v) in self.stats {
            *tr.stats.entry(k).or_insert(0) += v;
        }
    }
}

/// The report of a session: the items missing here and there.
type Report = (Vec<Item>, Vec<Item>);

/// One session between `init` over `ia` and `resp` over `ib`, every message passing through `tamper`. `cut` ends the
/// session after that many handler calls, as a reset of the stream would. `Ok(None)` is a session that did not
/// finish (cut, or nothing left to send).
fn session(
    cs: &mut Case,
    init: &mut Initiator,
    resp: &mut Responder,
    ia: &MemIndex,
    ib: &MemIndex,
    tamper: &mut dyn FnMut(Dir, &mut Vec<u8>),
    cut: Option<usize>,
) -> Result<Option<Report>, Err> {
    cs.begin();
    let r = run(cs, init, resp, ia, ib, tamper, cut);
    cs.end();
    r
}

fn run(
    cs: &mut Case,
    init: &mut Initiator,
    resp: &mut Responder,
    ia: &MemIndex,
    ib: &MemIndex,
    tamper: &mut dyn FnMut(Dir, &mut Vec<u8>),
    cut: Option<usize>,
) -> Result<Option<Report>, Err> {
    let cap = |l: &Limits| l.max_message.min(0x00ff_ffff) + 2 * l.max_item + 36;
    let (capi, capr) = (cap(&cs.li), cap(&cs.lr));
    let mut calls = 0usize;
    resp.reset();
    cs.reset();
    let (mut tx, mut rx) = (Vec::new(), Vec::new());
    let rf = cs.rf.clone();
    let r = init.start(ia, &rf, &mut tx);
    cs.ev("I", "start", &[], r.map(|()| Step::Send), &tx);
    r?;
    macro_rules! check_cut {
        () => {
            calls += 1;
            if cut.is_some_and(|c| calls > c) {
                return Ok(None);
            }
        };
    }
    loop {
        check_cut!();
        tamper(Dir::ToResponder, &mut tx);
        let first = cs.r_fresh;
        cs.r_fresh = false;
        cs.note(&tx, first);
        let r = resp.handle(ib, &tx, &mut rx);
        cs.ev("R", "handle", &tx, r, &rx);
        let mut step = r?;
        let mut replies: Vec<Vec<u8>> = Vec::new();
        loop {
            match step {
                Step::Send | Step::Last => replies.push(rx.clone()),
                Step::Chunk => {
                    replies.push(rx.clone());
                    check_cut!();
                    let r = resp.resume(ib, &mut rx);
                    cs.ev("R", "resume", &[], r, &rx);
                    step = r?;
                    continue;
                }
                Step::Done | Step::Wait => {}
            }
            break;
        }
        let mut next = None;
        for mut m in replies {
            check_cut!();
            tamper(Dir::ToInitiator, &mut m);
            assert!(m.len() <= capr + 3, "a responder message passes the frame cap");
            cs.note(&m, false);
            let r = init.handle(ia, &m, &mut tx);
            cs.ev("I", "handle", &m, r, &tx);
            match r? {
                Step::Send => {
                    assert!(tx.len() <= capi + 3, "an initiator message passes the frame cap");
                    next = Some(tx.clone());
                }
                Step::Last => {
                    check_cut!();
                    tamper(Dir::ToResponder, &mut tx);
                    cs.note(&tx, false);
                    let r = resp.handle(ib, &tx, &mut rx);
                    cs.ev("R", "handle", &tx, r, &rx);
                    r?;
                }
                Step::Wait | Step::Done | Step::Chunk => {}
            }
        }
        match next {
            Some(m) => tx = m,
            None => break,
        }
    }
    match init.report() {
        Some(rep) => {
            let here: Vec<Item> = rep.missing_here().map(<[u8]>::to_vec).collect();
            let there: Vec<Item> = rep.missing_there().map(<[u8]>::to_vec).collect();
            cs.rep(&here, &there);
            Ok(Some((here, there)))
        }
        None => Ok(None),
    }
}

/// The honest result: exactly the symmetric difference, each item once.
fn assert_exact(rep: &Report, a: &[Item], b: &[Item]) {
    let (only_b, only_a) = sym_diff(a, b);
    assert_eq!(sorted(rep.0.clone()), only_b, "items missing here");
    assert_eq!(sorted(rep.1.clone()), only_a, "items missing there");
    assert_eq!(rep.0.len(), only_b.len(), "no duplicates in here");
    assert_eq!(rep.1.len(), only_a.len(), "no duplicates in there");
}

fn nothing(_: Dir, _: &mut Vec<u8>) {}

/// An honest session on fresh objects, asserted exact.
fn honest(tr: &mut Tr, a: &[Item], b: &[Item], li: Limits, lr: Limits) -> Case {
    let mut cs = Case::new(tr, a, b, li, lr, b"set");
    let (ia, ib) = (index(a), index(b));
    let (mut init, mut resp) = (Initiator::new(li), Responder::new(lr));
    let rep = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, None)
        .expect("an honest session ends")
        .expect("an honest session finishes");
    assert_exact(&rep, a, b);
    cs
}

fn small_limits(max_item: usize, extra: usize) -> Limits {
    let mut l = Limits {
        max_item,
        max_message: 0,
        ..Limits::default()
    };
    l.max_message = l.min_message() + extra;
    l
}

fn dense_set(rng: &mut SplitMix64, n: usize, plen: usize, tail: usize) -> Vec<Item> {
    sorted(
        (0..n)
            .map(|_| {
                let mut it = vec![7u8; plen + tail];
                rng.fill(&mut it[plen..]);
                it
            })
            .collect(),
    )
}

// ---- the families --------------------------------------------------------------------------------------------------

fn basic_cases(tr: &mut Tr, rng: &mut SplitMix64) {
    let d = Limits::default();
    let mut cases = Vec::new();
    let e: Vec<Item> = vec![];
    cases.push(honest(tr, &e, &e, d, d));
    let s5 = fixed_set(rng, 5, 6);
    cases.push(honest(tr, &e, &s5, d, d));
    cases.push(honest(tr, &s5, &e, d, d));
    let s40 = fixed_set(rng, 40, 6);
    cases.push(honest(tr, &s40, &s40, d, d));
    let s100 = fixed_set(rng, 100, 6);
    cases.push(honest(tr, &e, &s100, d, d));
    cases.push(honest(tr, &s5, &s100, d, d));
    let s20 = fixed_set(rng, 20, 6);
    let s200 = fixed_set(rng, 200, 6);
    cases.push(honest(tr, &s200, &s20, d, d));
    cases.push(honest(tr, &s20, &s200, d, d));
    // A tiny responder against an initiator of the same size and a larger one.
    cases.push(honest(tr, &s20, &fixed_set(rng, 32, 6), d, d));
    // Differences of every size, default limits and the smallest limit of the item length.
    for len in [6usize, 40] {
        let base = fixed_set(rng, if len == 6 { 160 } else { 120 }, len);
        for dsz in [1usize, 2, 5, 17, 40, 100] {
            if len == 40 && dsz != 2 && dsz != 40 {
                continue;
            }
            let (other, ..) = mutate(rng, &base, dsz, len);
            let li = if len == 6 { small_limits(len, 0) } else { d };
            cases.push(honest(tr, &base, &other, d, d));
            cases.push(honest(tr, &base, &other, li, li));
            cases.push(honest(tr, &other, &base, li, small_limits(len, 40)));
        }
    }
    // Variable length items, prefixes of one another, the empty item.
    for (n, dsz) in [(150usize, 20usize), (150, 100), (60, 60)] {
        let mut base = var_set(rng, n, 6);
        base.insert(0, vec![]);
        let base = sorted(base);
        let mut other = var_set(rng, dsz, 6);
        other.extend(base.iter().step_by(2).cloned());
        let other = sorted(other);
        cases.push(honest(tr, &base, &other, d, d));
        cases.push(honest(tr, &other, &base, small_limits(6, 0), small_limits(6, 0)));
    }
    // Dense ranges: long shared prefixes, then the narrowing of splits under the smallest limit.
    for (plen, tail) in [(5usize, 3usize), (3, 2), (6, 2)] {
        let max_item = plen + tail;
        let base = dense_set(rng, 200, plen, tail);
        let other = dense_set(rng, 80, plen, tail);
        let mut merged = base.clone();
        merged.extend(other.iter().take(60).cloned());
        let merged = sorted(merged);
        for extra in [0usize, 7, 30] {
            let l = small_limits(max_item, extra);
            cases.push(honest(tr, &base, &merged, l, l));
            cases.push(honest(tr, &merged, &base, l, l));
        }
    }
    // Tiny items, tiny limits: chunked rounds and frames.
    for max_item in [3usize, 4, 6, 8] {
        let base = fixed_set(rng, 120, max_item);
        let (other, ..) = mutate(rng, &base, 70, max_item);
        for extra in [0usize, 1, 17, 100] {
            let l = small_limits(max_item, extra);
            cases.push(honest(tr, &base, &other, l, l));
            cases.push(honest(tr, &other, &base, l, l));
        }
        // A cold stream under the smallest limit: many chunks.
        let few = fixed_set(rng, 3, max_item);
        let l = small_limits(max_item, 0);
        cases.push(honest(tr, &few, &fixed_set(rng, 200, max_item), l, l));
    }
    for c in cases {
        c.finish(tr);
    }
}

fn error_cases(tr: &mut Tr, rng: &mut SplitMix64) {
    let d = Limits::default();
    let base = fixed_set(rng, 120, 6);
    let (other, ..) = mutate(rng, &base, 40, 6);
    // An item longer than max_item in the initiator's index (the start fails), in the responder's (cold stream and
    // split), and a set reference longer than max_item.
    let long = sorted([base.clone(), vec![vec![9; 10]]].concat());
    let lim4 = Limits {
        max_item: 6,
        ..Limits::default()
    };
    let small: Vec<Item> = base.iter().take(10).cloned().collect();
    let small_long = sorted([small.clone(), vec![vec![9; 10]]].concat());
    let run_err = |tr: &mut Tr, a: &[Item], b: &[Item], li: Limits, lr: Limits, rf: &[u8]| {
        let mut cs = Case::new(tr, a, b, li, lr, rf);
        let (ia, ib) = (index(a), index(b));
        let (mut init, mut resp) = (Initiator::new(li), Responder::new(lr));
        let r = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, None);
        cs.finish(tr);
        r
    };
    assert!(matches!(
        run_err(tr, &long, &base, lim4, lim4, b"s"),
        Err(Error::Index(_))
    ));
    assert!(matches!(
        run_err(tr, &base, &long, lim4, lim4, b"s"),
        Err(Error::Index(_))
    ));
    assert!(matches!(
        run_err(tr, &small, &small_long, lim4, lim4, b"s"),
        Err(Error::Index(_))
    ));
    assert!(matches!(
        run_err(tr, &small_long, &small, lim4, lim4, b"s"),
        Err(Error::Index(_))
    ));
    assert!(matches!(
        run_err(tr, &base, &other, lim4, lim4, &[1; 10]),
        Err(Error::ItemTooLarge)
    ));
    // A responder that allows less than the initiator's references.
    let lr = Limits {
        max_item: 2,
        ..Limits::default()
    };
    assert!(matches!(
        run_err(tr, &small, &base, d, lr, b"setref"),
        Err(Error::ItemTooLarge | Error::Index(_) | Error::Malformed(_))
    ));
    // Limits of rounds (the ends of a longer session too) and of the report.
    for rounds in [3u32, 4, 5, 7] {
        let l = Limits {
            max_rounds: rounds,
            ..d
        };
        let _ = run_err(tr, &base, &other, l, d, b"s");
        let _ = run_err(tr, &base, &other, d, l, b"s");
    }
    for rounds in [1u32, 2] {
        let l = Limits {
            max_rounds: rounds,
            ..d
        };
        let li = Limits {
            max_rounds: 1 << 20,
            ..d
        };
        let r = run_err(tr, &base, &other, l, li, b"s");
        assert!(
            matches!(r, Err(Error::TooManyRounds)),
            "initiator rounds {rounds}: {r:?}"
        );
        let r = run_err(tr, &base, &other, li, l, b"s");
        assert!(
            matches!(r, Err(Error::TooManyRounds)),
            "responder rounds {rounds}: {r:?}"
        );
    }
    for rep in [0usize, 10, 40, 100] {
        let l = Limits { max_report: rep, ..d };
        let r = run_err(tr, &base, &other, l, d, b"s");
        assert!(matches!(r, Err(Error::ReportTooLarge)), "report {rep}: {r:?}");
        let r = run_err(tr, &fixed_set(rng, 3, 6), &fixed_set(rng, 100, 6), l, d, b"s");
        assert!(matches!(r, Err(Error::ReportTooLarge)), "cold report {rep}: {r:?}");
    }
    // Enough room for exactly the difference.
    let l = Limits { max_report: 2000, ..d };
    assert!(run_err(tr, &base, &other, l, d, b"s").is_ok());
}

/// Tamper that changes the fingerprint of the final check the first `times` times it is delivered, so the responder
/// answers with a MISS (a check that disagrees); `checks` counts the checks delivered.
fn lying(checks: &mut usize, times: usize) -> impl FnMut(Dir, &mut Vec<u8>) + '_ {
    move |d, m| {
        if d == Dir::ToResponder && common_kind(m) == Some(6) {
            *checks += 1;
            if *checks <= times
                && let Some(x) = m.last_mut()
            {
                *x ^= 1;
            }
        }
    }
}

fn common_kind(m: &[u8]) -> Option<u8> {
    vinc_reconcile::frame_body(m)
        .ok()
        .and_then(|b| b.get(1).map(|t| t & 0x7f))
}

fn swap_bytes(msg: &mut [u8], from: &[u8], to: &[u8]) -> bool {
    match msg.windows(from.len()).position(|w| w == from) {
        Some(at) => {
            msg[at..at + to.len()].copy_from_slice(to);
            true
        }
        None => false,
    }
}

fn exactness_cases(tr: &mut Tr, rng: &mut SplitMix64) {
    let d = Limits::default();
    // A forced id collision, resolved by items.
    let common_items = fixed_set(rng, 198, 12);
    let y = vec![0xBB; 12];
    let mut x = y.clone();
    x[11] = 0xBC;
    let (mut a, mut b) = (common_items.clone(), common_items);
    a.push(y.clone());
    b.push(x.clone());
    let (a, b) = (sorted(a), sorted(b));
    let mut cs = Case::new(tr, &a, &b, d, d, b"set");
    let (ia, ib) = (index(&a), index(&b));
    let (mut init, mut resp) = (Initiator::new(d), Responder::new(d));
    let mut collided = 0;
    let rep = session(
        &mut cs,
        &mut init,
        &mut resp,
        &ia,
        &ib,
        &mut |dir, m| {
            if dir == Dir::ToResponder {
                collided += usize::from(swap_bytes(m, &item_id(&y), &item_id(&x)));
            }
        },
        None,
    )
    .unwrap()
    .unwrap();
    assert_eq!(collided, 1);
    assert_exact(&rep, &a, &b);
    // The same objects again, honestly (no state leaks across sessions).
    let rep = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, None)
        .unwrap()
        .unwrap();
    assert_exact(&rep, &a, &b);
    cs.finish(tr);

    // A responder that claims the check disagrees: once (the exact pass answers), and always (Mismatch).
    let base = fixed_set(rng, 150, 6);
    let (other, ..) = mutate(rng, &base, 30, 6);
    let mut cs = Case::new(tr, &base, &other, d, d, b"set");
    let (ia, ib) = (index(&base), index(&other));
    let (mut init, mut resp) = (Initiator::new(d), Responder::new(d));
    let mut checks = 0;
    let rep = session(
        &mut cs,
        &mut init,
        &mut resp,
        &ia,
        &ib,
        &mut lying(&mut checks, 99),
        None,
    );
    assert!(matches!(rep, Err(Error::Mismatch)), "{rep:?}");
    let mut checks = 0;
    let rep = session(
        &mut cs,
        &mut init,
        &mut resp,
        &ia,
        &ib,
        &mut lying(&mut checks, 1),
        None,
    )
    .unwrap()
    .unwrap();
    assert_eq!(checks, 2);
    assert_exact(&rep, &base, &other);
    cs.finish(tr);

    // Resets: a session cut at every call, then the whole session again on the same objects.
    let base = fixed_set(rng, 100, 6);
    let (other, ..) = mutate(rng, &base, 30, 6);
    for l in [d, small_limits(6, 0)] {
        let mut cs = Case::new(tr, &base, &other, l, l, b"set");
        let (ia, ib) = (index(&base), index(&other));
        let (mut init, mut resp) = (Initiator::new(l), Responder::new(l));
        for cut in 0..14 {
            let r = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, Some(cut)).unwrap();
            assert!(r.is_none() || cut > 3);
            let rep = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, None)
                .unwrap()
                .unwrap();
            assert_exact(&rep, &base, &other);
        }
        cs.finish(tr);
    }
    // A cold session cut, then redone.
    let few = fixed_set(rng, 3, 4);
    let many = fixed_set(rng, 120, 4);
    let l = small_limits(4, 0);
    let mut cs = Case::new(tr, &few, &many, l, l, b"set");
    let (ia, ib) = (index(&few), index(&many));
    let (mut init, mut resp) = (Initiator::new(l), Responder::new(l));
    for cut in [0usize, 1, 2, 5, 9] {
        let _ = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, Some(cut)).unwrap();
        let rep = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut nothing, None)
            .unwrap()
            .unwrap();
        assert_exact(&rep, &few, &many);
    }
    cs.finish(tr);
}

/// First messages that are not what an initiator writes, delivered to a fresh responder.
fn header_cases(tr: &mut Tr, rng: &mut SplitMix64) {
    let d = Limits::default();
    let b = fixed_set(rng, 100, 6);
    let a = fixed_set(rng, 100, 6);
    let mut cs = Case::new(tr, &a, &b, d, d, b"set");
    let (ia, ib) = (index(&a), index(&b));
    let _ = ia;
    let mut resp = Responder::new(d);
    let bodies: Vec<Vec<u8>> = vec![
        vec![],
        vec![0],
        vec![0, 0],
        vec![0, 0, 0],
        vec![0, 100, 0],
        vec![0, 100, 2],
        vec![0, 100, 3, 0, 0],
        vec![5, 1, 2],
        vec![200, 255],
        vec![0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80],
        vec![0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f, 0],
        vec![0, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x80, 0x00],
        vec![0, 100, 0x80, 0x80, 0x80, 0x80, 0x10],
        vec![0, 100, 1, 0x81, 0, 0],
        vec![0, 100, 2, 0x81, 0, 0],
        vec![0, 100, 1, 0x00, 0, 0],
        vec![0, 100, 1, 0x88, 0, 0],
        vec![0, 5, 2, 0x82, 0, 0, 0],
    ];
    for (i, body) in bodies.iter().enumerate() {
        let mut msg = vec![0, 0, 0];
        msg.extend_from_slice(body);
        fix_len(&mut msg);
        if i % 5 == 4 {
            msg[2] = msg[2].wrapping_add(1);
        }
        cs.begin();
        resp.reset();
        cs.reset();
        cs.note(&msg, true);
        cs.r_fresh = false;
        let mut rx = Vec::new();
        let r = resp.handle(&ib, &msg, &mut rx);
        cs.ev("R", "handle", &msg, r, &rx);
        cs.end();
    }
    // A header that names a longer reference than the limit allows.
    let lr = Limits { max_item: 3, ..d };
    let mut cs2 = Case::new(tr, &a, &b, d, lr, b"set");
    let mut resp = Responder::new(lr);
    let ia = index(&a);
    let mut init = Initiator::new(d);
    let r = session(&mut cs2, &mut init, &mut resp, &ia, &index(&b), &mut nothing, None);
    assert!(r.is_err());
    cs2.finish(tr);
    cs.finish(tr);
}

/// Fault injection: one changed message per session, on the messages of an honest session, objects reused.
fn mutation_cases(tr: &mut Tr, rng: &mut SplitMix64) {
    let d = Limits {
        max_rounds: 400,
        ..Limits::default()
    };
    let t4 = Limits {
        max_rounds: 400,
        ..small_limits(4, 0)
    };
    let t8 = Limits {
        max_rounds: 400,
        ..small_limits(8, 9)
    };
    let s6 = fixed_set(rng, 45, 6);
    let (s6b, ..) = mutate(rng, &s6, 10, 6);
    let t4a = fixed_set(rng, 36, 4);
    let (t4b, ..) = mutate(rng, &t4a, 16, 4);
    let few = fixed_set(rng, 3, 4);
    let many = fixed_set(rng, 50, 4);
    let tiny = fixed_set(rng, 25, 6);
    let dn = dense_set(rng, 36, 5, 3);
    let dn2 = sorted([dn.clone(), dense_set(rng, 14, 5, 3)].concat());
    let vs = var_set(rng, 36, 5);
    let (vs2, ..) = (sorted([vs.clone(), var_set(rng, 14, 5)].concat()), 0);
    let scenarios: Vec<(Vec<Item>, Vec<Item>, Limits, bool)> = vec![
        (s6.clone(), s6b.clone(), d, false),
        (s6b.clone(), s6.clone(), d, false),
        (t4a.clone(), t4b.clone(), t4, false),
        (t4b.clone(), t4a.clone(), t4, false),
        (few, many.clone(), t4, false),
        (tiny.clone(), s6.clone(), d, false),
        (dn.clone(), dn2.clone(), t8, false),
        (vs.clone(), vs2, small_limits(5, 3), false),
        (s6.clone(), s6b, d, true),
    ];
    for (a, b, l, collide) in scenarios {
        let mut a = a;
        let mut b = b;
        let (y, x) = (vec![0xBB; 6], vec![0xBB, 0xBB, 0xBB, 0xBB, 0xBB, 0xBC]);
        if collide {
            a.push(y.clone());
            b.push(x.clone());
            a = sorted(a);
            b = sorted(b);
        }
        let mut cs = Case::new(tr, &a, &b, l, l, b"set");
        let (ia, ib) = (index(&a), index(&b));
        let (mut init, mut resp) = (Initiator::new(l), Responder::new(l));
        let mut base = |dir: Dir, m: &mut Vec<u8>| {
            if collide && dir == Dir::ToResponder {
                swap_bytes(m, &item_id(&y), &item_id(&x));
            }
        };
        let mut log: Vec<(Dir, Vec<u8>, bool)> = Vec::new();
        let mut first = true;
        let rep = session(
            &mut cs,
            &mut init,
            &mut resp,
            &ia,
            &ib,
            &mut |dir, m| {
                base(dir, m);
                log.push((dir, m.clone(), first && dir == Dir::ToResponder));
                first = false;
            },
            None,
        )
        .unwrap()
        .unwrap();
        assert_exact(&rep, &a, &b);
        let picks: Vec<usize> = if log.len() <= 9 {
            (0..log.len()).collect()
        } else {
            (0..9).map(|k| k * log.len() / 9).collect()
        };
        for idx in picks {
            for kind in 0..15u32 {
                let mut k = 0usize;
                let seed = rng.next_u64();
                let mut mrng = SplitMix64::new(seed);
                let isfirst = log[idx].2;
                let r = session(
                    &mut cs,
                    &mut init,
                    &mut resp,
                    &ia,
                    &ib,
                    &mut |dir, m| {
                        base(dir, m);
                        if k == idx {
                            mutate_msg(kind, m, isfirst, &mut mrng);
                        }
                        k += 1;
                    },
                    None,
                );
                let _ = r;
            }
        }
        // The objects still do an honest session after all of that.
        let rep = session(&mut cs, &mut init, &mut resp, &ia, &ib, &mut base, None)
            .unwrap()
            .unwrap();
        assert_exact(&rep, &a, &b);
        cs.finish(tr);
    }
}

#[test]
fn reconcile_sessions_match_the_models() {
    let mut rng = SplitMix64::new(0x7265_636f_6e63_696c);
    let on = std::env::var("VINC_TRACE_DIR").is_ok();
    let mut tr = Tr { on, ..Tr::default() };
    basic_cases(&mut tr, &mut rng);
    error_cases(&mut tr, &mut rng);
    exactness_cases(&mut tr, &mut rng);
    header_cases(&mut tr, &mut rng);
    mutation_cases(&mut tr, &mut rng);
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("reconcile.ndjson"), &tr.norm).unwrap();
        if !tr.big.is_empty() {
            std::fs::write(std::path::Path::new(&dir).join("reconcile_big.ndjson"), &tr.big).unwrap();
        }
        for (k, v) in &tr.stats {
            eprintln!("rc {k}: {v}");
        }
        eprintln!("rc bytes: {} + {}", tr.norm.len(), tr.big.len());
    }
}
