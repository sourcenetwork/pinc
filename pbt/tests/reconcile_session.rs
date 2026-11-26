//! `pinc-reconcile`: whole sessions of the real initiator and responder, run to the end over the sans-IO API the
//! drivers use, on set pairs of every shape.
//!
//! Where the expected behaviour comes from:
//! - the crate documentation: "The initiator learns the exact difference", "no input can make any call panic", and
//!   "A round larger than one message is spread over as many messages as it needs, each within
//!   [`Limits::max_message`], so a valid difference never fails for its size; only the host-set report limit can end
//!   it";
//! - `Report::missing_here` ("The items the peer has and the initiator lacks") and `Report::missing_there` ("The
//!   items the initiator has and the peer lacks");
//! - `Limits::max_report` ("The most bytes of difference the initiator keeps for its report");
//! - `docs/proofs/properties.md`, the reconcile rows: "every message a handler writes is a valid frame whose body is
//!   at most `cap + 2 max_item + 36`", "the parts of a pass are at most `17 + 17 D (2 (lg nA + lg nB) + 2)`" (with
//!   `lg` the smallest `k` with `n <= 2^k`, `f = 2` always holds), "two equal sets cost at most 17 parts whatever
//!   their sizes", and "a run on used objects, in any state, ends as the run on new objects with the same limits and
//!   role".
//!
//! The existing suites (`tests/reconcile_*.rs`) run fixed seeds, or proptest over sets of at most 120 items of at
//! most 24 bytes from a 4-letter alphabet with `max_item = 32`. These properties aim past that: sets up to a few
//! thousand items, shared prefixes around the 255-byte cap of the bound encoding, the empty item and the top of the
//! key space, message limits from `min_message()` up, report limits around the difference, reused objects, and peers
//! that lie in well-formed messages.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

use std::collections::{BTreeSet, VecDeque};
use std::ops::ControlFlow;

use ephyra::prelude::*;
use ephyra::{check_generator, check_shrinker};
use pinc_reconcile::wire::{count, first_set_ref, frame_body, put_bound, put_parts, put_varint, read_bound, read_parts};
use pinc_reconcile::{Error, Initiator, Limits, MemError, MemIndex, Responder, Step};
use pinc_wire::Reader;

type Item = Vec<u8>;
type Err = Error<MemError>;

const SET: &[u8] = b"set";
/// The most messages one simulated session delivers before it is called stuck: far above any valid exchange of the
/// sets generated here, low enough that a loop ends the test in seconds.
const MAX_STEPS: usize = 200_000;

// ---- cases ------------------------------------------------------------------------------------------------------

/// Two sets and the limits a session between them runs under.
#[derive(Clone)]
struct Case {
    a: Vec<Item>,
    b: Vec<Item>,
    /// `max_item` is the longest item (or the set reference) plus this.
    slack: usize,
    /// `max_message` is `min_message()` plus this; `None` is the default limit.
    extra: Option<usize>,
}

impl Case {
    fn limits(&self) -> Limits {
        let longest = self.a.iter().chain(&self.b).map(Vec::len).max().unwrap_or(0).max(SET.len());
        let base = Limits {
            max_item: longest + self.slack,
            ..Limits::default()
        };
        match self.extra {
            Some(x) => Limits {
                max_message: base.min_message() + x,
                ..base
            },
            None => base,
        }
    }
}

/// An item as hex with runs of one byte folded (`00*300 43`), so a counterexample with long shared prefixes reads.
fn show(it: &[u8]) -> String {
    let mut out = Vec::new();
    let mut i = 0;
    while let Some(&b) = it.get(i) {
        let run = it[i..].iter().take_while(|x| **x == b).count();
        out.push(if run > 3 { format!("{b:02x}*{run}") } else { vec![format!("{b:02x}"); run].join(" ") });
        i += run;
    }
    format!("[{}]", out.join(" "))
}

fn show_set(v: &[Item]) -> String {
    format!("{{{}}}", v.iter().map(|x| show(x)).collect::<Vec<_>>().join(", "))
}

impl std::fmt::Debug for Case {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Case {{ a: {}, b: {}, slack: {}, extra: {:?} }}",
            show_set(&self.a),
            show_set(&self.b),
            self.slack,
            self.extra
        )
    }
}

fn strictly_sorted(v: &[Item]) -> bool {
    v.windows(2).all(|w| w[0] < w[1])
}

fn case_ok(c: &Case) -> bool {
    strictly_sorted(&c.a) && strictly_sorted(&c.b)
}

fn case_size(c: &Case) -> u64 {
    let bytes: usize = c.a.iter().chain(&c.b).map(Vec::len).sum();
    (c.a.len() + c.b.len() + bytes + c.slack) as u64 + c.extra.map_or(0, |x| x as u64 + 1)
}

/// The key universe of a case: items of a shared prefix (possibly around the 255-byte cap of the bound encoding)
/// and a short suffix from a small or a full alphabet, sometimes the empty item and an item at the top of the order.
fn universe(g: &mut Source) -> Vec<Item> {
    let (lo, hi) = *g.weighted(&[(4, (0usize, 40usize)), (4, (30, 200)), (2, (200, 900)), (1, (900, 2500))]);
    let n = g.int(lo..=hi);
    let plen = *g.pick(&[0usize, 0, 0, 1, 3, 254, 255, 256, 257, 300]);
    let pbyte = *g.pick(&[0u8, 0xff, 0x41]);
    let alphabets: [&[u8]; 4] = [&[0, 1], &[0, 1, 2, 3], &[0x00, 0xff], &[]];
    let alpha = *g.pick(&alphabets);
    let maxlen = *g.pick(&[1usize, 2, 4, 8, 24, 40]);
    let mixed = g.bool_with(0.3);
    let mut out = BTreeSet::new();
    for _ in 0..n {
        let p = if mixed && g.bool() { g.int(0..=plen) } else { plen };
        let mut it = vec![pbyte; p];
        for _ in 0..g.int(0..=maxlen) {
            it.push(if alpha.is_empty() { g.int(0u8..=255) } else { *g.pick(alpha) });
        }
        out.insert(it);
    }
    if g.bool_with(0.2) {
        out.insert(Vec::new());
    }
    if g.bool_with(0.2) {
        out.insert(vec![0xff; plen + maxlen + 1]);
    }
    out.into_iter().collect()
}

/// Which items of the universe go to which side: 0 both, 1 only A, 2 only B, 3 neither.
fn assign(g: &mut Source, n: usize) -> Vec<u8> {
    match g.int(0u8..=6) {
        // A random difference over a shared base.
        0 | 1 => {
            let both = *g.pick(&[50u32, 90, 99, 100]);
            (0..n)
                .map(|_| {
                    let r = g.int(0u32..100);
                    if r < both { 0 } else { g.int(1u8..=3) }
                })
                .collect()
        },
        // Equal sets.
        2 => vec![0; n],
        // Disjoint sets.
        3 => (0..n).map(|_| g.int(1u8..=2)).collect(),
        // One item apart.
        4 => {
            let mut v = vec![0; n];
            if n > 0 {
                v[g.index(n)] = g.int(1u8..=2);
            }
            v
        },
        // A difference clustered in one window of the key order.
        5 => {
            let s = if n > 0 { g.index(n) } else { 0 };
            let e = s + g.int(0..=(n - s));
            (0..n).map(|i| if (s..e).contains(&i) { g.int(0u8..=3) } else { 0 }).collect()
        },
        // One side empty.
        _ => {
            let side = g.int(1u8..=2);
            vec![side; n]
        },
    }
}

fn split_sets(u: &[Item], who: &[u8]) -> (Vec<Item>, Vec<Item>) {
    let (mut a, mut b) = (Vec::new(), Vec::new());
    for (it, w) in u.iter().zip(who) {
        if *w == 0 || *w == 1 {
            a.push(it.clone());
        }
        if *w == 0 || *w == 2 {
            b.push(it.clone());
        }
    }
    (a, b)
}

fn draw_pair(g: &mut Source) -> (Vec<Item>, Vec<Item>) {
    let u = universe(g);
    let who = assign(g, u.len());
    split_sets(&u, &who)
}

fn draw_limits(g: &mut Source) -> (usize, Option<usize>) {
    let slack = *g.pick(&[0usize, 0, 1, 37, 4096]);
    let extra = if g.bool_with(0.25) {
        None
    } else {
        Some(*g.weighted(&[(3, 0usize), (2, 1), (2, 9), (2, 100), (2, 1000), (1, 20_000)]))
    };
    (slack, extra)
}

fn shrink_list(v: &[Item], mut visit: impl FnMut(Vec<Item>) -> ControlFlow<()>) -> ControlFlow<()> {
    if v.is_empty() {
        return ControlFlow::Continue(());
    }
    visit(Vec::new())?;
    let n = v.len();
    if n > 1 {
        visit(v[n / 2..].to_vec())?;
        visit(v[..n / 2].to_vec())?;
    }
    if n > 16 {
        for k in 0..8 {
            let (s, e) = (n * k / 8, n * (k + 1) / 8);
            let mut w = v[..s].to_vec();
            w.extend_from_slice(&v[e..]);
            visit(w)?;
        }
    } else {
        for i in 0..n {
            let mut w = v.to_vec();
            w.remove(i);
            visit(w)?;
        }
    }
    ControlFlow::Continue(())
}

fn shrink_case(c: &Case, visit: &mut dyn FnMut(Case) -> ControlFlow<()>) -> ControlFlow<()> {
    // A prefix every item shares can go from all of them at once: the order and the distinctness stay.
    let mut all = c.a.iter().chain(&c.b);
    if let Some(first) = all.next() {
        let p = all.fold(first.len(), |p, x| p.min(first.iter().zip(x).take_while(|(u, v)| u == v).count()));
        for cut in [p, p / 2] {
            if cut > 0 {
                let strip = |s: &[Item]| s.iter().map(|x| x[cut..].to_vec()).collect::<Vec<_>>();
                visit(Case {
                    a: strip(&c.a),
                    b: strip(&c.b),
                    ..c.clone()
                })?;
            }
        }
    }
    // Items both sides hold go together, so the difference keeps its shape while the sets get smaller.
    let common: Vec<Item> = c.a.iter().filter(|x| c.b.binary_search(x).is_ok()).cloned().collect();
    shrink_list(&common, |keep| {
        let keep: BTreeSet<Item> = keep.into_iter().collect();
        let drop = |s: &[Item]| -> Vec<Item> {
            s.iter()
                .filter(|x| keep.contains(*x) || common.binary_search(x).is_err())
                .cloned()
                .collect()
        };
        visit(Case {
            a: drop(&c.a),
            b: drop(&c.b),
            ..c.clone()
        })
    })?;
    shrink_list(&c.a, |a| visit(Case { a, ..c.clone() }))?;
    shrink_list(&c.b, |b| visit(Case { b, ..c.clone() }))?;
    if c.slack > 0 {
        visit(Case { slack: 0, ..c.clone() })?;
    }
    if let Some(x) = c.extra
        && x > 0
    {
        visit(Case {
            extra: Some(0),
            ..c.clone()
        })?;
        visit(Case {
            extra: Some(x / 2),
            ..c.clone()
        })?;
    }
    ControlFlow::Continue(())
}

fn cases() -> ephyra::BoxGen<Case> {
    (|g: &mut Source| {
        let (a, b) = draw_pair(g);
        let (slack, extra) = draw_limits(g);
        Case { a, b, slack, extra }
    })
    .with_shrink(shrink_case)
    .boxed()
}

// ---- the session ------------------------------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Dir {
    /// Initiator to responder.
    Up,
    /// Responder to initiator.
    Down,
}

#[derive(Debug, PartialEq, Eq)]
enum Fail {
    Init(Err),
    Resp(Err),
    /// The initiator was waiting when the responder finished the stream (the driver's `RunError::Closed`).
    Closed,
    /// A handler asked for something its role never does.
    Role(&'static str),
    Stuck,
}

#[derive(Debug, Default)]
struct Outcome {
    log: Vec<(Dir, Vec<u8>)>,
    here: Vec<Item>,
    there: Vec<Item>,
    /// The responder ended the way its driver ends a finished session.
    resp_done: bool,
}

fn index(set: &[Item]) -> MemIndex {
    MemIndex::from_sorted(set.iter().map(Vec::as_slice)).unwrap()
}

/// One session between `init` over `a` and `resp` over `b`, delivered message by message the way
/// `Initiator::run` and `Responder::serve` drive them over a channel. `tamper` sees and may change every message
/// as it is sent (its index counts the messages of the session); `stop_after` cuts the session after that many
/// deliveries, leaving both objects wherever they are.
fn session(
    init: &mut Initiator,
    resp: &mut Responder,
    a: &MemIndex,
    b: &MemIndex,
    tamper: &mut dyn FnMut(Dir, usize, &mut Vec<u8>),
    stop_after: Option<usize>,
) -> Result<Outcome, Fail> {
    let mut o = Outcome::default();
    let mut up: VecDeque<(Vec<u8>, bool)> = VecDeque::new();
    let mut down: VecDeque<(Vec<u8>, bool)> = VecDeque::new();
    let mut sent = 0usize;
    let mut post = |o: &mut Outcome, q: &mut VecDeque<(Vec<u8>, bool)>, dir: Dir, mut m: Vec<u8>, fin: bool| {
        if !m.is_empty() {
            tamper(dir, sent, &mut m);
            sent += 1;
            o.log.push((dir, m.clone()));
        }
        q.push_back((m, fin));
    };
    let (mut tx, mut rx) = (Vec::new(), Vec::new());
    resp.reset();
    init.start(a, SET, &mut tx).map_err(Fail::Init)?;
    post(&mut o, &mut up, Dir::Up, tx.clone(), false);
    let (mut init_done, mut resp_fresh) = (false, true);
    let mut down_fin = false;
    let mut delivered = 0usize;
    for _ in 0..MAX_STEPS {
        if stop_after.is_some_and(|s| delivered >= s) {
            return Ok(o);
        }
        if let Some((m, _)) = up.pop_front() {
            if m.is_empty() || o.resp_done {
                continue;
            }
            delivered += 1;
            if resp_fresh {
                // `serve` resolves the set from the first message before it hands it to the state machine.
                if first_set_ref(&m) != Ok(SET) {
                    return Err(Fail::Resp(Error::Malformed(pinc_reconcile::Reason::Truncated)));
                }
                resp_fresh = false;
            }
            let mut step = resp.handle(b, &m, &mut rx).map_err(Fail::Resp)?;
            while step == Step::Chunk {
                post(&mut o, &mut down, Dir::Down, rx.clone(), false);
                step = resp.resume(b, &mut rx).map_err(Fail::Resp)?;
            }
            match step {
                Step::Send => post(&mut o, &mut down, Dir::Down, rx.clone(), false),
                Step::Last => {
                    post(&mut o, &mut down, Dir::Down, rx.clone(), true);
                    o.resp_done = true;
                },
                Step::Done => {
                    post(&mut o, &mut down, Dir::Down, Vec::new(), true);
                    o.resp_done = true;
                },
                Step::Wait | Step::Chunk => {},
            }
            continue;
        }
        if let Some((m, fin)) = down.pop_front() {
            down_fin |= fin;
            if init_done || m.is_empty() {
                continue;
            }
            delivered += 1;
            match init.handle(a, &m, &mut tx).map_err(Fail::Init)? {
                Step::Send => post(&mut o, &mut up, Dir::Up, tx.clone(), false),
                Step::Last => {
                    post(&mut o, &mut up, Dir::Up, tx.clone(), true);
                    init_done = true;
                },
                Step::Wait => {},
                Step::Done => init_done = true,
                Step::Chunk => return Err(Fail::Role("the initiator asked to stream a chunk")),
            }
            continue;
        }
        if !init_done {
            return Err(if down_fin { Fail::Closed } else { Fail::Stuck });
        }
        let rep = init.report().ok_or(Fail::Role("a finished initiator has no report"))?;
        o.here = rep.missing_here().map(<[u8]>::to_vec).collect();
        o.there = rep.missing_there().map(<[u8]>::to_vec).collect();
        assert_eq!(rep.here_count(), o.here.len(), "here_count disagrees with the items it yields");
        assert_eq!(rep.there_count(), o.there.len(), "there_count disagrees with the items it yields");
        return Ok(o);
    }
    Err(Fail::Stuck)
}

fn fresh(c: &Case, tamper: &mut dyn FnMut(Dir, usize, &mut Vec<u8>)) -> (Result<Outcome, Fail>, Limits) {
    let lim = c.limits();
    let (ia, ib) = (index(&c.a), index(&c.b));
    let r = session(&mut Initiator::new(lim), &mut Responder::new(lim), &ia, &ib, tamper, None);
    (r, lim)
}

fn sym_diff(a: &[Item], b: &[Item]) -> (Vec<Item>, Vec<Item>) {
    let only_b = b.iter().filter(|x| a.binary_search(x).is_err()).cloned().collect();
    let only_a = a.iter().filter(|x| b.binary_search(x).is_err()).cloned().collect();
    (only_b, only_a)
}

fn sorted(mut v: Vec<Item>) -> Vec<Item> {
    v.sort_unstable();
    v
}

/// The part count of a message (after the set reference and item count of the first one).
fn parts_of(m: &[u8], first: bool) -> usize {
    let mut r = Reader::new(frame_body(m).unwrap());
    if first {
        let n = count(&mut r).unwrap();
        r.read_bytes(n).unwrap();
        r.read_varint().unwrap();
    }
    read_parts(&mut r).unwrap().0
}

/// The smallest `k` with `n <= 2^k` (0 below 2): `lg 2 n` of the cost theorems.
fn lg2(n: usize) -> usize {
    if n < 2 { 0 } else { (usize::BITS - (n - 1).leading_zeros()) as usize }
}

/// Whether the responder streams its list (`Core::is_cold`, restated from its documentation: "A small or cold side
/// streams its whole list instead"; `nb <= 32` or `10 na < nb`).
fn is_cold(na: usize, nb: usize) -> bool {
    nb <= 32 || na.saturating_mul(10) < nb
}

#[ephyra::test(gen = cases(), tests = 300)]
fn honest_sessions_report_exactly_the_symmetric_difference(c: Case) {
    let (r, lim) = fresh(&c, &mut |_, _, _| {});
    let o = match r {
        Ok(o) => o,
        Err(e) => panic!("an honest session failed: {e:?} (limits {lim:?})"),
    };
    let (only_b, only_a) = sym_diff(&c.a, &c.b);
    assert_eq!(sorted(o.here.clone()), only_b, "missing_here is not B \\ A");
    assert_eq!(sorted(o.there.clone()), only_a, "missing_there is not A \\ B");
    assert!(o.resp_done, "the responder did not end its stream");
    let frame_cap = lim.max_message.min(0x00ff_ffff) + 2 * lim.max_item + 36;
    for (dir, m) in &o.log {
        let body = frame_body(m).expect("a handler wrote a message that is not a frame");
        assert!(body.len() <= frame_cap, "{dir:?} body {} past the frame cap {frame_cap}", body.len());
    }
    if !is_cold(c.a.len(), c.b.len()) {
        let parts: usize = o.log.iter().enumerate().map(|(i, (_, m))| parts_of(m, i == 0)).sum();
        let d = only_a.len() + only_b.len();
        let bound = 17 + 17 * d * (2 * (lg2(c.a.len()) + lg2(c.b.len())) + 2);
        // The final check and its answer are outside the pass the bound counts.
        assert!(parts <= bound + 2, "{parts} parts for a difference of {d}: past the bound {bound}");
        if d == 0 {
            assert!(parts <= 17, "two equal sets took {parts} parts");
        }
    }
}

#[ephyra::test(gen = cases(), tests = 100)]
fn swapping_the_roles_mirrors_the_report(c: Case) {
    let (ab, _) = fresh(&c, &mut |_, _, _| {});
    let swapped = Case {
        a: c.b.clone(),
        b: c.a.clone(),
        ..c.clone()
    };
    let (ba, _) = fresh(&swapped, &mut |_, _, _| {});
    let (ab, ba) = (ab.expect("a to b failed"), ba.expect("b to a failed"));
    assert_eq!(sorted(ab.here), sorted(ba.there), "what a lacks is not what b has over a");
    assert_eq!(sorted(ab.there), sorted(ba.here), "what b lacks is not what a has over b");
}

// ---- the report limit -------------------------------------------------------------------------------------------

/// The bytes of a report: each item as `venc(len) item`.
fn report_bytes(items: &[Item]) -> usize {
    items.iter().map(|x| pinc_wire::varint::encoded_len(x.len() as u64) + x.len()).sum()
}

#[ephyra::test(gen = (cases(), gens::int(0usize..=40), gens::int(0u8..=2)), tests = 200)]
fn the_report_limit_ends_a_session_only_when_the_difference_passes_it(input: (Case, usize, u8)) {
    let (c, delta, side) = input;
    let (only_b, only_a) = sym_diff(&c.a, &c.b);
    let total = report_bytes(&only_b) + report_bytes(&only_a);
    // A limit just under, at, or comfortably over the difference (`push` keeps one varint of headroom).
    let max_report = match side {
        0 => total.saturating_sub(delta),
        1 => total + delta,
        _ => total + pinc_wire::varint::MAX_LEN + delta,
    };
    let lim = Limits { max_report, ..c.limits() };
    let (ia, ib) = (index(&c.a), index(&c.b));
    let r = session(&mut Initiator::new(lim), &mut Responder::new(lim), &ia, &ib, &mut |_, _, _| {}, None);
    match r {
        Ok(o) => {
            assert!(
                report_bytes(&o.here) + report_bytes(&o.there) <= max_report,
                "the report holds more than the report limit"
            );
            assert_eq!(sorted(o.here), only_b, "missing_here is not B \\ A under a report limit");
            assert_eq!(sorted(o.there), only_a, "missing_there is not A \\ B under a report limit");
        },
        Err(Fail::Init(Error::ReportTooLarge)) => assert!(
            total + pinc_wire::varint::MAX_LEN > max_report,
            "a difference of {total} bytes was refused under a report limit of {max_report}"
        ),
        Err(e) => panic!("a session under a report limit failed otherwise: {e:?}"),
    }
}

// ---- reused objects ---------------------------------------------------------------------------------------------

#[derive(Clone, Debug)]
struct Reuse {
    first: Case,
    /// The first session is cut after this many deliveries (`None`: run to the end).
    cut: Option<usize>,
    /// The second session's sets; it runs under the first one's limits.
    a2: Vec<Item>,
    b2: Vec<Item>,
}

fn reuses() -> ephyra::BoxGen<Reuse> {
    (|g: &mut Source| {
        let (a, b) = draw_pair(g);
        let (slack, extra) = draw_limits(g);
        let first = Case { a, b, slack, extra };
        let cut = if g.bool_with(0.6) { Some(g.int(0usize..=12)) } else { None };
        // The second pair keeps the first's item lengths within its item limit.
        let max = first.limits().max_item;
        let (mut a2, mut b2) = draw_pair(g);
        a2.retain(|x| x.len() <= max);
        b2.retain(|x| x.len() <= max);
        Reuse { first, cut, a2, b2 }
    })
    .with_shrink(|r: &Reuse, visit: &mut dyn FnMut(Reuse) -> ControlFlow<()>| {
        shrink_case(&r.first, &mut |first| visit(Reuse { first, ..r.clone() }))?;
        shrink_list(&r.a2, |a2| visit(Reuse { a2, ..r.clone() }))?;
        shrink_list(&r.b2, |b2| visit(Reuse { b2, ..r.clone() }))
    })
    .boxed()
}

#[ephyra::test(gen = reuses(), tests = 150)]
fn a_session_on_used_objects_ends_as_on_new_ones(r: Reuse) {
    let lim = r.first.limits();
    let (mut init, mut resp) = (Initiator::new(lim), Responder::new(lim));
    let (ia, ib) = (index(&r.first.a), index(&r.first.b));
    let _ = session(&mut init, &mut resp, &ia, &ib, &mut |_, _, _| {}, r.cut);
    let (ia2, ib2) = (index(&r.a2), index(&r.b2));
    let used = session(&mut init, &mut resp, &ia2, &ib2, &mut |_, _, _| {}, None);
    let new = session(&mut Initiator::new(lim), &mut Responder::new(lim), &ia2, &ib2, &mut |_, _, _| {}, None);
    match (used, new) {
        (Ok(u), Ok(n)) => {
            assert_eq!(u.log, n.log, "the messages of a session on used objects differ from new ones");
            assert_eq!(u.here, n.here, "missing_here on used objects differs");
            assert_eq!(u.there, n.there, "missing_there on used objects differs");
        },
        (u, n) => assert_eq!(u.err(), n.err(), "used and new objects end differently"),
    }
}

// ---- id collisions -----------------------------------------------------------------------------------------------

/// The first ids part of an initiator message: its bounds (`None` for an infinite upper bound), the offset of its
/// first id in the message and the id count.
fn first_ids_part(m: &[u8], first: bool) -> Option<(Vec<u8>, Option<Vec<u8>>, usize, usize)> {
    let body = frame_body(m).ok()?;
    let mut r = Reader::new(body);
    if first {
        let n = count(&mut r).ok()?;
        r.read_bytes(n).ok()?;
        r.read_varint().ok()?;
    }
    let (n, _) = read_parts(&mut r).ok()?;
    let mut last = Vec::new();
    for _ in 0..n {
        let tag = r.read_u8().ok()?;
        read_bound(&mut last, &mut r, usize::MAX).ok()?;
        let lo = last.clone();
        let hi = if tag & INF == 0 {
            read_bound(&mut last, &mut r, usize::MAX).ok()?;
            Some(last.clone())
        } else {
            None
        };
        match tag & !INF {
            1 | 6 => {
                r.read_bytes(32).ok()?;
            },
            2 => {
                let c = count(&mut r).ok()?;
                return Some((lo, hi, 3 + r.position(), c));
            },
            3 => {
                read_items(&mut r);
            },
            _ => return None,
        }
    }
    None
}

#[derive(Clone, Debug)]
struct Collide {
    case: Case,
    /// Which id of the part (modulo the count) collides, and with which of the responder's items in its range.
    which: usize,
    with: usize,
}

fn collisions() -> ephyra::BoxGen<Collide> {
    (|g: &mut Source| {
        let (a, b) = draw_pair(g);
        let (slack, extra) = draw_limits(g);
        Collide {
            case: Case { a, b, slack, extra },
            which: g.int(0usize..=64),
            with: g.int(0usize..=64),
        }
    })
    .with_shrink(|c: &Collide, visit: &mut dyn FnMut(Collide) -> ControlFlow<()>| {
        shrink_case(&c.case, &mut |case| visit(Collide { case, ..c.clone() }))
    })
    .boxed()
}

/// An id collision, simulated faithfully: the responder only ever sees ids, so an initiator id `id(X)` replaced in
/// flight by `id(Z)` of a responder item `Z` in the same range is exactly what the responder sees when
/// `id(X) == id(Z)`. The session documentation: "A disagreement (an id collision) restarts the session from the root
/// with items in place of ids, which cannot collide; a second disagreement is [`Error::Mismatch`]. So a finished
/// session is exact". `docs/proofs/properties.md`: "the exact pass is exact and passes the check".
#[ephyra::test(gen = collisions(), tests = 300)]
fn an_id_collision_is_resolved_by_the_exact_pass(c: Collide) {
    let (a, b) = (c.case.a.clone(), c.case.b.clone());
    let mut done = false;
    let mut what = String::new();
    let mut collide = |dir: Dir, i: usize, m: &mut Vec<u8>| {
        if done || dir != Dir::Up {
            return;
        }
        let Some((lo, hi, off, n)) = first_ids_part(m, i == 0) else { return };
        if n == 0 {
            return;
        }
        let in_range = |x: &&Item| **x >= lo && hi.as_ref().is_none_or(|h| *x < h);
        let mine: Vec<&Item> = a.iter().filter(in_range).collect();
        assert_eq!(mine.len(), n, "an ids part does not list the initiator's items of its range");
        // The simulation is faithful only for an `X` the responder does not hold: a responder holding `X` would
        // compute `id(X) == id(Z)` for its own item too, which no change of the message can show it.
        let slot = (0..n).map(|k| (c.which + k) % n).find(|k| b.binary_search(mine[*k]).is_err());
        let Some(slot) = slot else { return };
        let x = mine[slot];
        let theirs: Vec<&Item> = b.iter().filter(in_range).filter(|z| *z != x).collect();
        let fresh: Vec<&&Item> = theirs.iter().filter(|z| a.binary_search(**z).is_err()).collect();
        let z = match (fresh.is_empty(), theirs.is_empty()) {
            (false, _) => *fresh[c.with % fresh.len()],
            (true, false) => theirs[c.with % theirs.len()],
            (true, true) => return,
        };
        let at = off + 8 * slot;
        m[at..at + 8].copy_from_slice(&pinc_reconcile::item_id(z));
        done = true;
        what = format!(
            "message {i}: id {} of {n} (X = {}) now reads as Z = {} (Z in A: {}, X in B: {}, Z's slot: {:?})",
            slot,
            show(x),
            show(z),
            a.binary_search(z).is_ok(),
            b.binary_search(x).is_ok(),
            mine.iter().position(|y| *y == z)
        );
    };
    let (r, _) = fresh(&c.case, &mut collide);
    ephyra::cover(done, "an id collision was simulated");
    let o = match r {
        Ok(o) => o,
        Err(e) => panic!("a session with one id collision failed: {e:?}"),
    };
    let (only_b, only_a) = sym_diff(&a, &b);
    let diag = format!("{what}; messages: {}", summarize(&o.log));
    assert_eq!(sorted(o.here.clone()), only_b, "missing_here is not B \\ A after a collision: {diag}");
    assert_eq!(sorted(o.there.clone()), only_a, "missing_there is not A \\ B after a collision: {diag}");
}

/// The part kinds of every message of a session, for a failure message.
fn summarize(log: &[(Dir, Vec<u8>)]) -> String {
    log.iter()
        .enumerate()
        .map(|(i, (dir, m))| {
            let Ok(body) = frame_body(m) else { return format!("{dir:?}:unframed") };
            let mut r = Reader::new(body);
            if i == 0 {
                let n = count(&mut r).unwrap();
                r.read_bytes(n).unwrap();
                r.read_varint().unwrap();
            }
            let (n, more) = read_parts(&mut r).unwrap();
            let mut last = Vec::new();
            let mut kinds = Vec::new();
            for _ in 0..n {
                let Ok(tag) = r.read_u8() else { break };
                if read_bound(&mut last, &mut r, usize::MAX).is_err() {
                    break;
                }
                if tag & INF == 0 && read_bound(&mut last, &mut r, usize::MAX).is_err() {
                    break;
                }
                let k = tag & !INF;
                kinds.push(["?", "fp", "ids", "full", "reply", "cold", "check", "miss"].get(usize::from(k)).copied().unwrap_or("?"));
                let ok = match k {
                    1 | 6 => r.read_bytes(32).is_ok(),
                    2 => count(&mut r).is_ok_and(|c| r.read_bytes(8 * c).is_ok()),
                    3 | 5 => {
                        read_items(&mut r);
                        true
                    },
                    4 => {
                        let c = count(&mut r).unwrap();
                        r.read_bytes(c.div_ceil(8)).unwrap();
                        read_items(&mut r);
                        true
                    },
                    _ => true,
                };
                if !ok {
                    break;
                }
            }
            format!("{}{}[{}]", if *dir == Dir::Up { "U" } else { "D" }, if more { "+" } else { "" }, kinds.join(" "))
        })
        .collect::<Vec<_>>()
        .join(" ")
}

// ---- hosts with different message limits ------------------------------------------------------------------------

/// Two hosts that chose different message limits, both at or above `min_message()` for the same item limit.
/// `Limits::max_message`: "A difference of any size is spread over as many messages as it needs, as long as the
/// limit is at least [`min_message`](Self::min_message)". The result is exact, or the side with the smaller limit
/// refuses a larger message of the other (`Error::MessageTooLarge`, documented), never a wrong answer.
#[ephyra::test(gen = (cases(), gens::frequency(vec![(3, gens::int(0usize..=64).boxed()), (2, gens::int(0usize..=20_000).boxed())])), tests = 300)]
fn hosts_with_different_message_limits_reconcile_exactly_or_refuse_the_larger_message(input: (Case, usize)) {
    let (c, extra_b) = input;
    let la = c.limits();
    let lb = Limits {
        max_message: la.min_message() + extra_b,
        ..la
    };
    let (ia, ib) = (index(&c.a), index(&c.b));
    let r = session(&mut Initiator::new(la), &mut Responder::new(lb), &ia, &ib, &mut |_, _, _| {}, None);
    // Intended: `Error::MessageTooLarge` is "A message from the peer is longer than the message limit", so the side
    // with the smaller limit refuses the other's larger messages (there is no negotiation of the limit). That is the
    // one failure allowed here, and only on that side.
    let o = match r {
        Ok(o) => o,
        Err(Fail::Resp(Error::MessageTooLarge)) if lb.max_message < la.max_message => return,
        Err(Fail::Init(Error::MessageTooLarge)) if la.max_message < lb.max_message => return,
        Err(e) => panic!("hosts with message limits {} and {} failed: {e:?}", la.max_message, lb.max_message),
    };
    let (only_b, only_a) = sym_diff(&c.a, &c.b);
    assert_eq!(sorted(o.here), only_b, "missing_here is not B \\ A across different limits");
    assert_eq!(sorted(o.there), only_a, "missing_there is not A \\ B across different limits");
}

// ---- lying and hostile peers ------------------------------------------------------------------------------------

/// One decoded part of a responder message, enough to re-encode it after a lie.
#[derive(Clone, Debug)]
struct Part {
    tag: u8,
    lo: Vec<u8>,
    hi: Vec<u8>,
    /// Everything after the bounds, except for a reply's or an items part's item list.
    head: Vec<u8>,
    items: Vec<Item>,
}

const INF: u8 = 0x80;

fn read_items(r: &mut Reader<'_>) -> Vec<Item> {
    let n = count(r).unwrap();
    (0..n)
        .map(|_| {
            let l = count(r).unwrap();
            r.read_bytes(l).unwrap().to_vec()
        })
        .collect()
}

/// Decode a message the honest responder wrote (the format of `pinc_reconcile::wire`).
fn decode_down(m: &[u8]) -> (Vec<Part>, bool) {
    let mut r = Reader::new(frame_body(m).unwrap());
    let (n, more) = read_parts(&mut r).unwrap();
    let mut last = Vec::new();
    let mut parts = Vec::new();
    for _ in 0..n {
        let tag = r.read_u8().unwrap();
        read_bound(&mut last, &mut r, usize::MAX).unwrap();
        let lo = last.clone();
        let hi = if tag & INF == 0 {
            read_bound(&mut last, &mut r, usize::MAX).unwrap();
            last.clone()
        } else {
            Vec::new()
        };
        let (head, items) = match tag & !INF {
            1 => (r.read_bytes(32).unwrap().to_vec(), Vec::new()),
            3 | 5 => (Vec::new(), read_items(&mut r)),
            4 => {
                let c = count(&mut r).unwrap();
                let mut h = Vec::new();
                put_varint(&mut h, c).unwrap();
                h.extend_from_slice(r.read_bytes(c.div_ceil(8)).unwrap());
                (h, read_items(&mut r))
            },
            7 => (Vec::new(), Vec::new()),
            t => panic!("the honest responder wrote an unknown part kind {t}"),
        };
        parts.push(Part { tag, lo, hi, head, items });
    }
    assert!(r.is_empty(), "bytes after the last part");
    (parts, more)
}

fn encode_down(parts: &[Part], more: bool) -> Vec<u8> {
    let mut body = Vec::new();
    put_parts(&mut body, parts.len(), more).unwrap();
    let mut last = Vec::new();
    for p in parts {
        body.push(p.tag);
        put_bound(&mut body, &mut last, &p.lo).unwrap();
        if p.tag & INF == 0 {
            put_bound(&mut body, &mut last, &p.hi).unwrap();
        }
        body.extend_from_slice(&p.head);
        if matches!(p.tag & !INF, 3..=5) {
            put_varint(&mut body, p.items.len()).unwrap();
            for it in &p.items {
                put_varint(&mut body, it.len()).unwrap();
                body.extend_from_slice(it);
            }
        }
    }
    let n = body.len();
    let mut m = vec![(n >> 16) as u8, (n >> 8) as u8, n as u8];
    m.extend_from_slice(&body);
    m
}

/// A responder that answers from its set but lies inside well-formed messages: it adds items the initiator holds to
/// the extras of its replies and to its item leaves, repeats an item it sends, and never reports a failed check.
#[derive(Clone, Debug)]
struct Liar {
    case: Case,
    /// Which lie, by kind: 0 an item of A into a reply's extras, 1 an item of A into an item leaf or cold chunk,
    /// 2 an item sent twice.
    lie: u8,
    /// Which item of A (modulo its length) is planted.
    pick: usize,
    /// Drop every miss part, so a failed final check is never reported.
    hide_miss: bool,
}

fn liars() -> ephyra::BoxGen<Liar> {
    (|g: &mut Source| {
        let (a, b) = draw_pair(g);
        let (slack, extra) = draw_limits(g);
        Liar {
            case: Case { a, b, slack, extra },
            lie: g.int(0u8..=2),
            pick: g.int(0usize..=10_000),
            hide_miss: g.bool_with(0.8),
        }
    })
    .with_shrink(|l: &Liar, visit: &mut dyn FnMut(Liar) -> ControlFlow<()>| {
        shrink_case(&l.case, &mut |case| visit(Liar { case, ..l.clone() }))?;
        if l.pick > 0 {
            visit(Liar { pick: 0, ..l.clone() })?;
        }
        ControlFlow::Continue(())
    })
    .boxed()
}

/// A finished report is consistent with some set the peer could hold: what it says the initiator lacks is not in the
/// initiator's set, what it says the peer lacks is, and no item is listed twice.
fn assert_consistent(o: &Outcome, a: &[Item]) {
    for x in &o.here {
        assert!(a.binary_search(x).is_err(), "missing_here lists an item the initiator holds: {x:?}");
    }
    for x in &o.there {
        assert!(a.binary_search(x).is_ok(), "missing_there lists an item the initiator does not hold: {x:?}");
    }
    let here: BTreeSet<&Item> = o.here.iter().collect();
    assert_eq!(here.len(), o.here.len(), "missing_here lists an item twice");
    let there: BTreeSet<&Item> = o.there.iter().collect();
    assert_eq!(there.len(), o.there.len(), "missing_there lists an item twice");
}

#[ephyra::test(gen = liars(), tests = 300)]
fn a_lying_responder_never_gets_a_self_contradicting_report_accepted(l: Liar) {
    let a = l.case.a.clone();
    let max_item = l.case.limits().max_item;
    let mut lie = |dir: Dir, _: usize, m: &mut Vec<u8>| {
        if dir != Dir::Down {
            return;
        }
        let (mut parts, more) = decode_down(m);
        if l.hide_miss {
            parts.retain(|p| p.tag & !INF != 7);
        }
        let plant = (!a.is_empty()).then(|| a[l.pick % a.len()].clone()).filter(|x| x.len() <= max_item);
        for p in &mut parts {
            let kind = p.tag & !INF;
            match (l.lie, kind) {
                (0, 4) | (1, 3 | 5) => {
                    if let Some(x) = &plant {
                        p.items.push(x.clone());
                        if kind != 4 {
                            // Item lists are ascending; a reply's extras are not ordered.
                            p.items.sort_unstable();
                            p.items.dedup();
                        }
                    }
                },
                (2, 4) => {
                    if let Some(x) = p.items.first().cloned() {
                        p.items.push(x);
                    }
                },
                _ => {},
            }
        }
        *m = encode_down(&parts, more);
    };
    let (r, _) = fresh(&l.case, &mut lie);
    if let Ok(o) = r {
        assert_consistent(&o, &a);
    }
}

/// A session whose messages in one direction are mangled once: no handler panics, every message a handler writes
/// is a frame within the frame cap, and a session that still finishes has a consistent report.
#[ephyra::test(gen = (cases(), gens::int(0usize..=40), gens::bool(), gens::int(0u64..=u64::MAX)), tests = 400)]
fn a_mangled_message_never_panics_and_never_gets_a_contradiction_accepted(input: (Case, usize, bool, u64)) {
    let (c, at, down, seed) = input;
    let lim = c.limits();
    let frame_cap = lim.max_message.min(0x00ff_ffff) + 2 * lim.max_item + 36;
    let mut src = Source::new(seed, 8);
    let mut tamper = |dir: Dir, i: usize, m: &mut Vec<u8>| {
        if let Ok(body) = frame_body(m) {
            assert!(body.len() <= frame_cap, "{dir:?} message body {} past the frame cap", body.len());
        }
        if i == at && (dir == Dir::Down) == down {
            *m = pinc_pbt::mangle(&mut src, m);
        }
    };
    let (r, _) = fresh(&c, &mut tamper);
    if let Ok(o) = r {
        assert_consistent(&o, &c.a);
    }
}

// ---- generators -------------------------------------------------------------------------------------------------

#[test]
fn the_case_generator_builds_sorted_sets_and_shrinks_within_them() {
    check_generator(&Config::default().tests(200), cases(), case_ok).assert_passed();
    check_shrinker(&Config::default().tests(100), cases(), case_ok, case_size).assert_passed();
}
