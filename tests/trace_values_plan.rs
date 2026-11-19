//! Trace generation for the response geometry and the value server: seeded random runs of the real `Plan`,
//! `ValueSource::read_at`, `proof_k` and `Server` proof frames, recorded as ndjson (`values_plan.ndjson`, and
//! `values_plan_small.ndjson` with the runs whose numbers fit TLC's 32-bit integers) for the TLA+ trace check
//! (`TraceValuesPlan.tla`) and the Lean replay (`Pinc/TraceValuesPlan.lean`).
//!
//! What is checked here against `pinc-dag`, with no proof tool involved: the reference response of a request is built
//! from `RangeEncoder` steps (header, the pairs the previous group leaves open, the group) and its range
//! encodings equal `encode_range`; `Plan::new` gives that total (or the right refusal), every frame of `Plan` is the
//! reference frame at the reference offset, `locate` finds the frame of every offset and inverts `frame`,
//! `frame_of_group` and `proof_pair` agree, and `ValueSource::read_at` returns exactly the reference bytes for every
//! offset and length asked (fresh sources, retransmissions, short reads, windows refilled), reading the store only as the
//! model predicts. The server's proof frames are cut at block boundaries, at most 1100 proof bytes, and their proof
//! length is `range_pairs` of their group range.
//!
//! What is recorded is what an observer sees. A plan event holds the value length, the spans and what `Plan` answered:
//! the refusal or the ranges, the total, a sample of frames, locates, `frame_of_group` and `proof_pair` answers. A read
//! event holds the offset, the length asked, the length returned and the reads of the store (outboard `o` or value `v`,
//! offset, length asked, length returned) in order. A server run is the events fed to the server (a loss, a send, a
//! proof request) and the proof frames it sent, as `(start, length, proof bytes, body bytes)`.
//! A slot run is the request slots of a `Server` (`vslotnew`, then `vslot` events): a stream opened, a request answered
//! (served over the rounded ranges of its plan, or refused), a stream finished or reset, a session closed. Each event
//! holds the whole table before and after (a free slot `[]`, a request being collected `[stream, peer]`, a response
//! `[stream, peer, root, ranges]`) and the resets the server sent, so the checks need no state of their own.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::type_complexity,
    clippy::doc_markdown,
    clippy::unreadable_literal,
    clippy::cast_lossless,
    unreachable_pub
)]

mod values_support;

use std::cell::RefCell;
use std::rc::Rc;

use pinc_dag::tree::{Layout, PARENT_LEN, RangeEncoder, Step, encode_range};
use pinc_tests::SplitMix64;
use pinc_transport::frame::ext;
use pinc_transport::stream::StreamSource;
use pinc_values::knobs::{GROUP, GROUP_LOG, WT_LEAD, WT_MAXF, WT_PMAX};
use pinc_values::plan::{Frame, Plan, PlanError, range_pairs};
use pinc_values::server::{Server, ServerIn, proof_k};
use pinc_values::session::Provider;
use pinc_values::source::ValueSource;
use pinc_values::span::Span;
use pinc_values::store::ValueRead;
use pinc_values::wire::{GROUP_HDR, GroupHeader, PROOF_BODY_MAX, ProofFrame, ProofReq, Req};
use values_support::*;

/// TLC integers are 32 bits: a run is "small" when every number of it is under this.
const SMALL: u64 = 1 << 26;

#[derive(Default)]
struct Sink {
    all: String,
    small: String,
    reads: usize,
    plans: usize,
}

impl Sink {
    fn line(&mut self, line: &str, nums: &[u64]) {
        self.all.push_str(line);
        self.all.push('\n');
        if nums.iter().all(|&n| n < SMALL) {
            self.small.push_str(line);
            self.small.push('\n');
        }
    }

    /// A plan event: the TLC trace takes one in three (a plan event costs TLC the most); Lean replays all.
    fn plan(&mut self, line: &str, nums: &[u64]) {
        self.plans += 1;
        if self.plans.is_multiple_of(3) {
            self.line(line, nums);
        } else {
            self.all.push_str(line);
            self.all.push('\n');
        }
    }

    /// A read event: the TLC trace takes one short read in three (a read costs TLC more than any other event); Lean
    /// replays all.
    fn read(&mut self, line: &str, nums: &[u64], n: usize) {
        if n <= 50_000 {
            self.reads += 1;
        }
        if n <= 50_000 && self.reads.is_multiple_of(3) {
            self.line(line, nums);
        } else {
            self.all.push_str(line);
            self.all.push('\n');
        }
    }
}

fn arr(items: impl Iterator<Item = String>) -> String {
    format!("[{}]", items.collect::<Vec<_>>().join(","))
}

// ---------------------------------------------------------------------------------------------------------------
// The reference response, from the encoder of pinc-dag
// ---------------------------------------------------------------------------------------------------------------

/// A frame of the reference: the outboard offsets of the pairs it opens, the group offset and length.
struct RefFrame {
    pend: Vec<u64>,
    off: u64,
    len: u32,
    follows: bool,
}

/// The framed encoding of the groups `[first, last)` of `value`, built from `RangeEncoder` steps alone; also checks it
/// holds the bytes of `encode_range` once the headers are taken out.
fn reference_range(value: &[u8], outboard: &[u8], first: u64, last: u64) -> (Vec<u8>, Vec<RefFrame>) {
    let len = value.len() as u64;
    let layout = Layout::new(len, GROUP_LOG).unwrap();
    let range = first * GROUP..(last * GROUP).min(len);
    let mut framed = Vec::new();
    let mut frames = Vec::new();
    let mut pend: Vec<u64> = Vec::new();
    let mut stripped = Vec::new();
    for step in RangeEncoder::new(layout, &range).unwrap() {
        match step.unwrap() {
            Step::Parent { outboard_offset } => pend.push(outboard_offset),
            Step::Group { offset, len: l } => {
                let follows = !frames.is_empty();
                let hdr = GroupHeader {
                    off: offset,
                    len: l as u32,
                    plen: (pend.len() * PARENT_LEN) as u16,
                    follows,
                }
                .encode();
                framed.extend_from_slice(&hdr);
                for &o in &pend {
                    let pair = &outboard[o as usize..o as usize + PARENT_LEN];
                    framed.extend_from_slice(pair);
                    stripped.extend_from_slice(pair);
                }
                let g = &value[offset as usize..(offset + l) as usize];
                framed.extend_from_slice(g);
                stripped.extend_from_slice(g);
                frames.push(RefFrame {
                    pend: std::mem::take(&mut pend),
                    off: offset,
                    len: l as u32,
                    follows,
                });
            }
        }
    }
    assert!(pend.is_empty(), "the encoding ends on a group");
    let mut enc = vec![0u8; stripped.len()];
    let n = encode_range(value, outboard, GROUP_LOG, &range, &mut enc).unwrap();
    assert_eq!(
        &enc[..n],
        stripped.as_slice(),
        "the reference is encode_range with headers"
    );
    (framed, frames)
}

/// The groups `[first, last)` a span rounds out to, if it is not empty and inside the value.
fn rounded(len: u64, s: &Span) -> Option<(u64, u64)> {
    (s.len > 0 && u128::from(s.off) + u128::from(s.len) <= u128::from(len)).then(|| {
        let end = s.off + s.len;
        (s.off / GROUP, end.div_ceil(GROUP))
    })
}

// ---------------------------------------------------------------------------------------------------------------
// A store that logs its reads
// ---------------------------------------------------------------------------------------------------------------

type Log = Rc<RefCell<Vec<(u8, u64, usize, usize)>>>;

#[derive(Clone)]
struct LogStore {
    inner: PStore,
    log: Log,
}

impl ValueRead for LogStore {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        self.inner.servable_len(root)
    }
    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let n = self.inner.read_at(root, offset, dst);
        self.log.borrow_mut().push((b'v', offset, dst.len(), n));
        n
    }
    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let n = self.inner.read_outboard(root, offset, dst);
        self.log.borrow_mut().push((b'o', offset, dst.len(), n));
        n
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Plan runs
// ---------------------------------------------------------------------------------------------------------------

fn span_json(spans: &[Span]) -> String {
    arr(spans.iter().map(|s| format!("[{},{}]", s.off, s.len)))
}

fn frame_json(f: &Frame) -> String {
    format!(
        "[{},{},{},{},{},{},{}]",
        f.range,
        f.k,
        f.start,
        f.off,
        f.dlen,
        f.plen,
        u8::from(f.follows)
    )
}

fn err_code(e: PlanError) -> u8 {
    match e {
        PlanError::OutOfBounds => 1,
        PlanError::TooManyRanges => 2,
        PlanError::TooLong => 3,
    }
}

/// The expected refusal, from the spans alone (independent of `Plan`): too many, past the value, or over 2^62 - 1 with
/// the sizes of the encoder (`size` gives the framed bytes of the groups `[first, last)`).
fn expected(len: u64, spans: &[Span], size: impl Fn(u64, u64) -> u128) -> Result<u128, PlanError> {
    if spans.len() > 255 {
        return Err(PlanError::TooManyRanges);
    }
    let mut total = 0u128;
    for s in spans.iter().filter(|s| s.len > 0) {
        let (first, last) = rounded(len, s).ok_or(PlanError::OutOfBounds)?;
        total += size(first, last);
        if total > (1u128 << 62) - 1 {
            return Err(PlanError::TooLong);
        }
    }
    Ok(total)
}

/// One plan run over a real value: `Plan` against the reference, then reads through a `ValueSource`.
fn plan_run(sink: &mut Sink, rng: &mut SplitMix64, store: &PStore, spans: &[Span]) {
    let len = store.len();
    let value = store.content().bytes(0, len);
    let outboard = &store.0.outboard;
    let refs: Vec<(Vec<u8>, Vec<RefFrame>)> = spans
        .iter()
        .filter_map(|s| rounded(len, s))
        .map(|(a, b)| reference_range(&value, outboard, a, b))
        .collect();
    let want = expected(len, spans, |a, b| {
        reference_range(&value, outboard, a, b).0.len() as u128
    });
    let plan = Plan::new(len, spans);
    let sj = span_json(spans);
    match (&plan, &want) {
        (Err(e), Err(w)) => {
            assert_eq!(e, w);
            let line = format!(r#"{{"t":"vplan","len":{len},"spans":{sj},"err":{}}}"#, err_code(*e));
            let mut nums = vec![len];
            nums.extend(spans.iter().flat_map(|s| [s.off, s.len]));
            sink.plan(&line, &nums);
            return;
        }
        (Ok(p), Ok(w)) => assert_eq!(u128::from(p.total()), *w, "total is the sum of the reference ranges"),
        (p, w) => panic!("plan {p:?} against the reference {w:?}"),
    }
    let plan = plan.unwrap();
    let reference: Vec<u8> = refs.iter().flat_map(|r| r.0.iter().copied()).collect();
    assert_eq!(plan.total(), reference.len() as u64);
    assert_eq!(plan.ranges(), refs.len());

    // Every frame is the reference frame at the reference offset (all of a small plan, a sample of a large one).
    let mut frames = Vec::new();
    let mut nums = vec![len, plan.total()];
    nums.extend(spans.iter().flat_map(|s| [s.off, s.len]));
    let mut base = 0u64;
    let mut sampled: Vec<Frame> = Vec::new();
    for (i, (bytes, rf)) in refs.iter().enumerate() {
        assert_eq!(plan.range_groups(i), Some(rf.len() as u64));
        let sp = plan.range_span(i).unwrap();
        assert_eq!(sp.off, rf[0].off, "the range starts at its first group");
        assert_eq!(
            sp.end(),
            rf[rf.len() - 1].off + u64::from(rf[rf.len() - 1].len),
            "and ends at its last"
        );
        let m = rf.len();
        let picks: Vec<usize> = if m <= 12 {
            (0..m).collect()
        } else {
            let mut v = vec![0, 1, m - 2, m - 1];
            v.extend((0..3).map(|_| (rng.next_u64() % m as u64) as usize));
            v.sort_unstable();
            v.dedup();
            v
        };
        let mut at = base;
        let mut starts = Vec::with_capacity(m);
        for r in rf {
            starts.push(at);
            at += (GROUP_HDR + r.pend.len() * PARENT_LEN) as u64 + u64::from(r.len);
        }
        assert_eq!(at, base + bytes.len() as u64);
        for k in picks {
            let f = plan.frame(i, k as u64).unwrap();
            let r = &rf[k];
            assert_eq!((f.range, f.k), (i, k as u64));
            assert_eq!(f.start, starts[k], "frame start is the reference offset");
            assert_eq!(
                (f.off, f.dlen, u64::from(f.plen), f.follows),
                (r.off, r.len, (r.pend.len() * PARENT_LEN) as u64, r.follows)
            );
            // The header at the frame start is the header of the reference.
            let hdr = GroupHeader::parse(&reference[f.start as usize..]).unwrap();
            assert_eq!(
                (hdr.off, hdr.len, u64::from(hdr.plen), hdr.follows),
                (f.off, f.dlen, u64::from(f.plen), f.follows)
            );
            assert_eq!(
                f.end(),
                f.start + (GROUP_HDR + r.pend.len() * PARENT_LEN) as u64 + u64::from(r.len)
            );
            frames.push(frame_json(&f));
            sampled.push(f);
        }
        assert!(plan.frame(i, m as u64).is_none());
        base += bytes.len() as u64;
    }
    assert!(plan.frame(refs.len(), 0).is_none());

    // locate: every sampled frame is found from its first, middle and last byte, and offsets at and past the end are not.
    let mut loc = Vec::new();
    let mut nloc = Vec::new();
    let mut probes: Vec<u64> = Vec::new();
    for f in &sampled {
        probes.extend([f.start, f.end() - 1]);
    }
    probes.extend((0..6).map(|_| rng.next_u64() % plan.total().max(1)));
    probes.extend([0, plan.total().saturating_sub(1)]);
    for &at in &probes {
        if at >= plan.total() {
            continue;
        }
        let f = plan.locate(at).unwrap();
        assert!(f.start <= at && at < f.end());
        assert_eq!(plan.frame(f.range, f.k), Some(f), "locate returns the frame");
        loc.push(format!("[{at},{},{}]", f.range, f.k));
    }
    for &at in &[plan.total(), plan.total() + 1, plan.total() + 1000, u64::MAX] {
        assert!(plan.locate(at).is_none());
        nloc.push(format!("{at}"));
    }
    for f in &sampled {
        assert_eq!(plan.locate(f.start), Some(*f), "locate inverts frame at the first byte");
        assert_eq!(plan.locate(f.end() - 1), Some(*f), "and at the last");
    }

    // frame_of_group: the first range that holds the group; unaligned offsets none.
    let mut fog = Vec::new();
    let mut nfog = Vec::new();
    let ngroups = len.div_ceil(GROUP);
    let mut goffs: Vec<u64> = sampled.iter().take(6).map(|f| f.off).collect();
    goffs.extend((0..4).map(|_| (rng.next_u64() % ngroups.max(1)) * GROUP));
    goffs.extend([ngroups * GROUP, ngroups * GROUP + GROUP]);
    for &off in &goffs {
        let g = off / GROUP;
        let first_range = refs.iter().position(|(_, rf)| {
            let a = rf[0].off / GROUP;
            a <= g && g < a + rf.len() as u64
        });
        match (plan.frame_of_group(off), first_range) {
            (Some(f), Some(i)) => {
                assert_eq!(f.range, i, "the first range that holds the group");
                assert_eq!(f.off, off);
                fog.push(format!("[{off},{},{}]", f.range, f.k));
            }
            (None, None) => nfog.push(format!("{off}")),
            (a, b) => panic!("frame_of_group({off}) = {a:?}, reference range {b:?}"),
        }
    }
    for off in [1u64, GROUP - 1, GROUP + 1] {
        assert!(plan.frame_of_group(off).is_none());
        nfog.push(format!("{off}"));
    }

    // proof_pair: the j-th pair of a frame is the j-th pair the encoder opened there.
    let mut pp = Vec::new();
    let mut npp = Vec::new();
    for f in sampled.iter().take(8) {
        let r = &refs[f.range].1[f.k as usize];
        for j in 0..=r.pend.len() as u64 {
            match (plan.proof_pair(f, j), r.pend.get(j as usize)) {
                (Some(o), Some(&w)) => {
                    assert_eq!(o, w);
                    pp.push(format!("[{},{},{j},{o}]", f.range, f.k));
                }
                (None, None) => npp.push(format!("[{},{},{j}]", f.range, f.k)),
                (a, b) => panic!("proof_pair {a:?} against {b:?}"),
            }
        }
    }
    let ranges = arr((0..plan.ranges()).map(|i| {
        let f = plan.frame(i, 0).unwrap();
        let sp = plan.range_span(i).unwrap();
        format!(
            "[{},{},{}]",
            sp.off / GROUP,
            plan.range_groups(i).unwrap() + sp.off / GROUP,
            f.start
        )
    }));
    let line = format!(
        r#"{{"t":"vplan","len":{len},"spans":{sj},"total":{},"ranges":{ranges},"frames":{},"loc":{},"nloc":{},"fog":{},"nfog":{},"pp":{},"npp":{}}}"#,
        plan.total(),
        arr(frames.into_iter()),
        arr(loc.into_iter()),
        arr(nloc.into_iter()),
        arr(fog.into_iter()),
        arr(nfog.into_iter()),
        arr(pp.into_iter()),
        arr(npp.into_iter()),
    );
    sink.plan(&line, &nums);

    // read_at: exactly the reference bytes, for any offset and length; a fresh source and a long-lived one agree.
    let log: Log = Rc::default();
    let ls = LogStore {
        inner: store.clone(),
        log: Rc::clone(&log),
    };
    let root = store.root();
    let mut live = ValueSource::new(ls.clone(), root, plan.clone());
    let total = plan.total();
    let mut asks: Vec<(u64, usize)> = vec![
        (0, total as usize),
        (0, 1),
        (total.saturating_sub(1), 5),
        (total, 8),
        (total + 10, 8),
    ];
    for f in sampled.iter().take(12) {
        asks.push((f.start, 16));
        asks.push((f.start + 3, 40));
        asks.push((f.proof_start(), 64 * 3));
        asks.push((f.data_start(), 100));
        asks.push((f.end().saturating_sub(7), 30));
        asks.push((f.start.saturating_sub(5), (f.end() - f.start) as usize + 11));
    }
    for _ in 0..12 {
        let off = rng.next_u64() % (total + 5);
        let n = (rng.next_u64() % (3 * u64::from(GROUP as u32) + 70)) as usize;
        asks.push((off, n));
    }
    for (off, n) in asks {
        let n = n.min(1 << 20);
        let upto = reference
            .len()
            .min(usize::try_from(off).unwrap_or(usize::MAX).saturating_add(n));
        let expect = reference.get(off as usize..upto).unwrap_or_default();
        log.borrow_mut().clear();
        let mut fresh = ValueSource::new(ls.clone(), root, plan.clone());
        let mut got = vec![0u8; n];
        let r = fresh.read_at(off, &mut got);
        assert_eq!(&got[..r], expect, "read_at({off}, {n}) is the reference");
        assert_eq!(r, expect.len(), "short only at the end of the response");
        let acc = log.borrow().clone();
        // the same bytes from a long-lived source (window kept), and again (a retransmission)
        for _ in 0..2 {
            let mut again = vec![0u8; n];
            let r2 = live.read_at(off, &mut again);
            assert_eq!(&again[..r2], expect, "retransmission and window");
        }
        let line = format!(
            r#"{{"t":"vread","len":{len},"spans":{sj},"off":{off},"n":{n},"ret":{r},"acc":{}}}"#,
            arr(acc
                .iter()
                .map(|(k, o, q, g)| format!("[{},{o},{q},{g}]", u8::from(*k == b'v'))))
        );
        let mut nums = vec![len, off, n as u64, total];
        nums.extend(spans.iter().flat_map(|s| [s.off, s.len]));
        sink.read(&line, &nums, n);
    }
}

fn random_spans(rng: &mut SplitMix64, len: u64) -> Vec<Span> {
    let count = match rng.next_u64() % 8 {
        0 => 0,
        1..=4 => 1,
        5 => 2,
        6 => 3,
        _ => 1 + (rng.next_u64() % 5) as usize,
    };
    (0..count)
        .map(|_| match rng.next_u64() % 10 {
            0 => Span {
                off: rng.next_u64() % (len + 1),
                len: 0,
            },
            1 => Span { off: 0, len },
            2 => Span {
                off: len.saturating_sub(1),
                len: 1,
            },
            3 => {
                let off = (rng.next_u64() % len.max(1)) / GROUP * GROUP;
                Span {
                    off,
                    len: (len - off).min(GROUP),
                }
            }
            _ => {
                let off = rng.next_u64() % len.max(1);
                Span {
                    off,
                    len: 1 + rng.next_u64() % (len - off).max(1),
                }
            }
        })
        .collect()
}

// ---------------------------------------------------------------------------------------------------------------
// Plans of values too large to hold: the refusals and the boundary of 2^62 - 1
// ---------------------------------------------------------------------------------------------------------------

/// The framed bytes of the full value: header per group, a pair per parent, the value (a closed form of the encoder:
/// `encoded_len` walks every group, which a value this large cannot afford).
fn full_size(len: u64) -> u128 {
    let g = u128::from(len.div_ceil(GROUP));
    u128::from(len) + 64 * (g - 1) + 16 * g
}

fn big_plans(sink: &mut Sink, rng: &mut SplitMix64) {
    let mut lens: Vec<u64> = vec![
        1,
        GROUP,
        GROUP + 1,
        1 << 30,
        (1 << 30) + 1,
        1 << 40,
        (1 << 50) + 12345,
        1 << 55,
        1 << 60,
    ];
    // the largest value whose whole framed response still fits 2^62 - 1, found with the closed form, and its neighbours
    let (mut lo, mut hi) = (1u64, u64::MAX);
    while lo < hi {
        let mid = lo + (hi - lo).div_ceil(2);
        if full_size(mid) < (1u128 << 62) {
            lo = mid;
        } else {
            hi = mid - 1;
        }
    }
    lens.extend([lo - 1, lo, lo + 1, lo + GROUP, u64::MAX - 1, u64::MAX]);
    lens.extend((0..10).map(|_| 1 + rng.next_u64() % (u64::MAX / 2) + rng.next_u64() % (u64::MAX / 2)));
    for len in lens {
        let ng = len.div_ceil(GROUP);
        let mut cases: Vec<Vec<Span>> = vec![
            vec![Span { off: 0, len }],
            vec![Span { off: 0, len: 1 }],
            vec![Span { off: len - 1, len: 1 }],
            vec![
                Span {
                    off: 0,
                    len: len / 2 + 1,
                },
                Span {
                    off: len / 3,
                    len: len - len / 3,
                },
            ],
            vec![Span { off: 1, len }],
            vec![Span { off: u64::MAX, len: 2 }],
            vec![Span { off: 5, len: u64::MAX }],
            vec![
                Span { off: 0, len: 0 },
                Span {
                    off: len / 2,
                    len: len - len / 2,
                },
            ],
            vec![Span { off: 0, len: 1 }; 256],
            vec![Span { off: 0, len: 1 }; 33],
        ];
        cases.push(vec![Span {
            off: (ng / 2) * GROUP,
            len: 1,
        }]);
        for spans in cases {
            let sj = span_json(&spans);
            let plan = Plan::new(len, &spans);
            // the independent expectation: the closed form for full-value ranges, none needed to decide the refusals
            let layout = Layout::new(len, GROUP_LOG).unwrap();
            let want = expected(len, &spans, |a, b| {
                let data = (u128::from(b) * u128::from(GROUP)).min(u128::from(len)) - u128::from(a) * u128::from(GROUP);
                let parents = range_pairs(layout.groups(), a, b);
                u128::from(b - a) * 16 + data + 64 * u128::from(parents)
            });
            let want_full = spans.len() == 1 && spans[0].off == 0 && spans[0].len == len;
            match (&plan, &want) {
                (Err(e), Err(w)) => assert_eq!(e, w, "{len} {sj}"),
                (Ok(p), Ok(w)) => {
                    assert_eq!(u128::from(p.total()), *w, "{len} {sj}");
                    assert!(p.total() < 1 << 62);
                    if want_full {
                        assert_eq!(*w, full_size(len), "closed form of the whole value");
                    }
                }
                (p, w) => panic!("{len} {sj}: plan {p:?} against {w:?}"),
            }
            if want_full {
                assert_eq!(plan.is_ok(), full_size(len) < (1 << 62), "the 2^62 - 1 limit for {len}");
            }
            let mut nums = vec![len];
            nums.extend(spans.iter().flat_map(|s| [s.off, s.len]));
            match plan {
                Err(e) => {
                    let line = format!(r#"{{"t":"vplan","len":{len},"spans":{sj},"err":{}}}"#, err_code(e));
                    sink.plan(&line, &nums);
                }
                Ok(p) => {
                    // frames of the first and last range: first, second, last, and the located ones
                    let mut frames = Vec::new();
                    let mut loc = Vec::new();
                    for i in 0..p.ranges() {
                        let m = p.range_groups(i).unwrap();
                        for k in [0, 1, m / 2, m.saturating_sub(2), m - 1] {
                            if let Some(f) = p.frame(i, k) {
                                assert!(f.end() <= p.total());
                                assert_eq!(p.locate(f.start), Some(f));
                                assert_eq!(p.locate(f.end() - 1), Some(f));
                                loc.push(format!("[{},{},{}]", f.start, f.range, f.k));
                                loc.push(format!("[{},{},{}]", f.end() - 1, f.range, f.k));
                                frames.push(frame_json(&f));
                            }
                        }
                    }
                    let ranges = arr((0..p.ranges()).map(|i| {
                        let sp = p.range_span(i).unwrap();
                        format!(
                            "[{},{},{}]",
                            sp.off / GROUP,
                            sp.off / GROUP + p.range_groups(i).unwrap(),
                            p.frame(i, 0).unwrap().start
                        )
                    }));
                    let line = format!(
                        r#"{{"t":"vplan","len":{len},"spans":{sj},"total":{},"ranges":{ranges},"frames":{},"loc":{},"nloc":[{}],"fog":[],"nfog":[],"pp":[],"npp":[]}}"#,
                        p.total(),
                        arr(frames.into_iter()),
                        arr(loc.into_iter()),
                        p.total()
                    );
                    sink.plan(&line, &nums);
                    assert!(p.locate(p.total()).is_none());
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// The server
// ---------------------------------------------------------------------------------------------------------------

struct Rig {
    server: Server<PStore, 4>,
    sess: ServerSession,
    rec: Rec,
    seen: usize,
}

impl Rig {
    fn new(store: &PStore, spans: &[Span]) -> Self {
        let mut r = Self {
            server: Server::new(store.clone()),
            sess: ServerSession::default(),
            rec: Rec::default(),
            seen: 0,
        };
        let mut b = [0u8; 600];
        let n = Req::encode(&store.root(), spans, &mut b).unwrap();
        r.sess.reqs.insert(1, b[..n].to_vec());
        r.server.on_event(
            &mut r.sess,
            &mut r.rec,
            0,
            &ServerIn::Opened {
                stream: 1,
                peer: Provider(7),
            },
        );
        r.server.on_event(&mut r.sess, &mut r.rec, 0, &ServerIn::Readable(1));
        r
    }

    /// Feed an event and return the proof frames it made the server send: (start, length, proof bytes, body bytes).
    fn feed(&mut self, ev: &ServerIn<'_>) -> Vec<(u64, u32, usize, usize)> {
        self.server.on_event(&mut self.sess, &mut self.rec, 0, ev);
        let mut out = Vec::new();
        for m in &self.sess.out[self.seen..] {
            if let ToClient::Ext(1, ty, body) = m {
                assert_eq!(*ty, ext::PROOF);
                let pf = ProofFrame::parse(body).unwrap();
                out.push((pf.start, pf.wn, pf.proof.len(), body.len()));
            }
        }
        self.seen = self.sess.out.len();
        out
    }
}

fn server_run(sink: &mut Sink, rng: &mut SplitMix64, store: &PStore, spans: &[Span], steps: usize, wild: bool) {
    let ln = store.len();
    let plan = Plan::new(ln, spans).unwrap();
    let mut rig = Rig::new(store, spans);
    let layout = Layout::new(ln, GROUP_LOG).unwrap();
    let sj = span_json(spans);
    let mut lines = vec![format!(r#"{{"t":"vsrvnew","ln":{ln},"spans":{sj}}}"#)];
    let mut nums = vec![ln, plan.total()];
    nums.extend(spans.iter().flat_map(|s| [s.off, s.len]));
    let mut max_end = 0u64;
    for _ in 0..steps {
        let total = plan.total().max(1);
        let window = match rng.next_u64() % 6 {
            0 => 0,
            1 => 1 + rng.next_u64() % 2000,
            2..=3 => 20_000 + rng.next_u64() % 400_000,
            4 => WT_LEAD * 2 + rng.next_u64() % 3_000_000,
            _ => {
                if wild {
                    u64::MAX / 2 + rng.next_u64() % (u64::MAX / 2)
                } else {
                    rng.next_u64() % 5_000_000
                }
            }
        };
        let (kind, a, b, frames) = match rng.next_u64() % 5 {
            0 => {
                let (off, sent) = (rng.next_u64() % total, rng.next_u64() % (total + 1000));
                (
                    b'l',
                    off,
                    sent,
                    rig.feed(&ServerIn::Loss {
                        stream: 1,
                        offset: off,
                        sent,
                        window,
                    }),
                )
            }
            1 | 2 => {
                let sent = rng.next_u64() % (total + 1000);
                (
                    b's',
                    sent,
                    0,
                    rig.feed(&ServerIn::Sent {
                        stream: 1,
                        sent,
                        window,
                    }),
                )
            }
            _ => {
                let from = match rng.next_u64() % 4 {
                    0 => 0,
                    1 if wild => u64::MAX - rng.next_u64() % 100,
                    _ => rng.next_u64() % (ln + GROUP),
                };
                let upto = match rng.next_u64() % 5 {
                    0 => 0,
                    1 if wild => u64::MAX - rng.next_u64() % 40_000,
                    _ => rng.next_u64() % (ln + 3 * GROUP),
                };
                let mut body = [0u8; 32];
                let n = ProofReq { sid: 1, from, upto }.encode(&mut body).unwrap();
                (
                    b'x',
                    from,
                    upto,
                    rig.feed(&ServerIn::Ext {
                        ty: ext::PROOF_REQ,
                        body: &body[..n],
                    }),
                )
            }
        };
        // the invariants of every frame, against the encoder
        let k = proof_k(ln);
        for &(start, wn, plen, blen) in &frames {
            let k = k.expect("a deep value sends no proof frame");
            let block = k * GROUP;
            assert!(
                start.is_multiple_of(GROUP) && wn > 0 && u64::from(wn) <= block,
                "frame {start}+{wn}"
            );
            assert_eq!(
                start / block,
                (start + u64::from(wn) - 1) / block,
                "a frame lies in one block of {k} groups"
            );
            assert!(start + u64::from(wn) <= ln);
            assert!(plen <= WT_PMAX, "proof of {plen} bytes");
            assert!(blen <= PROOF_BODY_MAX);
            assert_eq!(
                plen as u64,
                range_pairs(layout.groups(), start / GROUP, (start + u64::from(wn)).div_ceil(GROUP))
                    * PARENT_LEN as u64,
                "the proof has range_pairs pairs"
            );
            max_end = max_end.max(start + u64::from(wn));
        }
        assert!(frames.len() <= WT_MAXF);
        let kc = match kind {
            b'l' => "loss",
            b's' => "sent",
            _ => "ext",
        };
        let fr = arr(frames.iter().map(|(s, w, p, bl)| format!("[{s},{w},{p},{bl}]")));
        lines.push(format!(
            r#"{{"t":"vsrv","ev":"{kc}","a":{a},"b":{b},"w":{window},"fr":{fr}}}"#
        ));
        nums.extend([a, b, window]);
        nums.extend(frames.iter().flat_map(|f| [f.0, u64::from(f.1)]));
    }
    for l in lines {
        sink.line(&l, &nums);
    }
}

#[test]
fn plan_source_and_server_agree_with_the_encoder_and_are_traced() {
    let mut rng = SplitMix64::traced(0x9_1A);
    let mut sink = Sink::default();

    // Plans and reads over real values: lengths around group and tree-shape boundaries.
    let g = GROUP as usize;
    let lens = [
        1,
        2,
        g - 1,
        g,
        g + 1,
        2 * g,
        3 * g - 1,
        3 * g,
        4 * g + 5,
        5 * g,
        7 * g + 3,
        8 * g,
        9 * g,
        16 * g - 7,
        17 * g,
        31 * g + 1,
        33 * g,
        64 * g,
        65 * g + 100,
        100 * g + 1,
    ];
    for (n, &l) in lens.iter().enumerate() {
        let store = PStore::random(100 + n as u64, l);
        for round in 0..6 {
            let spans = if round == 0 {
                vec![Span { off: 0, len: l as u64 }]
            } else {
                random_spans(&mut rng, l as u64)
            };
            plan_run(&mut sink, &mut rng, &store, &spans);
        }
    }
    // some refused plans over a real value
    let store = PStore::random(7, 5 * g + 9);
    for spans in [
        vec![Span {
            off: 0,
            len: 5 * g as u64 + 10,
        }],
        vec![Span { off: u64::MAX, len: 2 }],
        vec![Span { off: 3, len: u64::MAX }],
        vec![Span { off: 0, len: 1 }; 256],
        vec![Span { off: 0, len: 1 }; 33],
    ] {
        plan_run(&mut sink, &mut rng, &store, &spans);
    }
    big_plans(&mut sink, &mut rng);

    // proof_k: the frame size for every value size, the closed form for deep values
    for ln in [
        1u64,
        2,
        GROUP,
        GROUP + 1,
        3 * GROUP,
        17 * GROUP,
        100 * GROUP,
        1 << 20,
        1 << 26,
        1 << 29,
        (1 << 30) - 1,
        1 << 30,
        (1 << 30) + 1,
        (1 << 30) + GROUP,
        1 << 31,
        1 << 40,
        u64::MAX,
    ] {
        let k = proof_k(ln);
        assert_eq!(
            k.is_none(),
            ln > 1 << 30,
            "a value over 1 GiB gets no write-through ({ln})"
        );
        if let Some(k) = k {
            assert!([4, 8, 16].contains(&k));
        }
        sink.line(&format!(r#"{{"t":"vk","ln":{ln},"k":{}}}"#, k.unwrap_or(0)), &[ln]);
    }
    for g in 1..300u64 {
        let ln = g * GROUP - (g % 3);
        let k = proof_k(ln).unwrap();
        sink.line(&format!(r#"{{"t":"vk","ln":{ln},"k":{k}}}"#), &[ln]);
    }

    // server runs over real values, small and wild numbers; and over a deep tree
    for (n, &l) in [g + 1, 3 * g, 20 * g, 64 * g, 300 * g + 7, 2000 * g].iter().enumerate() {
        let store = PStore::random(300 + n as u64, l);
        for wild in [false, true] {
            for spans in [
                vec![Span { off: 0, len: l as u64 }],
                vec![Span {
                    off: (l as u64 / 3) / GROUP * GROUP,
                    len: l as u64 / 2,
                }],
            ] {
                server_run(&mut sink, &mut rng, &store, &spans, 40, wild);
            }
        }
    }
    let deep = PStore::pattern(0xDEE9, (1 << 30) + 3 * GROUP + 5);
    server_run(
        &mut sink,
        &mut rng,
        &deep,
        &[Span {
            off: 0,
            len: deep.len(),
        }],
        12,
        true,
    );
    server_run(
        &mut sink,
        &mut rng,
        &deep,
        &[Span {
            off: (1 << 30) / 2,
            len: 5 * GROUP,
        }],
        12,
        true,
    );

    slot_runs(&mut |line, nums| sink.line(line, nums), &mut rng);

    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("values_plan.ndjson"), &sink.all).unwrap();
    std::fs::write(dir.join("values_plan_small.ndjson"), &sink.small).unwrap();
}
