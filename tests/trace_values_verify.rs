//! Trace generation for `pinc_values::verify::GroupVerifier` next to `pinc_dag::tree::RangeVerifier`: seeded random
//! runs of both real verifiers on one stream, fed the same pieces, recorded as ndjson (`values_verify.ndjson`) for
//! the TLA+ trace check (`TraceValuesVerify.tla`) and the Lean replay (`Pinc/ValuesVerifyTrace.lean`).
//!
//! A run proves a random byte range of a random value. The stream is the genuine `encode_range` output, or that
//! stream with a flipped bit, cut short, or followed by extra bytes. Both verifiers are fed every piece of the
//! stream; the piece sizes are the whole stream, a few bytes, item-sized and random, so the whole-pair path and the
//! buffered path of `GroupVerifier` and the fast and slow paths of `RangeVerifier` all run, at every offset of an
//! item. Per call the trace records what each verifier reported (consumed bytes, the group, the error, `next_len`,
//! `next_item`, `at_boundary`, `is_complete`, `failure`) and, when the call completed a stream item, the item and
//! the hash call (the computed chaining value is the oracle, as in `trace_verifier`). The group bytes the caller of
//! `GroupVerifier` keeps are identified (`grd`) next to the bytes `RangeVerifier` returned (`rd`).
//!
//! A run in skip mode also calls `GroupVerifier::skip_group` when the verifier sits at a group: the group's bytes are
//! then left out of its stream, and `RangeVerifier` (which cannot skip) is fed the genuine bytes of that group in
//! one call in their place, so the two stay in the same position. Refused skips (in the middle of an item, at a
//! pair, after a failure, on a complete stream) are recorded too: the verifier must be left as it was.
//!
//! The test asserts everything itself (both verifiers agree on every call, and with the genuine value), so it is
//! meaningful without the proof tools. The trace is written to the directory in `PINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::struct_excessive_bools,
    clippy::similar_names
)]

use std::collections::HashMap;
use std::fmt::Write as _;
use std::ops::Range;

use blake3::Hasher;
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};
use pinc_dag::tree::{
    Cv, Layout, RangeEncoder, RangeVerifier, Step, TreeError, build_outboard_vec, encode_range, encoded_len,
};
use pinc_tests::{SplitMix64, trace_cases};
use pinc_values::verify::{GroupVerifier, Item};

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// Dense ids, from 1, for distinct 32-byte values.
#[derive(Default)]
struct Ids(HashMap<[u8; 32], u32>);

impl Ids {
    fn id(&mut self, key: [u8; 32]) -> u32 {
        let next = u32::try_from(self.0.len()).unwrap() + 1;
        *self.0.entry(key).or_insert(next)
    }
}

/// The hash call both verifiers make for a group.
fn leaf_cv(root: bool, offset: u64, data: &[u8]) -> Cv {
    let mut hasher = Hasher::new();
    if root {
        *hasher.update(data).finalize().as_bytes()
    } else {
        hasher.set_input_offset(offset).update(data);
        hasher.finalize_non_root()
    }
}

/// The hash call both verifiers make for a parent pair.
fn parent_cv(root: bool, left: &Cv, right: &Cv) -> Cv {
    if root {
        *merge_subtrees_root(left, right, Mode::Hash).as_bytes()
    } else {
        merge_subtrees_non_root(left, right, Mode::Hash)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Kind {
    Genuine,
    Flip,
    Trunc,
    Extra,
}

impl Kind {
    fn name(self) -> &'static str {
        match self {
            Kind::Genuine => "genuine",
            Kind::Flip => "flip",
            Kind::Trunc => "trunc",
            Kind::Extra => "extra",
        }
    }
}

#[derive(Clone, Copy)]
enum Pieces {
    Whole,
    Mixed,
    Tiny,
}

fn window(
    mode: Pieces,
    rng: &mut SplitMix64,
    remaining: usize,
    group: usize,
    total: usize,
    need: Option<usize>,
) -> usize {
    let w = match mode {
        Pieces::Whole => remaining,
        Pieces::Tiny => (total / 50).max(8) + below(rng, 24) as usize,
        Pieces::Mixed => match (below(rng, 5), need) {
            (0, _) => 1 + below(rng, 3) as usize,
            (1, _) => 1 + below(rng, 2 * group as u64) as usize,
            (2, _) => remaining,
            (_, Some(r)) => (r + below(rng, 3) as usize).saturating_sub(1),
            (_, None) => 1 + below(rng, 64) as usize,
        },
    };
    w.clamp(1, remaining)
}

#[derive(Default)]
struct Trace {
    out: String,
    cvs: Ids,
    data: Ids,
}

fn json_u64(v: Option<u64>) -> i64 {
    v.map_or(-1, |x| i64::try_from(x).unwrap())
}

fn error_name(e: Option<TreeError>) -> &'static str {
    match e {
        None => "none",
        Some(TreeError::ParentMismatch) => "parent",
        Some(TreeError::GroupMismatch) => "group",
        Some(TreeError::TooMuchData) => "toomuch",
        Some(other) => unreachable!("unexpected verifier error {other:?}"),
    }
}

fn step_json(step: Option<&Step>) -> String {
    match step {
        Some(Step::Parent { outboard_offset }) => format!("[\"p\",{outboard_offset}]"),
        Some(Step::Group { offset, len }) => format!("[\"g\",{offset},{len}]"),
        None => "[]".to_string(),
    }
}

fn item_json(item: Option<Item>) -> String {
    match item {
        None => "[]".to_string(),
        Some(Item::Pair) => "[\"p\"]".to_string(),
        Some(Item::Group { offset, len }) => format!("[\"g\",{offset},{len}]"),
    }
}

/// The oracle fields of an item the verifiers just completed: the hash call, its value, the item.
struct Oracle {
    key: String,
    hout: u32,
    item: String,
}

fn oracle(tr: &mut Trace, step: Option<&Step>, root_flag: bool, glen: u64, bytes: &[u8]) -> Oracle {
    match step {
        Some(Step::Parent { .. }) => {
            let (l, r): (Cv, Cv) = (bytes[..32].try_into().unwrap(), bytes[32..64].try_into().unwrap());
            let (li, ri) = (tr.cvs.id(l), tr.cvs.id(r));
            Oracle {
                hout: tr.cvs.id(parent_cv(root_flag, &l, &r)),
                key: format!("[\"P\",{root_flag},{li},{ri}]"),
                item: format!("{{\"l\":{li},\"r\":{ri},\"d\":0}}"),
            }
        }
        Some(Step::Group { offset, .. }) => {
            let di = tr.data.id(*blake3::hash(bytes).as_bytes());
            Oracle {
                hout: tr.cvs.id(leaf_cv(root_flag, *offset, bytes)),
                key: format!("[\"L\",{root_flag},{},{di}]", offset / glen),
                item: format!("{{\"l\":0,\"r\":0,\"d\":{di}}}"),
            }
        }
        None => unreachable!("a completed item beyond the genuine stream"),
    }
}

const NO_ORACLE: (&str, u32, &str) = ("[]", 0, "{\"l\":0,\"r\":0,\"d\":0}");

fn run_case<const G: usize>(
    tr: &mut Trace,
    rng: &mut SplitMix64,
    run: usize,
    value: &[u8],
    log: u32,
    range: &Range<u64>,
    kind: Kind,
    mode: Pieces,
    skip_mode: bool,
) {
    let len = value.len() as u64;
    let layout = Layout::new(len, log).unwrap();
    let glen = layout.group_len();
    let (root, outboard) = build_outboard_vec(value, log).unwrap();
    let groups = layout.group_range(range).unwrap();
    let mut genuine = vec![0u8; encoded_len(layout, range).unwrap() as usize];
    assert_eq!(
        encode_range(value, &outboard, log, range, &mut genuine).unwrap(),
        genuine.len()
    );
    let steps: Vec<Step> = RangeEncoder::new(layout, range).unwrap().map(Result::unwrap).collect();
    // The offset of each stream item, and its size.
    let mut starts = Vec::new();
    let mut at = 0usize;
    for step in &steps {
        starts.push(at);
        at += match *step {
            Step::Parent { .. } => 64,
            Step::Group { len, .. } => len as usize,
        };
    }
    assert_eq!(at, genuine.len());

    let mut stream = genuine.clone();
    match kind {
        Kind::Genuine => {}
        Kind::Flip => {
            let i = below(rng, stream.len() as u64) as usize;
            stream[i] ^= 1 << below(rng, 8);
        }
        Kind::Trunc => stream.truncate(below(rng, stream.len() as u64) as usize),
        Kind::Extra => {
            let extra = 1 + below(rng, 8) as usize;
            stream.extend((0..extra).map(|_| rng.next_u64() as u8));
        }
    }

    let mut rv = RangeVerifier::<G>::new(root, len, range).unwrap();
    let mut gv = GroupVerifier::new(root, len, log, range).unwrap();
    let root_id = tr.cvs.id(root);
    let _ = writeln!(
        tr.out,
        "{{\"t\":\"gvrun\",\"run\":{run},\"kind\":\"{}\",\"skip\":{skip_mode},\"len\":{len},\"log\":{log},\"s\":{},\"e\":{},\"n\":{},\"first\":{},\"last\":{},\"root\":{root_id}}}",
        kind.name(),
        range.start,
        range.end,
        layout.groups(),
        groups.start,
        groups.end,
    );

    // The logical stream position (the offset of the first byte not yet fed), the offset of the item being read,
    // the number of items completed, the bytes buffered by `RangeVerifier` and the first error seen.
    let mut pos = 0usize;
    let mut filled = 0usize;
    let mut item_start = 0usize;
    let mut item_idx = 0usize;
    let mut failed = false;
    let mut errors = 0;
    let mut r_released: Vec<(u64, Vec<u8>)> = Vec::new();
    let mut g_released: Vec<(u64, u64, Vec<u8>)> = Vec::new();
    let mut first_error: Option<TreeError> = None;
    let mut skipped_any = false;
    let mut empty_first = stream.is_empty() || below(rng, 4) == 0;
    let mut attempts = 0;
    while pos < stream.len() || empty_first {
        // `skip_group` attempts: usually when the verifier sits at a group, sometimes anywhere.
        if skip_mode && !empty_first && attempts < 400 {
            let at_group = matches!(gv.next_item(), Some(Item::Group { .. })) && gv.at_boundary();
            let try_skip = if at_group {
                below(rng, 2) == 0
            } else {
                below(rng, 6) == 0
            };
            if try_skip {
                attempts += 1;
                let (item0, bound0, nl0g, cmp0, fail0) = (
                    gv.next_item(),
                    gv.at_boundary(),
                    gv.next_len(),
                    gv.is_complete(),
                    gv.failure(),
                );
                let res = gv.skip_group();
                let (item1, bound1, nl1g, cmp1, fail1) = (
                    gv.next_item(),
                    gv.at_boundary(),
                    gv.next_len(),
                    gv.is_complete(),
                    gv.failure(),
                );
                let mut line = format!(
                    "{{\"t\":\"gvskip\",\"run\":{run},\"pos\":{pos},\"fill\":{filled},\"item0\":{},\"bound0\":{bound0},\"nl0\":{},\"cmp0\":{cmp0},\"fail0\":\"{}\",",
                    item_json(item0),
                    json_u64(nl0g),
                    error_name(fail0),
                );
                match res {
                    Ok(m) => {
                        // `RangeVerifier` is fed the genuine bytes of the group in one call.
                        assert!(at_group && !failed && filled == 0);
                        let Some(Item::Group { offset, len: size }) = item0 else {
                            unreachable!()
                        };
                        assert_eq!((m.offset, m.len), (offset, size));
                        let idx = item_idx;
                        let st = starts[idx];
                        assert_eq!(st, pos);
                        let bytes = genuine[st..st + size as usize].to_vec();
                        let nl0r = rv.next_len();
                        let fed = rv.feed(&bytes).unwrap();
                        let released = fed.verified.unwrap();
                        assert_eq!(
                            (released.offset, fed.consumed, released.data),
                            (offset, bytes.len(), &bytes[..])
                        );
                        let rd = tr.data.id(*blake3::hash(released.data).as_bytes());
                        let ptr = if std::ptr::eq(released.data.as_ptr(), bytes.as_ptr()) {
                            "input"
                        } else {
                            "buf"
                        };
                        let (rcons, roff) = (fed.consumed, released.offset);
                        r_released.push((released.offset, bytes.clone()));
                        let o = oracle(tr, steps.get(idx), idx == 0, glen, &bytes);
                        // The `RangeVerifier` half: the genuine group fed whole, as a plain `feed` event.
                        let _ = writeln!(
                            tr.out,
                            "{{\"t\":\"gvrfeed\",\"run\":{run},\"ilen\":{},\"pos\":{pos},\"istart\":{st},\"fast\":true,\"nl0\":{},\"out\":\"release\",\"err\":\"none\",\"consumed\":{rcons},\"off\":{roff},\"ptr\":\"{ptr}\",\"rd\":{rd},\"nl\":{},\"cmp\":{},\"key\":{},\"hout\":{},\"item\":{},\"step\":{}}}",
                            bytes.len(),
                            json_u64(nl0r.map(|x| x as u64)),
                            json_u64(rv.next_len().map(|x| x as u64)),
                            rv.is_complete(),
                            o.key,
                            o.hout,
                            o.item,
                            step_json(steps.get(idx)),
                        );
                        let _ = write!(
                            line,
                            "\"ok\":true,\"off\":{},\"glen\":{},\"item1\":{},\"bound1\":{bound1},\"nl1\":{},\"cmp1\":{cmp1},\"fail1\":\"{}\"}}",
                            m.offset,
                            m.len,
                            item_json(item1),
                            json_u64(nl1g),
                            error_name(fail1),
                        );
                        item_idx += 1;
                        item_start = st + size as usize;
                        pos = item_start;
                        skipped_any = true;
                        assert_eq!(rv.is_complete(), gv.is_complete());
                        assert_eq!(rv.next_len().map(|x| x as u64), gv.next_len());
                    }
                    Err(e) => {
                        assert_eq!(e, TreeError::TooMuchData);
                        // A refused skip leaves the verifier as it was.
                        assert_eq!((item1, bound1, nl1g, cmp1, fail1), (item0, bound0, nl0g, cmp0, fail0));
                        assert!(!at_group || failed);
                        let _ = write!(
                            line,
                            "\"ok\":false,\"item1\":{},\"bound1\":{bound1},\"nl1\":{},\"cmp1\":{cmp1},\"fail1\":\"{}\"}}",
                            item_json(item1),
                            json_u64(nl1g),
                            error_name(fail1)
                        );
                    }
                }
                line.push('\n');
                tr.out.push_str(&line);
                continue;
            }
        }
        let nl0 = rv.next_len();
        let (gnl0, gb0, gi0) = (gv.next_len(), gv.at_boundary(), gv.next_item());
        assert_eq!(nl0.map(|x| x as u64), gnl0);
        let (call_pos, call_item_start) = (pos, item_start);
        let want = if empty_first {
            0
        } else {
            window(mode, rng, stream.len() - pos, G, stream.len(), nl0)
        };
        empty_first = false;
        let input = &stream[pos..pos + want];
        let fast = filled == 0 && nl0.is_some_and(|r| input.len() >= r);
        let (mut consumed, mut off, mut rd, mut err, mut ptr) = (None, None, 0u32, None, "none");
        match rv.feed(input) {
            Ok(fed) => {
                consumed = Some(fed.consumed);
                if let Some(g) = fed.verified {
                    off = Some(g.offset);
                    ptr = if std::ptr::eq(g.data.as_ptr(), input.as_ptr()) {
                        "input"
                    } else {
                        "buf"
                    };
                    rd = tr.data.id(*blake3::hash(g.data).as_bytes());
                    r_released.push((g.offset, g.data.to_vec()));
                }
            }
            Err(e) => err = Some(e),
        }
        let (gconsumed, goff, glen_rep, grd, gerr) = match gv.feed(input) {
            Ok(fed) => {
                let (o, l, d) = fed.group.map_or((None, None, 0), |m| {
                    // The caller keeps the pieces: the group is the stream slice that ends where this call ended.
                    let end = pos + fed.consumed;
                    let bytes = stream[end - m.len as usize..end].to_vec();
                    g_released.push((m.offset, m.len, bytes.clone()));
                    (
                        Some(m.offset),
                        Some(m.len),
                        tr.data.id(*blake3::hash(&bytes).as_bytes()),
                    )
                });
                (Some(fed.consumed), o, l, d, None)
            }
            Err(e) => (None, None, None, 0, Some(e)),
        };
        // The two verifiers agree on every observable.
        assert_eq!((consumed, off, err), (gconsumed, goff, gerr));
        assert_eq!(rd, grd);
        assert_eq!(rv.next_len().map(|x| x as u64), gv.next_len());
        assert_eq!(rv.is_complete(), gv.is_complete());
        let (nl, cmp) = (rv.next_len(), rv.is_complete());
        let completed = match (&err, consumed, nl0) {
            (None, Some(c), Some(r)) => c == r,
            (Some(TreeError::ParentMismatch | TreeError::GroupMismatch), _, Some(_)) => !failed,
            _ => false,
        };
        let (mut key, mut hout, mut item) = (NO_ORACLE.0.to_string(), NO_ORACLE.1, NO_ORACLE.2.to_string());
        let step = if completed { steps.get(item_idx) } else { None };
        if completed {
            let need = filled + nl0.unwrap();
            let bytes = &stream[item_start..item_start + need];
            let o = oracle(tr, steps.get(item_idx), item_idx == 0, glen, bytes);
            (key, hout, item) = (o.key, o.hout, o.item);
            item_start += need;
            item_idx += 1;
            filled = 0;
        } else if let Some(c) = consumed {
            filled += c;
        }
        let out = match (&err, consumed, off, failed) {
            (_, _, _, true) => "sticky",
            (Some(TreeError::TooMuchData), ..) => "toomuch",
            (Some(_), ..) => "reject",
            (None, _, Some(_), _) => "release",
            (None, _, None, _) if want == 0 => "empty",
            (None, _, None, _) if completed => "parent",
            (None, ..) => "more",
        };
        let err_name = error_name(err);
        if !failed && matches!(err, Some(TreeError::ParentMismatch | TreeError::GroupMismatch)) {
            failed = true;
        }
        let _ = writeln!(
            tr.out,
            "{{\"t\":\"gvfeed\",\"run\":{run},\"ilen\":{},\"pos\":{call_pos},\"istart\":{},\"fast\":{fast},\"out\":\"{out}\",\"err\":\"{err_name}\",\"consumed\":{},\"off\":{},\"glen\":{},\"ptr\":\"{ptr}\",\"rd\":{rd},\"grd\":{grd},\"nl0\":{},\"nl\":{},\"cmp\":{cmp},\"gnl0\":{},\"gb0\":{gb0},\"gi0\":{},\"gnl\":{},\"gb\":{},\"gi\":{},\"gcmp\":{},\"gfail\":\"{}\",\"key\":{key},\"hout\":{hout},\"item\":{item},\"step\":{}}}",
            input.len(),
            if completed {
                i64::try_from(call_item_start).unwrap()
            } else {
                -1
            },
            json_u64(consumed.map(|x| x as u64)),
            json_u64(off),
            json_u64(glen_rep),
            json_u64(nl0.map(|x| x as u64)),
            json_u64(nl.map(|x| x as u64)),
            json_u64(gnl0),
            item_json(gi0),
            json_u64(gv.next_len()),
            gv.at_boundary(),
            item_json(gv.next_item()),
            gv.is_complete(),
            error_name(gv.failure()),
            step_json(step),
        );
        if let Some(e) = err {
            first_error.get_or_insert(e);
            errors += 1;
            if errors >= 2 {
                break;
            }
        }
        pos += consumed.unwrap_or(0);
    }

    // The same facts, checked against the genuine value: what the caller of `GroupVerifier` kept is the value.
    let expect: Vec<(u64, Vec<u8>)> = (groups.start..groups.end)
        .map(|i| {
            let o = i * glen;
            (o, value[o as usize..(o + layout.group_size(i)) as usize].to_vec())
        })
        .collect();
    assert!(r_released.len() <= expect.len() && r_released == expect[..r_released.len()]);
    for (off, size, bytes) in &g_released {
        let i = (off / glen) as usize - groups.start as usize;
        assert!(*size == expect[i].1.len() as u64 && bytes == &expect[i].1);
    }
    if !skipped_any {
        assert_eq!(g_released.len(), r_released.len());
    }
    match kind {
        Kind::Genuine => assert!(first_error.is_none() && gv.is_complete() && r_released == expect),
        Kind::Flip => {
            // A flip inside a group that was skipped is not seen by `GroupVerifier`.
            assert!(matches!(first_error, Some(TreeError::ParentMismatch | TreeError::GroupMismatch)) || skipped_any);
        }
        Kind::Trunc => assert!(first_error.is_none() && (skipped_any || !gv.is_complete())),
        Kind::Extra => assert_eq!(first_error, Some(TreeError::TooMuchData)),
    }
}

fn run_dispatch(
    tr: &mut Trace,
    rng: &mut SplitMix64,
    run: usize,
    value: &[u8],
    log: u32,
    range: &Range<u64>,
    kind: Kind,
    mode: Pieces,
    skip_mode: bool,
) {
    match log {
        0 => run_case::<1024>(tr, rng, run, value, log, range, kind, mode, skip_mode),
        1 => run_case::<2048>(tr, rng, run, value, log, range, kind, mode, skip_mode),
        2 => run_case::<4096>(tr, rng, run, value, log, range, kind, mode, skip_mode),
        _ => run_case::<8192>(tr, rng, run, value, log, range, kind, mode, skip_mode),
    }
}

fn verify_traces() -> Trace {
    let mut tr = Trace::default();
    let mut rng = SplitMix64::traced(0x6a75_5e11);
    let mut run = 0;
    for case in 0..trace_cases(72, 140) as u64 {
        let log = below(&mut rng, 4) as u32;
        let g = 1024u64 << log;
        let groups = if case < 20 { case } else { below(&mut rng, 17) };
        let len = match below(&mut rng, 3) {
            0 => groups * g,
            _ if groups == 0 => 0,
            _ => (groups - 1) * g + 1 + below(&mut rng, g),
        };
        let mut value = vec![0u8; len as usize];
        rng.fill(&mut value);
        let range = match below(&mut rng, 6) {
            0 => 0..len,
            1 => {
                let a = below(&mut rng, len + 1);
                a..a
            }
            2 if len > 0 => {
                let a = below(&mut rng, len);
                a..a + 1
            }
            _ if len > 0 => {
                let a = below(&mut rng, len);
                a..a + 1 + below(&mut rng, len - a)
            }
            _ => 0..0,
        };
        let mode = |rng: &mut SplitMix64| match below(rng, 3) {
            0 => Pieces::Whole,
            1 => Pieces::Mixed,
            _ => Pieces::Tiny,
        };
        let skip = case % 2 == 1;
        let m = mode(&mut rng);
        run_dispatch(&mut tr, &mut rng, run, &value, log, &range, Kind::Genuine, m, skip);
        run += 1;
        let m = mode(&mut rng);
        let kind = [Kind::Flip, Kind::Flip, Kind::Trunc, Kind::Extra][below(&mut rng, 4) as usize];
        let empty = encoded_len(Layout::new(len, log).unwrap(), &range).unwrap() == 0;
        let kind = if empty { Kind::Extra } else { kind };
        run_dispatch(&mut tr, &mut rng, run, &value, log, &range, kind, m, skip);
        run += 1;
    }
    tr
}

#[test]
fn group_and_range_verifiers_agree_on_every_call() {
    let tr = verify_traces();
    for needle in [
        "\"out\":\"release\"",
        "\"out\":\"parent\"",
        "\"out\":\"more\"",
        "\"out\":\"reject\"",
        "\"out\":\"sticky\"",
        "\"out\":\"toomuch\"",
        "\"out\":\"empty\"",
        "\"err\":\"parent\"",
        "\"err\":\"group\"",
        "\"gfail\":\"group\"",
        "\"gfail\":\"parent\"",
        "\"t\":\"gvskip\"",
        "\"ok\":true",
        "\"ok\":false",
        "\"gb\":false",
        "\"gi\":[\"g\"",
    ] {
        assert!(
            pinc_tests::soaking() || tr.out.contains(needle),
            "the runs never produce {needle}"
        );
    }
    let lines = tr.out.lines().count();
    assert!(lines > 2000, "{lines} events");
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("values_verify.ndjson"), tr.out).unwrap();
}
