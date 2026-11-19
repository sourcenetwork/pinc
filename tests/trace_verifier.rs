//! Trace generation for the range verifier: seeded random runs of the real `RangeVerifier` over genuine and
//! tampered streams, fed in pieces of every size, recorded as ndjson for the TLA+ trace check and the Lean replay.
//!
//! A run proves a random byte range of a random value. The stream is the genuine `encode_range` output, or that
//! stream with a flipped bit, cut short, or followed by extra bytes. It is fed in windows (whole stream, a few
//! bytes, item-sized, random), so both the zero-copy path (whole next item in the input, nothing buffered) and the
//! buffered path run. Per `feed` call the trace records the input length, what the verifier reported (consumed
//! bytes, released offset, error, `next_len`, `is_complete`) and, when the call completed a stream item, the item
//! and the hash call the verifier made for it: the computed chaining value is the oracle. Chaining values and
//! group bytes are replaced by ids (one id per distinct value), so the checkers never see a hash function: they
//! check that the recorded oracle is a function and that every decision the verifier took is the one the model
//! takes under that oracle. The two paths are told apart by where a released group's bytes live: the fast path
//! returns a borrow of the input, the buffered path a borrow of the verifier's buffer (`ptr`).
//!
//! Every feed event also records the stream offset of the input (`pos`) and, when the call completed a stream item, the
//! offset of that item's first byte (`istart`), so the Lean replay can run the byte-level model of `feed` on the real
//! offsets: the buffer, `filled`, the fast path and the slow path.
//!
//! Two more files are written next to the verifier runs. `encoder.ndjson` holds the complete step list of
//! `RangeEncoder` for layouts of every size up to `u64::MAX` bytes (no value is needed to walk the tree): each
//! parent step is `64 * preorder position` of a node and each group step names a group, so the lists expose the
//! `left_groups` split of every node visited and the position of every parent. `encout.ndjson` holds `encode_range`
//! with output buffers of every size around the stream's length: `OutputTooSmall` exactly when the buffer is short.
//!
//! Every run is also checked here against the genuine value, so the test is meaningful without the proof tools.
//! The traces are written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written. The
//! same directory gets the `Layout` size cases (`groups`, `depth`, `outboard_size`, `group_size`).
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::too_many_arguments,
    clippy::struct_excessive_bools
)]

use std::collections::HashMap;
use std::fmt::Write as _;
use std::ops::Range;

use blake3::Hasher;
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};
use pinc_dag::tree::{
    Cv, Layout, RangeEncoder, RangeVerifier, Step, TreeError, build_outboard_vec, encode_range, encoded_len,
};
use pinc_tests::SplitMix64;

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// Dense ids, from 1, for distinct 32-byte values (chaining values, and fingerprints of group bytes).
#[derive(Default)]
struct Ids(HashMap<[u8; 32], u32>);

impl Ids {
    fn id(&mut self, key: [u8; 32]) -> u32 {
        let next = u32::try_from(self.0.len()).unwrap() + 1;
        *self.0.entry(key).or_insert(next)
    }
}

/// The hash call `RangeVerifier` makes for a group: the root hashes plainly, any other group is hashed at its
/// input offset and finalised as a non-root node.
fn leaf_cv(root: bool, offset: u64, data: &[u8]) -> Cv {
    let mut hasher = Hasher::new();
    if root {
        *hasher.update(data).finalize().as_bytes()
    } else {
        hasher.set_input_offset(offset).update(data);
        hasher.finalize_non_root()
    }
}

/// The hash call `RangeVerifier` makes for a parent pair.
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

/// How the stream is cut into the inputs of `feed`.
#[derive(Clone, Copy)]
enum Pieces {
    /// Everything that remains, so every item arrives whole: the fast path.
    Whole,
    /// A mix of single bytes, item-sized and random windows: both paths, and the boundaries between them.
    Mixed,
    /// Windows much smaller than an item: the buffered path.
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

/// One run's recorded events, and the ids shared by the whole file.
#[derive(Default)]
struct Trace {
    out: String,
    cvs: Ids,
    data: Ids,
}

fn json_u64(v: Option<u64>) -> i64 {
    v.map_or(-1, |x| i64::try_from(x).unwrap())
}

fn error_name(e: TreeError) -> &'static str {
    match e {
        TreeError::ParentMismatch => "parent",
        TreeError::GroupMismatch => "group",
        TreeError::TooMuchData => "toomuch",
        other => unreachable!("unexpected verifier error {other:?}"),
    }
}

/// The stream item the verifier is waiting for, as the encoder's step describes it.
fn step_json(step: Option<&Step>) -> String {
    match step {
        Some(Step::Parent { outboard_offset }) => format!("[\"p\",{outboard_offset}]"),
        Some(Step::Group { offset, len }) => format!("[\"g\",{offset},{len}]"),
        None => "[]".to_string(),
    }
}

fn run_case<const G: usize>(
    tr: &mut Trace,
    rng: &mut SplitMix64,
    run: usize,
    value: &[u8],
    log: u32,
    range: &Range<u64>,
    kind: Kind,
    mode: Pieces,
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
    // The steps are the stream: item sizes add up, and each item is the slice the step names.
    let mut at = 0usize;
    for step in &steps {
        let (src, n) = match *step {
            Step::Parent { outboard_offset } => (&outboard[outboard_offset as usize..][..64], 64),
            Step::Group { offset, len } => (&value[offset as usize..][..len as usize], len as usize),
        };
        assert_eq!(&genuine[at..at + n], src);
        at += n;
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

    let mut v = RangeVerifier::<G>::new(root, len, range).unwrap();
    let root_id = tr.cvs.id(root);
    let _ = writeln!(
        tr.out,
        "{{\"t\":\"vrun\",\"run\":{run},\"kind\":\"{}\",\"len\":{len},\"log\":{log},\"s\":{},\"e\":{},\"n\":{},\"first\":{},\"last\":{},\"root\":{root_id}}}",
        kind.name(),
        range.start,
        range.end,
        layout.groups(),
        groups.start,
        groups.end,
    );

    let mut pos = 0usize;
    let mut filled = 0usize;
    let mut item_start = 0usize;
    let mut item_idx = 0usize;
    let mut failed: Option<&'static str> = None;
    let mut errors = 0;
    let mut released: Vec<(u64, Vec<u8>)> = Vec::new();
    let mut first_error: Option<TreeError> = None;
    // An empty input is a no-op, always allowed; the first call of a run is sometimes one.
    let mut empty_first = stream.is_empty() || below(rng, 4) == 0;
    while pos < stream.len() || empty_first {
        let nl0 = v.next_len();
        let (call_pos, call_item_start) = (pos, item_start);
        let want = if empty_first {
            0
        } else {
            window(mode, rng, stream.len() - pos, G, stream.len(), nl0)
        };
        empty_first = false;
        let input = &stream[pos..pos + want];
        let fast = filled == 0 && nl0.is_some_and(|r| input.len() >= r);
        // What the call did, as the test sees it through the public API only.
        let mut consumed: Option<usize> = None;
        let mut off: Option<u64> = None;
        let mut ptr = "none";
        let mut rd = 0u32;
        let mut err: Option<TreeError> = None;
        match v.feed(input) {
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
                    released.push((g.offset, g.data.to_vec()));
                }
            }
            Err(e) => err = Some(e),
        }
        let (nl, cmp) = (v.next_len(), v.is_complete());
        // Did this call complete a stream item? The verifier took exactly what it still needed.
        let completed = match (&err, consumed, nl0) {
            (None, Some(c), Some(r)) => c == r,
            (Some(TreeError::ParentMismatch | TreeError::GroupMismatch), _, Some(_)) => failed.is_none(),
            _ => false,
        };
        let mut key = "[]".to_string();
        let mut hout = 0u32;
        let mut item = "{\"l\":0,\"r\":0,\"d\":0}".to_string();
        let step = if completed { steps.get(item_idx) } else { None };
        if completed {
            let need = filled + nl0.unwrap();
            let bytes = &stream[item_start..item_start + need];
            let root_flag = item_idx == 0;
            match steps.get(item_idx) {
                Some(Step::Parent { .. }) => {
                    let (l, r): (Cv, Cv) = (bytes[..32].try_into().unwrap(), bytes[32..64].try_into().unwrap());
                    let (li, ri) = (tr.cvs.id(l), tr.cvs.id(r));
                    hout = tr.cvs.id(parent_cv(root_flag, &l, &r));
                    key = format!("[\"P\",{root_flag},{li},{ri}]");
                    item = format!("{{\"l\":{li},\"r\":{ri},\"d\":0}}");
                }
                Some(Step::Group { offset, .. }) => {
                    let di = tr.data.id(*blake3::hash(bytes).as_bytes());
                    hout = tr.cvs.id(leaf_cv(root_flag, *offset, bytes));
                    key = format!("[\"L\",{root_flag},{},{di}]", offset / glen);
                    item = format!("{{\"l\":0,\"r\":0,\"d\":{di}}}");
                }
                None => unreachable!("a completed item beyond the genuine stream"),
            }
            item_start += need;
            item_idx += 1;
            filled = 0;
        } else if let Some(c) = consumed {
            filled += c;
        }
        let out = match (&err, consumed, off, failed) {
            (_, _, _, Some(_)) => "sticky",
            (Some(TreeError::TooMuchData), ..) => "toomuch",
            (Some(_), ..) => "reject",
            (None, _, Some(_), _) => "release",
            (None, _, None, _) if want == 0 => "empty",
            (None, _, None, _) if completed => "parent",
            (None, ..) => "more",
        };
        let err_name = err.map_or("none", error_name);
        if failed.is_none() && matches!(err, Some(TreeError::ParentMismatch | TreeError::GroupMismatch)) {
            failed = Some(err_name);
        }
        let _ = writeln!(
            tr.out,
            "{{\"t\":\"vfeed\",\"run\":{run},\"ilen\":{},\"pos\":{call_pos},\"istart\":{},\"fast\":{fast},\"nl0\":{},\"out\":\"{out}\",\"err\":\"{err_name}\",\"consumed\":{},\"off\":{},\"ptr\":\"{ptr}\",\"rd\":{rd},\"nl\":{},\"cmp\":{cmp},\"key\":{key},\"hout\":{hout},\"item\":{item},\"step\":{}}}",
            input.len(),
            if completed {
                i64::try_from(call_item_start).unwrap()
            } else {
                -1
            },
            json_u64(nl0.map(|x| x as u64)),
            json_u64(consumed.map(|x| x as u64)),
            json_u64(off),
            json_u64(nl.map(|x| x as u64)),
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

    // The same facts, checked against the genuine value.
    let expect: Vec<(u64, Vec<u8>)> = (groups.start..groups.end)
        .map(|i| {
            let o = i * glen;
            (o, value[o as usize..(o + layout.group_size(i)) as usize].to_vec())
        })
        .collect();
    assert!(released.len() <= expect.len() && released == expect[..released.len()]);
    match kind {
        Kind::Genuine => {
            assert!(first_error.is_none() && v.is_complete() && released == expect);
        }
        Kind::Flip => {
            assert!(matches!(
                first_error,
                Some(TreeError::ParentMismatch | TreeError::GroupMismatch)
            ));
            assert!(!v.is_complete() && v.next_len().is_none());
        }
        Kind::Trunc => {
            assert!(first_error.is_none() && !v.is_complete() && v.next_len().is_some());
        }
        Kind::Extra => {
            assert_eq!(first_error, Some(TreeError::TooMuchData));
            assert!(v.is_complete() && released == expect);
        }
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
) {
    match log {
        0 => run_case::<1024>(tr, rng, run, value, log, range, kind, mode),
        1 => run_case::<2048>(tr, rng, run, value, log, range, kind, mode),
        2 => run_case::<4096>(tr, rng, run, value, log, range, kind, mode),
        _ => run_case::<8192>(tr, rng, run, value, log, range, kind, mode),
    }
}

fn verifier_traces() -> Trace {
    let mut tr = Trace::default();
    let mut rng = SplitMix64::traced(0x7e21_f1e4);
    let mut run = 0;
    for case in 0..120u64 {
        let log = below(&mut rng, 4) as u32;
        let g = 1024u64 << log;
        // Up to 16 groups, so the tree has several levels; the length is a multiple of the group size, or not.
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
        let m = mode(&mut rng);
        run_dispatch(&mut tr, &mut rng, run, &value, log, &range, Kind::Genuine, m);
        run += 1;
        let m = mode(&mut rng);
        let kind = [Kind::Flip, Kind::Flip, Kind::Trunc, Kind::Extra][below(&mut rng, 4) as usize];
        // A flip or a cut needs a stream to damage.
        let empty = encoded_len(Layout::new(len, log).unwrap(), &range).unwrap() == 0;
        let kind = if empty { Kind::Extra } else { kind };
        run_dispatch(&mut tr, &mut rng, run, &value, log, &range, kind, m);
        run += 1;
    }
    tr
}

/// One `encoder` event: the complete step list of `RangeEncoder` for `range` of a value of `len` bytes. The encoder
/// needs only the layout, so `len` may be anything up to `u64::MAX`. The steps are checked here against the layout:
/// the group steps are exactly the groups of the range, in order, and every parent offset is a multiple of 64.
fn emit_encoder(out: &mut String, len: u64, log: u32, range: Range<u64>) {
    let layout = Layout::new(len, log).unwrap();
    let steps: Vec<Step> = RangeEncoder::new(layout, &range).unwrap().map(Result::unwrap).collect();
    let groups = layout.group_range(&range).unwrap();
    let glen = layout.group_len();
    let seen: Vec<u64> = steps
        .iter()
        .filter_map(|s| match *s {
            Step::Group { offset, len } => {
                assert_eq!(len, layout.group_size(offset / glen));
                Some(offset / glen)
            }
            Step::Parent { outboard_offset } => {
                assert_eq!(outboard_offset % 64, 0);
                assert!(outboard_offset < layout.outboard_size());
                None
            }
        })
        .collect();
    assert!(seen.iter().copied().eq(groups.start..groups.end));
    let body: Vec<String> = steps.iter().map(|s| step_json(Some(s))).collect();
    let _ = writeln!(
        out,
        "{{\"t\":\"enc\",\"len\":{len},\"log\":{log},\"s\":{},\"e\":{},\"steps\":[{}]}}",
        range.start,
        range.end,
        body.join(",")
    );
}

/// `RangeEncoder` step lists over layouts from one group to `2^54` groups.
fn encoder_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0xe4c0_de01);
    // Every tree up to 70 groups over its whole range, and narrow ranges in it.
    for n in 1..=70u64 {
        let log = (n % 21) as u32;
        let g = 1024u64 << log;
        for len in [n * g, (n - 1) * g + 1 + below(&mut rng, g)] {
            emit_encoder(&mut out, len, log, 0..len);
            emit_encoder(&mut out, len, log, 0..1);
            emit_encoder(&mut out, len, log, len - 1..len);
            let a = below(&mut rng, len);
            emit_encoder(&mut out, len, log, a..a + 1 + below(&mut rng, len - a));
            emit_encoder(&mut out, len, log, a..a);
        }
    }
    // Trees of 71 to 1500 groups: a few ranges each, the whole tree for some.
    for _ in 0..60 {
        let log = below(&mut rng, 4) as u32;
        let g = 1024u64 << log;
        let n = 71 + below(&mut rng, 1430);
        let len = (n - 1) * g + 1 + below(&mut rng, g);
        if n <= 300 {
            emit_encoder(&mut out, len, log, 0..len);
        }
        let a = below(&mut rng, len);
        emit_encoder(&mut out, len, log, a..a + 1 + below(&mut rng, (len - a).min(40 * g)));
    }
    // Huge trees, up to 2^54 groups (a value of u64::MAX bytes): around every power of two, with narrow ranges at
    // the start, the end and in the middle.
    for log in [0u32, 0, 1, 3, 7, 12, 20] {
        let g = 1024u64 << log;
        let max_n = u64::MAX.div_ceil(g);
        let mut counts = vec![max_n, max_n - 1, 1 + below(&mut rng, max_n)];
        for k in 1..=max_n.ilog2() {
            let p = 1u64 << k;
            counts.extend([p - 1, p, p + 1].into_iter().filter(|&c| c >= 1 && c <= max_n));
        }
        for n in counts {
            let len = if n == max_n {
                u64::MAX
            } else {
                (n - 1) * g + 1 + below(&mut rng, g)
            };
            assert_eq!(Layout::new(len, log).unwrap().groups(), n);
            let a = below(&mut rng, len);
            let width = (below(&mut rng, 3 * g)).min(len - a - 1) + 1;
            for range in [0..1, len - 1..len, a..a + width, a..a, 0..len.min(2 * g + 1)] {
                emit_encoder(&mut out, len, log, range);
            }
        }
    }
    out
}

/// `encode_range` with output buffers of every size around the stream's length, on a real value and outboard.
fn encout_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0x0e07_5eed);
    for _ in 0..160 {
        let log = below(&mut rng, 3) as u32;
        let g = 1024u64 << log;
        let groups = below(&mut rng, 13);
        let len = match below(&mut rng, 3) {
            0 => groups * g,
            _ if groups == 0 => 0,
            _ => (groups - 1) * g + 1 + below(&mut rng, g),
        };
        let mut value = vec![0u8; len as usize];
        rng.fill(&mut value);
        let (_, outboard) = build_outboard_vec(&value, log).unwrap();
        let layout = Layout::new(len, log).unwrap();
        let a = below(&mut rng, len + 1);
        let range = match below(&mut rng, 3) {
            0 => 0..len,
            1 => a..a,
            _ => a..a + below(&mut rng, len - a + 1),
        };
        let exact = encoded_len(layout, &range).unwrap() as usize;
        let mut sizes = vec![
            exact,
            exact.saturating_sub(1),
            0,
            exact + 1 + below(&mut rng, 10) as usize,
        ];
        sizes.push(below(&mut rng, exact as u64 + 1) as usize);
        for olen in sizes {
            let mut buf = vec![0xaa; olen];
            let res = encode_range(&value, &outboard, log, &range, &mut buf);
            let verdict = match res {
                Ok(n) => {
                    assert!(olen >= exact && n == exact);
                    format!("\"res\":\"ok\",\"n\":{n}")
                }
                Err(TreeError::OutputTooSmall) => {
                    assert!(olen < exact);
                    "\"res\":\"small\",\"n\":0".to_string()
                }
                Err(other) => unreachable!("unexpected error {other:?}"),
            };
            let _ = writeln!(
                out,
                "{{\"t\":\"encout\",\"len\":{len},\"log\":{log},\"s\":{},\"e\":{},\"olen\":{olen},{verdict}}}",
                range.start, range.end
            );
        }
    }
    out
}

/// `groups`, `depth`, `outboard_size` and `group_size` over lengths from 0 to `u64::MAX` and every group log.
fn size_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0x512e_0001);
    for _ in 0..1500 {
        let log = below(&mut rng, 21) as u32;
        let group = 1024u64 << log;
        let len = match below(&mut rng, 6) {
            0 => below(&mut rng, 4 * group),
            1 => group.saturating_mul(below(&mut rng, 70)),
            2 => group.saturating_mul(below(&mut rng, 70)).saturating_add(1),
            3 => rng.next_u64() >> below(&mut rng, 64),
            4 => u64::MAX - below(&mut rng, 3),
            _ => (1u64 << below(&mut rng, 64))
                .wrapping_add(below(&mut rng, 3))
                .wrapping_sub(1),
        };
        let l = Layout::new(len, log).unwrap();
        let n = l.groups();
        let mut idx = vec![
            0,
            1,
            n.saturating_sub(1),
            n,
            n.saturating_add(1),
            u64::MAX,
            below(&mut rng, n.saturating_add(2)),
        ];
        idx.sort_unstable();
        idx.dedup();
        let sizes: Vec<String> = idx.iter().map(|&i| format!("[{i},{}]", l.group_size(i))).collect();
        let _ = writeln!(
            out,
            "{{\"t\":\"sizes\",\"len\":{len},\"log\":{log},\"groups\":{n},\"depth\":{},\"ob\":{},\"gs\":[{}]}}",
            l.depth(),
            l.outboard_size(),
            sizes.join(",")
        );
    }
    out
}

#[test]
fn verifier_traces_are_consistent_with_the_genuine_value() {
    let tr = verifier_traces();
    let sizes = size_traces();
    let encoder = encoder_traces();
    let encout = encout_traces();
    let lines = tr.out.lines().count();
    // Both paths and every outcome must have been exercised.
    for needle in [
        "\"fast\":true",
        "\"ptr\":\"input\"",
        "\"ptr\":\"buf\"",
        "\"out\":\"release\"",
        "\"out\":\"parent\"",
        "\"out\":\"more\"",
        "\"out\":\"reject\"",
        "\"out\":\"sticky\"",
        "\"out\":\"toomuch\"",
        "\"out\":\"empty\"",
        "\"err\":\"parent\"",
        "\"err\":\"group\"",
    ] {
        assert!(
            pinc_tests::soaking() || tr.out.contains(needle),
            "the runs never produce {needle}"
        );
    }
    assert!(lines > 2000, "{lines} events");
    assert!(encoder.contains("[\"p\",") && encoder.contains("[\"g\",") && encoder.lines().count() > 600);
    assert!(encout.contains("\"res\":\"small\"") && encout.contains("\"res\":\"ok\""));
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("verifier.ndjson"), tr.out).unwrap();
    std::fs::write(dir.join("sizes.ndjson"), sizes).unwrap();
    std::fs::write(dir.join("encoder.ndjson"), encoder).unwrap();
    std::fs::write(dir.join("encout.ndjson"), encout).unwrap();
}
