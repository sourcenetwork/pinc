//! Trace generation for the outboard builder: seeded random runs of the real `OutboardBuilder` over random values,
//! group sizes and splits of the value into pieces, with the error cases, recorded as ndjson for the TLA+ trace check
//! and the Lean replay.
//!
//! A run starts with a `bnew` event: the layout and the genuine tree of the value, computed here from the definition
//! of the BLAKE3 tree (the split of a node is the largest power of two strictly below its group count) with the
//! BLAKE3 library, never with the code under test. The tree is given as two tables: the hash call of each group (root
//! flag, group index, bytes in the group, chaining value) and of each parent (root flag, left and right chaining
//! values, chaining value). Chaining values are ids (one id per distinct value, from 1; 0 stands for an all-zero
//! value). The checkers replay the builder's hash calls against these tables, so they never see a hash function.
//!
//! Each call of `update` and `finish` is then one event: where in the value its piece starts, its length, the length
//! of the outboard buffer it was given, its result, and the slots of the outboard it wrote. A slot is found by
//! comparing the buffer before and after the call, so the slot of a parent is observed, never computed from the code:
//! the checkers compare it with the pre-order position of the node whose pair it holds. The error cases are probed
//! between the real calls: a buffer of the wrong size, a piece longer than the bytes still due, and a `finish` before
//! the last byte. An error leaves the buffer untouched, which is asserted here.
//!
//! Every run is also checked here against the genuine value, so the test is meaningful without the proof tools: the
//! outboard equals the pre-order list of the tree's pairs, the root is `blake3::hash(value)` (for the empty value,
//! `blake3::hash(b"")`, the constant `RangeVerifier::new` checks), and the verifier accepts the builder's outboard.
//! The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::collections::HashMap;
use std::fmt::Write as _;

use blake3::Hasher;
use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};
use pinc_dag::tree::{Cv, Layout, OutboardBuilder, RangeVerifier, TreeError};
use pinc_tests::{SplitMix64, trace_cases};

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

/// The chaining value of a group: the root hashes plainly, any other group is hashed at its input offset and
/// finalised as a non-root node.
fn leaf_cv(root: bool, offset: u64, data: &[u8]) -> Cv {
    let mut hasher = Hasher::new();
    if root {
        *hasher.update(data).finalize().as_bytes()
    } else {
        hasher.set_input_offset(offset).update(data);
        hasher.finalize_non_root()
    }
}

fn parent_cv(root: bool, left: &Cv, right: &Cv) -> Cv {
    if root {
        *merge_subtrees_root(left, right, Mode::Hash).as_bytes()
    } else {
        merge_subtrees_non_root(left, right, Mode::Hash)
    }
}

/// The genuine tree of a value: every hash call, and the pairs in pre-order.
#[derive(Default)]
struct Tree {
    /// (root flag, group index, bytes in the group, chaining value)
    leaves: Vec<(bool, u64, usize, Cv)>,
    /// (root flag, left, right, chaining value)
    parents: Vec<(bool, Cv, Cv, Cv)>,
    /// The pair of each parent, in pre-order.
    pairs: Vec<(Cv, Cv)>,
}

/// The largest power of two strictly below `count >= 2`, written here from the definition.
fn split(count: u64) -> u64 {
    count.next_power_of_two() / 2
}

/// The chaining value of the node `[lo, hi)` of the tree of `n` groups over `value`, filling `t`.
fn walk(value: &[u8], g: usize, n: u64, lo: u64, hi: u64, t: &mut Tree) -> Cv {
    let root = lo == 0 && hi == n;
    if hi - lo == 1 {
        let start = lo as usize * g;
        let bytes = &value[start..(start + g).min(value.len())];
        let cv = leaf_cv(root, start as u64, bytes);
        t.leaves.push((root, lo, bytes.len(), cv));
        return cv;
    }
    let slot = t.pairs.len();
    t.pairs.push(([0; 32], [0; 32]));
    let mid = lo + split(hi - lo);
    let left = walk(value, g, n, lo, mid, t);
    let right = walk(value, g, n, mid, hi, t);
    t.pairs[slot] = (left, right);
    let cv = parent_cv(root, &left, &right);
    t.parents.push((root, left, right, cv));
    cv
}

/// How the value is cut into pieces.
#[derive(Clone, Copy)]
enum Pieces {
    Whole,
    /// A few bytes at a time.
    Tiny,
    /// One group at a time.
    Group,
    /// Pieces of one byte less and one byte more than a group, alternating.
    Straddle,
    /// Random sizes up to two groups.
    Random,
}

fn piece_len(mode: Pieces, rng: &mut SplitMix64, g: usize, step: usize) -> usize {
    match mode {
        Pieces::Whole => usize::MAX,
        Pieces::Tiny => 1 + below(rng, 7) as usize,
        Pieces::Group => g,
        Pieces::Straddle => {
            if step.is_multiple_of(2) {
                g - 1
            } else {
                g + 1
            }
        }
        Pieces::Random => 1 + below(rng, 2 * g as u64) as usize,
    }
}

#[derive(Default)]
struct Trace {
    out: String,
    ids: Ids,
}

/// The slots (index, left id, right id) that differ between two states of the outboard buffer.
fn changed(tr: &mut Trace, before: &[u8], after: &[u8]) -> String {
    assert_eq!(before.len(), after.len());
    let mut slots = Vec::new();
    for (k, (a, b)) in before
        .as_chunks::<64>()
        .0
        .iter()
        .zip(after.as_chunks::<64>().0)
        .enumerate()
    {
        if a != b {
            let (l, r): (Cv, Cv) = (b[..32].try_into().unwrap(), b[32..].try_into().unwrap());
            slots.push(format!("[{k},{},{}]", tr.ids.id(l), tr.ids.id(r)));
        }
    }
    format!("[{}]", slots.join(","))
}

fn run_case(tr: &mut Trace, rng: &mut SplitMix64, run: usize, len: usize, log: u32, mode: Pieces) {
    let g = 1024usize << log;
    let mut value = vec![0u8; len];
    rng.fill(&mut value);
    let layout = Layout::new(len as u64, log).unwrap();
    let n = layout.groups();
    let osz = layout.outboard_size() as usize;
    assert_eq!(osz % 64, 0);

    // The genuine tree and outboard, from the definition of the tree.
    let mut tree = Tree::default();
    let genuine_root = if n == 0 {
        *blake3::hash(b"").as_bytes()
    } else {
        walk(&value, g, n, 0, n, &mut tree)
    };
    assert_eq!(genuine_root, *blake3::hash(&value).as_bytes());
    assert_eq!(tree.pairs.len() as u64, n.saturating_sub(1));
    let expected: Vec<u8> = tree
        .pairs
        .iter()
        .flat_map(|(l, r)| l.iter().chain(r.iter()).copied())
        .collect();

    let empty_id = tr.ids.id(*blake3::hash(b"").as_bytes());
    let leaves: Vec<String> = tree
        .leaves
        .iter()
        .map(|&(root, i, bytes, cv)| format!("[{root},{i},{bytes},{}]", tr.ids.id(cv)))
        .collect();
    let parents: Vec<String> = tree
        .parents
        .iter()
        .map(|&(root, l, r, cv)| format!("[{root},{},{},{}]", tr.ids.id(l), tr.ids.id(r), tr.ids.id(cv)))
        .collect();
    let _ = writeln!(
        tr.out,
        "{{\"t\":\"bnew\",\"run\":{run},\"len\":{len},\"log\":{log},\"n\":{n},\"e0\":{empty_id},\"leaves\":[{}],\"parents\":[{}]}}",
        leaves.join(","),
        parents.join(",")
    );

    let mut b = OutboardBuilder::new(len as u64, log).unwrap();
    assert_eq!(*b.layout(), layout);
    let mut out = vec![0u8; osz];
    let mut pos = 0usize;
    let mut step = 0usize;

    // One recorded `update` call; returns the result.
    let update = |tr: &mut Trace, b: &mut OutboardBuilder, pos: usize, piece: &[u8], buf: &mut [u8]| {
        let before = buf.to_vec();
        let res = b.update(piece, buf);
        let slots = changed(tr, &before, buf);
        let verdict = match res {
            Ok(()) => "ok",
            Err(TreeError::OutboardSize) => "outsize",
            Err(TreeError::TooMuchData) => "toomuch",
            Err(other) => unreachable!("unexpected update error {other:?}"),
        };
        if res.is_err() {
            assert_eq!(before, buf, "a failed update must leave the outboard untouched");
        }
        let _ = writeln!(
            tr.out,
            "{{\"t\":\"bupd\",\"run\":{run},\"pos\":{pos},\"ilen\":{},\"olen\":{},\"res\":\"{verdict}\",\"slots\":{slots}}}",
            piece.len(),
            buf.len()
        );
        res
    };
    // One recorded `finish` call on a copy of the builder.
    let finish = |tr: &mut Trace, b: &OutboardBuilder, buf: &mut [u8]| {
        let before = buf.to_vec();
        let res = b.clone().finish(buf);
        let slots = changed(tr, &before, buf);
        let (verdict, root) = match res {
            Ok(root) => ("ok", tr.ids.id(root)),
            Err(TreeError::OutboardSize) => ("outsize", 0),
            Err(TreeError::Incomplete) => ("incomplete", 0),
            Err(other) => unreachable!("unexpected finish error {other:?}"),
        };
        if res.is_err() {
            assert_eq!(before, buf, "a failed finish must leave the outboard untouched");
        }
        let _ = writeln!(
            tr.out,
            "{{\"t\":\"bfin\",\"run\":{run},\"olen\":{},\"res\":\"{verdict}\",\"root\":{root},\"slots\":{slots}}}",
            buf.len()
        );
        res
    };
    // A buffer of the wrong size.
    let wrong = |rng: &mut SplitMix64| -> usize {
        match (osz, below(rng, 3)) {
            (0, _) => 1 + below(rng, 3) as usize,
            (_, 0) => osz - 1,
            (_, 1) => osz + 1,
            _ => below(rng, osz as u64) as usize,
        }
    };

    loop {
        let remaining = len - pos;
        // The error cases, between the real calls.
        if below(rng, 6) == 0 {
            let mut bad = vec![0u8; wrong(rng)];
            let take = remaining.min(1 + below(rng, 40) as usize);
            assert_eq!(
                update(tr, &mut b, pos, &value[pos..pos + take], &mut bad),
                Err(TreeError::OutboardSize)
            );
            if remaining > 0 {
                assert_eq!(finish(tr, &b, &mut bad), Err(TreeError::OutboardSize));
            }
        }
        if below(rng, 6) == 0 {
            let extra = 1 + below(rng, 8) as usize;
            let mut over = vec![0u8; remaining + extra];
            rng.fill(&mut over);
            assert_eq!(update(tr, &mut b, pos, &over, &mut out), Err(TreeError::TooMuchData));
        }
        if remaining > 0 && below(rng, 8) == 0 {
            assert_eq!(finish(tr, &b, &mut out.clone()), Err(TreeError::Incomplete));
        }
        if below(rng, 10) == 0 {
            update(tr, &mut b, pos, &[], &mut out).unwrap();
        }
        if remaining == 0 {
            break;
        }
        let size = piece_len(mode, rng, g, step).clamp(1, remaining);
        update(tr, &mut b, pos, &value[pos..pos + size], &mut out).unwrap();
        pos += size;
        step += 1;
    }
    // After the last byte any more data is refused, and the value is complete.
    assert_eq!(update(tr, &mut b, pos, &[0], &mut out), Err(TreeError::TooMuchData));
    let mut bad = vec![0u8; wrong(rng)];
    assert_eq!(finish(tr, &b, &mut bad), Err(TreeError::OutboardSize));
    let root = finish(tr, &b, &mut out).unwrap();

    // The genuine value.
    assert_eq!(root, genuine_root);
    assert_eq!(out, expected);
    if n == 0 {
        assert!(RangeVerifier::<1024>::new(root, 0, &(0..0)).is_ok());
        let mut other = root;
        other[0] ^= 1;
        assert_eq!(
            RangeVerifier::<1024>::new(other, 0, &(0..0)).err(),
            Some(TreeError::RootMismatch)
        );
    }
}

fn builder_traces() -> String {
    let mut tr = Trace::default();
    let mut rng = SplitMix64::traced(0xb011_de42);
    for (run, case) in (0..trace_cases(60, 170) as u64).enumerate() {
        let log = below(&mut rng, 4) as u32;
        let g = 1024usize << log;
        // The first cases walk every group count from 0 to 40 so the tree takes every shape; the rest are random,
        // some with many groups.
        let groups = if case <= 40 {
            case as usize
        } else if case % 10 == 0 {
            41 + below(&mut rng, 110) as usize
        } else {
            below(&mut rng, 41) as usize
        };
        let log = if groups > 60 { 0 } else { log };
        let g = if groups > 60 { 1024 } else { g };
        let len = match below(&mut rng, 3) {
            0 => groups * g,
            _ if groups == 0 => 0,
            1 => (groups - 1) * g + 1,
            _ => (groups - 1) * g + 1 + below(&mut rng, g as u64) as usize,
        };
        let mode = match below(&mut rng, 5) {
            0 => Pieces::Whole,
            1 if len <= 3 * g => Pieces::Tiny,
            1 | 2 => Pieces::Group,
            3 => Pieces::Straddle,
            _ => Pieces::Random,
        };
        run_case(&mut tr, &mut rng, run, len, log, mode);
    }
    tr.out
}

#[test]
fn builder_traces_are_consistent_with_the_genuine_value() {
    let trace = builder_traces();
    for needle in [
        "\"t\":\"bnew\"",
        "\"t\":\"bupd\"",
        "\"t\":\"bfin\"",
        "\"res\":\"ok\"",
        "\"res\":\"outsize\"",
        "\"res\":\"toomuch\"",
        "\"res\":\"incomplete\"",
        "\"len\":0,",
        "\"ilen\":0,",
    ] {
        assert!(
            pinc_tests::soaking() || trace.contains(needle),
            "the runs never produce {needle}"
        );
    }
    assert!(trace.lines().count() > 2000, "{} events", trace.lines().count());
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("builder.ndjson"), trace).unwrap();
}
