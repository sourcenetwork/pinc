//! `pinc-dag`: the verified-range sets, the BLAKE3 outboard and range proofs, blocks and CAR archives.
//!
//! Where the expected behaviour comes from:
//! - `pinc_dag::ranges`: "A set holds disjoint, sorted `[start, end)` intervals of `u64` offsets, with overlapping and
//!   adjacent intervals merged into one. Invariant: the set only ever grows." and "an insert that would need more than
//!   `N` disjoint intervals fails with `CapacityError` and changes nothing."
//! - `pinc_dag::tree`: "The root of the BLAKE3 tree equals `blake3::hash(value)`; the parents above the group level form
//!   the outboard, 64 bytes per parent in pre-order", the layout's "a node of `n >= 2` groups splits into a left subtree
//!   of the largest power of two strictly below `n` groups and a right subtree of the rest", and the verifier's "A
//!   group's bytes are handed out only after they hash to the chaining value committed by already-verified parents, so
//!   no unverified byte reaches the caller" and "A proof of earlier groups only authenticates those bytes, which are
//!   true bytes of the value for any claimed length". The reference outboard below is built straight from those
//!   sentences with the `blake3` crate's hazmat API, independently of the builder.
//! - `pinc_dag::block`: the parser's invariants ("the canonical form of a block is unique", unknown keys "validated and
//!   skipped", "a `null` or an empty array stands for no heads") and `encode_block`'s "The result parses with
//!   `BlockRef::parse` and re-encodes identically".
//! - `pinc_dag::car`: `CarDecoder`'s contract (on `NeedMore` the caller appends at least that many bytes; "end of
//!   stream between frames is a complete CAR, end of stream inside a frame is a truncation") against `CarReader` over
//!   the same bytes, and `CarWriter::header_len` / `section_len` as the exact sizes written.

use std::ops::{ControlFlow, Range};

use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};
use ephyra::prelude::*;
use pinc_dag::block::{BlockParts, BlockRef, Link, encode_block};
use pinc_dag::car::{CarDecoder, CarError, CarReader, CarWriter, Decoded};
use pinc_dag::cid::{BLAKE3, Cid, CidRef, DAG_CBOR, RAW, SHA2_256};
use pinc_dag::ranges::{VerifiedRanges, VerifiedRangesVec};
use pinc_dag::tree::{
    Layout, OutboardBuilder, RangeVerifier, TreeError, build_outboard_vec, encode_range, encoded_len,
};
use pinc_pbt::{mangle, shrink_bytes};
use pinc_wire::cbor::{Decoder, Encoder, Item, MapReader};

// ---------------------------------------------------------------------------------------------------------------
// Verified-range sets against a list of intervals merged the obvious way.

/// Offsets on a small grid (so ranges overlap and touch), plus the top of `u64`.
fn offset() -> BoxGen<u64> {
    gens::frequency(vec![
        (8, gens::int(0u64..=24).boxed()),
        (1, gens::int(u64::MAX - 3..=u64::MAX).boxed()),
    ])
    .boxed()
}

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum RangeOp {
    Insert(#[ephyra(gen = offset())] u64, #[ephyra(gen = offset())] u64),
}

/// The model: sort, then merge every interval that overlaps or touches the one before.
fn merged(mut ivs: Vec<(u64, u64)>) -> Vec<(u64, u64)> {
    ivs.retain(|iv| iv.0 < iv.1);
    ivs.sort();
    let mut out: Vec<(u64, u64)> = Vec::new();
    for (s, e) in ivs {
        match out.last_mut() {
            Some(last) if s <= last.1 => last.1 = last.1.max(e),
            _ => out.push((s, e)),
        }
    }
    out
}

fn ranges_cases() -> impl Gen<Value = Vec<RangeOp>> {
    gens::vec(ephyra::any::<RangeOp>()).len(0..=30)
}

/// After every insert, both sets hold exactly the merged model; the fixed one refuses past 4 intervals and is then
/// unchanged; `contains`, `contains_range` and `covered_len` answer as the model does.
#[ephyra::test(gen = ranges_cases(), tests = 20_000)]
fn verified_ranges_match_the_merged_model(ops: Vec<RangeOp>) {
    let mut fixed = VerifiedRanges::<4>::new();
    let mut vec = VerifiedRangesVec::new();
    let mut model: Vec<(u64, u64)> = Vec::new();
    let mut probes: Vec<u64> = vec![0, 1, 23, 24, 25, u64::MAX - 1, u64::MAX];
    for RangeOp::Insert(a, b) in &ops {
        probes.extend([*a, *b, a.saturating_sub(1), b.saturating_add(1)]);
        let mut next = model.clone();
        next.push((*a, *b));
        let next = merged(next);
        vec.insert(*a..*b);
        let before: Vec<Range<u64>> = fixed.iter().collect();
        match fixed.insert(*a..*b) {
            Ok(()) => {
                assert!(next.len() <= 4, "insert {a}..{b} gave {} intervals in a set of 4", next.len());
                model = next;
            },
            Err(_) => {
                assert!(next.len() > 4, "insert {a}..{b} refused with {} intervals needed", next.len());
                assert_eq!(fixed.iter().collect::<Vec<_>>(), before, "a refused insert changed the set");
            },
        }
        let want: Vec<Range<u64>> = model.iter().map(|iv| iv.0..iv.1).collect();
        assert_eq!(fixed.iter().collect::<Vec<_>>(), want, "after insert {a}..{b}");
        assert_eq!(fixed.len(), want.len());
        let vwant: Vec<Range<u64>> = merged(
            vec.iter().map(|r| (r.start, r.end)).chain(std::iter::once((*a, *b))).collect(),
        )
        .iter()
        .map(|iv| iv.0..iv.1)
        .collect();
        assert_eq!(vec.iter().collect::<Vec<_>>(), vwant, "the Vec set is not merged after insert {a}..{b}");
        let covered: u64 = model.iter().map(|iv| iv.1 - iv.0).sum();
        assert_eq!(fixed.covered_len(), covered);
        for &p in &probes {
            let inside = model.iter().any(|iv| iv.0 <= p && p < iv.1);
            assert_eq!(fixed.contains(p), inside, "contains({p})");
            for &q in &probes {
                let whole = p >= q || model.iter().any(|iv| iv.0 <= p && q <= iv.1);
                assert_eq!(fixed.contains_range(p..q), whole, "contains_range({p}..{q})");
            }
        }
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Outboards and range proofs.

/// Deterministic value bytes from a seed (drawing each byte would dominate the run).
fn fill(seed: u64, len: usize) -> Vec<u8> {
    let mut x = seed | 1;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x >> 24) as u8
        })
        .collect()
}

fn left_groups(n: u64) -> u64 {
    if n < 2 { 0 } else { 1 << (n - 1).ilog2() }
}

fn group_cv(value: &[u8], group: u64, lo: u64, hi: u64) -> [u8; 32] {
    let start = (lo * group) as usize;
    let end = ((hi * group) as usize).min(value.len());
    let mut h = blake3::Hasher::new();
    h.set_input_offset(lo * group);
    h.update(&value[start..end]);
    h.finalize_non_root()
}

/// The chaining value of the node `[lo, hi)`, pushing its parents' pairs in pre-order.
fn reference_node(value: &[u8], group: u64, lo: u64, hi: u64, out: &mut Vec<u8>) -> [u8; 32] {
    if hi - lo == 1 {
        return group_cv(value, group, lo, hi);
    }
    let at = out.len();
    out.extend([0u8; 64]);
    let mid = lo + left_groups(hi - lo);
    let l = reference_node(value, group, lo, mid, out);
    let r = reference_node(value, group, mid, hi, out);
    out[at..at + 32].copy_from_slice(&l);
    out[at + 32..at + 64].copy_from_slice(&r);
    merge_subtrees_non_root(&l, &r, Mode::Hash)
}

/// The root and outboard of `value` from the module's own description.
fn reference(value: &[u8], log: u32) -> ([u8; 32], Vec<u8>) {
    let group = 1024u64 << log;
    let groups = (value.len() as u64).div_ceil(group);
    if groups <= 1 {
        return (*blake3::hash(value).as_bytes(), Vec::new());
    }
    let mut out = Vec::new();
    out.extend([0u8; 64]);
    let mid = left_groups(groups);
    let l = reference_node(value, group, 0, mid, &mut out);
    let r = reference_node(value, group, mid, groups, &mut out);
    out[..32].copy_from_slice(&l);
    out[32..64].copy_from_slice(&r);
    (*merge_subtrees_root(&l, &r, Mode::Hash).as_bytes(), out)
}

/// A value: its group-size log (0 to 3), its length (often at a group boundary or one off it) and its seed.
#[derive(Debug, Clone)]
struct Value {
    log: u32,
    len: usize,
    seed: u64,
}

fn value_gen(g: &mut Source) -> Value {
    let log = g.int(0u32..=3);
    let group = 1024usize << log;
    let len = match g.int(0u8..=3) {
        0 => g.int(0usize..=2 * group),
        1 => {
            let k = g.int(0usize..=17);
            (k * group).saturating_add_signed(g.int(-1isize..=1))
        },
        2 => g.int(0usize..=1100),
        _ => g.int(0usize..=18 * group),
    };
    Value { log, len, seed: g.int(..) }
}

fn shrink_value(v: &Value, visit: &mut dyn FnMut(Value) -> ControlFlow<()>) -> ControlFlow<()> {
    if v.log > 0 {
        visit(Value { log: v.log - 1, ..v.clone() })?;
    }
    for len in [0, v.len / 2, v.len.saturating_sub(1)] {
        if len < v.len {
            visit(Value { len, ..v.clone() })?;
        }
    }
    ControlFlow::Continue(())
}

/// A value with the sizes of the pieces it is fed in.
fn outboard_cases() -> BoxGen<(Value, Vec<usize>)> {
    (|g: &mut Source| {
        let v = value_gen(g);
        let n = g.int(0usize..=12);
        let pieces = (0..n)
            .map(|_| match g.int(0u8..=3) {
                0 => 0,
                1 => g.int(1usize..=3),
                2 => (1024usize << v.log).saturating_add_signed(g.int(-1isize..=1)),
                _ => g.int(1usize..=40_000),
            })
            .collect();
        (v, pieces)
    })
    .with_shrink(|c: &(Value, Vec<usize>), visit: &mut dyn FnMut((Value, Vec<usize>)) -> ControlFlow<()>| {
        shrink_value(&c.0, &mut |v| visit((v, c.1.clone())))?;
        for i in 0..c.1.len() {
            let mut p = c.1.clone();
            p.remove(i);
            visit((c.0.clone(), p))?;
        }
        ControlFlow::Continue(())
    })
    .boxed()
}

/// The builder fed in any pieces (empty ones and over-long ones included) gives the reference root and outboard; the
/// root is `blake3::hash` of the value; an over-long piece is refused with nothing consumed.
#[ephyra::test(gen = outboard_cases(), tests = 1_500)]
fn outboard_matches_the_reference(case: (Value, Vec<usize>)) {
    let (v, pieces) = case;
    let value = fill(v.seed, v.len);
    let (root, want) = reference(&value, v.log);
    assert_eq!(root, *blake3::hash(&value).as_bytes(), "the reference disagrees with blake3");
    let layout = Layout::new(v.len as u64, v.log).expect("log in range");
    assert_eq!(layout.outboard_size(), want.len() as u64);
    let mut ob = vec![0u8; want.len()];
    let mut b = OutboardBuilder::new(v.len as u64, v.log).expect("log in range");
    let mut rest = &value[..];
    for &p in pieces.iter().chain(std::iter::repeat(&40_000)) {
        if rest.is_empty() {
            break;
        }
        // An over-long piece is refused, then the rest is fed whole (so the loop always ends).
        let p = if p > rest.len() {
            let too_much = vec![0u8; rest.len() + 1];
            assert_eq!(b.update(&too_much, &mut ob), Err(TreeError::TooMuchData));
            rest.len()
        } else {
            p
        };
        let (head, tail) = rest.split_at(p);
        assert_eq!(b.update(head, &mut ob), Ok(()));
        rest = tail;
    }
    assert_eq!(b.update(&[], &mut ob), Ok(()));
    assert_eq!(b.finish(&mut ob), Ok(root), "builder root");
    assert!(ob == want, "builder outboard differs from the reference");
    let (r2, ob2) = build_outboard_vec(&value, v.log).expect("builds");
    assert_eq!(r2, root);
    assert!(ob2 == want, "build_outboard_vec differs from the reference");
}

/// A value, a byte range in it and the sizes of the pieces the stream is fed in.
fn proof_cases() -> BoxGen<(Value, (u64, u64), Vec<usize>)> {
    (|g: &mut Source| {
        let v = value_gen(g);
        let len = v.len as u64;
        let group = 1024u64 << v.log;
        let point = |g: &mut Source| match g.int(0u8..=2) {
            0 => g.int(0u64..=len),
            1 => (g.int(0u64..=len / group) * group).min(len),
            _ => len.saturating_sub(g.int(0u64..=2)),
        };
        let (a, b) = (point(g), point(g));
        let n = g.int(1usize..=10);
        let pieces = (0..n).map(|_| *g.pick(&[1usize, 7, 63, 64, 65, 1023, 1024, 1025, 5000, 70_000])).collect();
        (v, (a.min(b), a.max(b)), pieces)
    })
    .with_shrink(
        |c: &(Value, (u64, u64), Vec<usize>),
         visit: &mut dyn FnMut((Value, (u64, u64), Vec<usize>)) -> ControlFlow<()>| {
            shrink_value(&c.0, &mut |v| {
                let len = v.len as u64;
                visit((v, (c.1.0.min(len), c.1.1.min(len)), c.2.clone()))
            })?;
            if c.2.len() > 1 {
                visit((c.0.clone(), c.1, vec![c.2[0]]))?;
            }
            ControlFlow::Continue(())
        },
    )
    .boxed()
}

/// Feed `stream` to a verifier, cycling through the piece sizes, and collect what it releases.
fn verify_stream<const G: usize>(
    root: [u8; 32],
    len: u64,
    range: &Range<u64>,
    stream: &[u8],
    pieces: &[usize],
) -> Result<(Vec<(u64, Vec<u8>)>, bool), TreeError> {
    let mut v = RangeVerifier::<G>::new(root, len, range)?;
    let mut released = Vec::new();
    let mut rest = stream;
    let mut k = 0usize;
    // Every call consumes at least one byte of a non-empty input or fails, so this ends; the bound is a backstop.
    for _ in 0..=stream.len() + 1 {
        if rest.is_empty() {
            break;
        }
        let p = pieces.get(k % pieces.len().max(1)).copied().unwrap_or(1).min(rest.len());
        k += 1;
        let need = v.next_len();
        let fed = v.feed(&rest[..p])?;
        assert!(fed.consumed > 0, "a feed of {p} bytes consumed nothing");
        assert!(fed.consumed <= p, "a feed consumed more than it was given");
        if let Some(need) = need {
            assert!(fed.consumed <= need, "a feed consumed {} bytes past the current item of {need}", fed.consumed);
        }
        if let Some(g) = fed.verified {
            released.push((g.offset, g.data.to_vec()));
        }
        rest = &rest[fed.consumed..];
    }
    assert!(rest.is_empty(), "the feed loop did not end");
    if v.is_complete() {
        assert_eq!(v.feed(&[1]), Err(TreeError::TooMuchData), "a complete verifier took more input");
        assert_eq!(v.next_len(), None);
    }
    Ok((released, v.is_complete()))
}

macro_rules! by_group {
    ($log:expr, $f:ident ( $($a:expr),* )) => {
        match $log {
            0 => $f::<1024>($($a),*),
            1 => $f::<2048>($($a),*),
            2 => $f::<4096>($($a),*),
            _ => $f::<8192>($($a),*),
        }
    };
}

fn expected_groups(value: &[u8], layout: &Layout, range: &Range<u64>) -> Vec<(u64, Vec<u8>)> {
    let gr = layout.group_range(range).expect("range in bounds");
    gr.map(|g| {
        let off = g * layout.group_len();
        (off, value[off as usize..(off + layout.group_size(g)) as usize].to_vec())
    })
    .collect()
}

/// An honest stream has the length `encoded_len` states, and the verifier, fed it in any pieces, releases exactly the
/// groups of the range, in order, with the value's bytes, then refuses more input.
#[ephyra::test(gen = proof_cases(), tests = 1_500)]
fn range_proofs_round_trip(case: (Value, (u64, u64), Vec<usize>)) {
    let (v, (a, b), pieces) = case;
    let value = fill(v.seed, v.len);
    let (root, ob) = reference(&value, v.log);
    let layout = Layout::new(v.len as u64, v.log).expect("log in range");
    let range = a..b;
    let n = encoded_len(layout, &range).expect("range in bounds");
    let mut stream = vec![0u8; n as usize];
    assert_eq!(encode_range(&value, &ob, v.log, &range, &mut stream), Ok(n as usize));
    let mut short = vec![0u8; (n as usize).saturating_sub(1)];
    if n > 0 {
        assert_eq!(encode_range(&value, &ob, v.log, &range, &mut short), Err(TreeError::OutputTooSmall));
    }
    let got = by_group!(v.log, verify_stream(root, v.len as u64, &range, &stream, &pieces));
    let (released, complete) = got.expect("an honest stream verifies");
    assert!(complete, "the verifier is not complete after the whole stream");
    assert_eq!(released, expected_groups(&value, &layout, &range));
}

/// A hostile stream: an honest one edited, verified under the true root with the true or a wrong length. Whatever the
/// verifier releases is the value's own bytes at the stated offset; with no edit and the true length it succeeds.
fn hostile_cases() -> BoxGen<(Value, (u64, u64), i64, Vec<u8>, Vec<usize>)> {
    (|g: &mut Source| {
        let (v, (a, b), pieces) = g.draw(&proof_cases());
        let group = 1024i64 << v.log;
        let delta = match g.int(0u8..=3) {
            0 => 0,
            1 => g.int(-2i64..=2),
            2 => group * g.int(-2i64..=2) + g.int(-1i64..=1),
            _ => g.int(-100_000i64..=100_000),
        };
        let value = fill(v.seed, v.len);
        let (_, ob) = reference(&value, v.log);
        let layout = Layout::new(v.len as u64, v.log).expect("log in range");
        let n = encoded_len(layout, &(a..b)).unwrap_or(0) as usize;
        let mut stream = vec![0u8; n];
        let _ = encode_range(&value, &ob, v.log, &(a..b), &mut stream);
        if g.bool_with(0.7) {
            for _ in 0..g.int(1u8..=2) {
                stream = mangle(g, &stream);
            }
        }
        (v, (a, b), delta, stream, pieces)
    })
    .with_shrink(
        |c: &(Value, (u64, u64), i64, Vec<u8>, Vec<usize>),
         visit: &mut dyn FnMut((Value, (u64, u64), i64, Vec<u8>, Vec<usize>)) -> ControlFlow<()>| {
            if c.2 != 0 {
                visit((c.0.clone(), c.1, 0, c.3.clone(), c.4.clone()))?;
            }
            shrink_bytes(&c.3, &mut |s| visit((c.0.clone(), c.1, c.2, s, c.4.clone())))
        },
    )
    .boxed()
}

#[ephyra::test(gen = hostile_cases(), tests = 3_000)]
fn hostile_proofs_release_only_true_bytes(case: (Value, (u64, u64), i64, Vec<u8>, Vec<usize>)) {
    let (v, (a, b), delta, stream, pieces) = case;
    let value = fill(v.seed, v.len);
    let root = *blake3::hash(&value).as_bytes();
    let claimed = (v.len as i64).saturating_add(delta).max(0) as u64;
    let range = a.min(claimed)..b.min(claimed);
    let honest = {
        let layout = Layout::new(v.len as u64, v.log).expect("log in range");
        let n = encoded_len(layout, &(a..b)).unwrap_or(0) as usize;
        let mut s = vec![0u8; n];
        let _ = encode_range(&value, &reference(&value, v.log).1, v.log, &(a..b), &mut s);
        s
    };
    let got = by_group!(v.log, verify_stream(root, claimed, &range, &stream, &pieces));
    if let Ok((released, _)) = &got {
        for (off, data) in released {
            let start = *off as usize;
            let truth = value.get(start..start + data.len());
            assert!(truth == Some(&data[..]), "released {} bytes at {off} that are not the value's", data.len());
        }
    }
    if delta == 0 && stream == honest {
        let (released, complete) = got.expect("the honest stream under the true length is refused");
        assert!(complete);
        let layout = Layout::new(v.len as u64, v.log).expect("log in range");
        assert_eq!(released, expected_groups(&value, &layout, &range));
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Blocks.

fn cid_gen(g: &mut Source) -> Cid {
    let block = [g.int(0u8..=255), g.int(0u8..=3)];
    match g.int(0u8..=4) {
        0 => Cid::for_block(DAG_CBOR, SHA2_256, &block).expect("known hash"),
        1 => Cid::for_block(DAG_CBOR, BLAKE3, &block).expect("known hash"),
        2 => Cid::for_block(RAW, SHA2_256, &block).expect("known hash"),
        3 => {
            let n = g.int(0usize..=64);
            let digest: Vec<u8> = (0..n).map(|_| g.int(0u8..=255)).collect();
            Cid::new(g.int(0u64..=(1 << 20)), 0x13 + u64::from(g.int(0u8..=4)), &digest).expect("valid parts")
        },
        _ => Cid::new(DAG_CBOR, SHA2_256, &[g.int(0u8..=1); 32]).expect("valid parts"),
    }
}

fn delta_gen(g: &mut Source) -> Vec<u8> {
    let mut buf = vec![0u8; 512];
    let mut e = Encoder::new(&mut buf);
    match g.int(0u8..=4) {
        0 => e.unsigned(g.int(..)).expect("fits"),
        1 => e.text("ab").expect("fits"),
        2 => {
            e.array(2).expect("fits");
            e.null().expect("fits");
            e.bytes(&[1, 2, 3]).expect("fits");
        },
        3 => {
            let mut k = e.ordered_map(2).expect("fits");
            k.key(&mut e, "a").expect("fits");
            e.bool(true).expect("fits");
            k.key(&mut e, "bb").expect("fits");
            e.tag_cid(cid_gen(g).as_bytes()).expect("fits");
        },
        _ => e.float(-0.0).expect("fits"),
    }
    e.written().to_vec()
}

/// What a block says, owned.
#[derive(Debug, Clone, PartialEq)]
struct Logical {
    delta: Vec<u8>,
    heads: Vec<Vec<u8>>,
    links: Vec<(Vec<u8>, String)>,
    signature: Option<Vec<u8>>,
    encryption: Option<Vec<u8>>,
}

fn logical(b: &BlockRef<'_>) -> Logical {
    Logical {
        delta: b.delta().to_vec(),
        heads: b.heads().map(|c| c.as_bytes().to_vec()).collect(),
        links: b.links().map(|l| (l.cid.as_bytes().to_vec(), l.name.to_string())).collect(),
        signature: b.signature().map(|c| c.as_bytes().to_vec()),
        encryption: b.encryption().map(|c| c.as_bytes().to_vec()),
    }
}

fn encode_logical(l: &Logical) -> Result<Vec<u8>, pinc_dag::block::BlockError> {
    let cid = |b: &Vec<u8>| Cid::from_bytes(b).expect("a parsed CID is valid");
    let mut heads: Vec<Cid> = l.heads.iter().map(cid).collect();
    let mut links: Vec<Link<'_>> = l.links.iter().map(|(c, n)| Link { name: n, cid: cid(c) }).collect();
    let mut parts = BlockParts {
        delta: &l.delta,
        heads: &mut heads,
        links: &mut links,
        encryption: l.encryption.as_ref().map(cid),
        signature: l.signature.as_ref().map(cid),
    };
    let n = parts.encoded_len();
    let mut out = vec![0u8; n];
    let written = encode_block(&mut out, &mut parts)?;
    assert_eq!(written, n, "encoded_len is not the size encode_block writes");
    Ok(out)
}

/// One value of a hand-built block map: proper, `null`, an empty array, or a stray item.
fn block_value(g: &mut Source, e: &mut Encoder<'_>, key: &str) {
    let shape = g.int(0u8..=9);
    match (key, shape) {
        (_, 9) => e.unsigned(7).expect("fits"),
        ("delta", _) => {
            let d = delta_gen(g);
            let mut dec = Decoder::new(&d);
            write_item(&mut dec, e);
        },
        ("heads", 0) | ("links", 0) | ("signature", 0) | ("encryption", 0) => e.null().expect("fits"),
        ("heads", 1) | ("links", 1) => e.array(0).expect("fits"),
        ("heads", _) => {
            let mut hs: Vec<Cid> = (0..g.int(1usize..=4)).map(|_| cid_gen(g)).collect();
            hs.sort_by(Cid::cmp_text);
            if g.bool_with(0.15) {
                hs.reverse();
            }
            e.array(hs.len() as u64).expect("fits");
            for h in &hs {
                e.tag_cid(h.as_bytes()).expect("fits");
            }
        },
        ("links", _) => {
            let mut ls: Vec<(Cid, &str)> =
                (0..g.int(1usize..=4)).map(|_| (cid_gen(g), *g.pick(&["", "a", "b", "ab", "é"]))).collect();
            ls.sort_by(|a, b| a.0.cmp_text(&b.0).then_with(|| a.1.cmp(b.1)));
            e.array(ls.len() as u64).expect("fits");
            for (c, name) in &ls {
                let extra = g.bool_with(0.1);
                let mut k = e.ordered_map(if extra { 3 } else { 2 }).expect("fits");
                k.key(e, "link").expect("fits");
                e.tag_cid(c.as_bytes()).expect("fits");
                k.key(e, "name").expect("fits");
                e.text(name).expect("fits");
                if extra {
                    k.key(e, "other").expect("fits");
                    e.null().expect("fits");
                }
            }
        },
        ("signature", _) | ("encryption", _) => e.tag_cid(cid_gen(g).as_bytes()).expect("fits"),
        _ => e.bytes(&[1, 2]).expect("fits"),
    }
}

/// Copy one item from `dec` to `e`.
fn write_item(dec: &mut Decoder<'_>, e: &mut Encoder<'_>) {
    let mut pending = 1u64;
    while pending > 0 {
        pending -= 1;
        match dec.next_item().expect("a valid delta") {
            Item::Unsigned(n) => e.unsigned(n),
            Item::Negative(n) => e.negative(n),
            Item::Bytes(b) => e.bytes(b),
            Item::Text(t) => e.text(t),
            Item::Array(n) => {
                pending += n;
                e.array(n)
            },
            Item::Map(n) => {
                pending += 2 * n;
                e.map(n)
            },
            Item::Tag(_) => match dec.next_item().expect("a valid delta") {
                Item::Bytes([0, c @ ..]) => e.tag_cid(c),
                _ => unreachable!("the decoder checks tag content"),
            },
            Item::Bool(b) => e.bool(b),
            Item::Null => e.null(),
            Item::Float(f) => e.float(f),
        }
        .expect("fits");
    }
}

/// A block as bytes: from `encode_block`, or a hand-built map with optional keys, unknown keys, nulls and empty
/// arrays; then edited 60% of the time.
fn block_bytes() -> BoxGen<Vec<u8>> {
    (|g: &mut Source| {
        let mut out = if g.bool() {
            let l = Logical {
                delta: delta_gen(g),
                heads: (0..g.int(0usize..=3)).map(|_| cid_gen(g).as_bytes().to_vec()).collect(),
                links: (0..g.int(0usize..=3))
                    .map(|_| (cid_gen(g).as_bytes().to_vec(), g.pick(&["", "a", "b", "x"]).to_string()))
                    .collect(),
                signature: g.bool().then(|| cid_gen(g).as_bytes().to_vec()),
                encryption: g.bool().then(|| cid_gen(g).as_bytes().to_vec()),
            };
            encode_logical(&l).unwrap_or_default()
        } else {
            let mut keys: Vec<&str> = ["delta", "heads", "links", "signature", "encryption", "a", "zzzzz", "zzzzzzzzzzzz"]
                .into_iter()
                .filter(|k| if *k == "delta" { g.bool_with(0.95) } else { g.bool_with(0.4) })
                .collect();
            keys.sort_by(|a, b| (a.len(), a.as_bytes()).cmp(&(b.len(), b.as_bytes())));
            let mut buf = vec![0u8; 4096];
            let mut e = Encoder::new(&mut buf);
            let mut mk = e.ordered_map(keys.len() as u64).expect("fits");
            for k in &keys {
                mk.key(&mut e, k).expect("fits");
                block_value(g, &mut e, k);
            }
            e.written().to_vec()
        };
        if g.bool_with(0.6) {
            for _ in 0..g.int(1u8..=2) {
                out = mangle(g, &out);
            }
        }
        out
    })
    .with_shrink(shrink_bytes)
    .boxed()
}

/// Whether a block uses none of the tolerated non-canonical forms: only the five known keys (two in a link), no
/// `null`, no empty array. Such a block's canonical form is its own bytes.
fn plain_block(bytes: &[u8]) -> bool {
    fn walk(bytes: &[u8]) -> Result<bool, pinc_wire::WireError> {
        let mut d = Decoder::new(bytes);
        let mut m = MapReader::new(&mut d)?;
        while let Some(k) = m.next_key(&mut d)? {
            let mut probe = d;
            let first = probe.next_item()?;
            match (k, first) {
                ("delta", _) => d.skip_value()?,
                ("heads" | "links", Item::Array(0)) | (_, Item::Null) => return Ok(false),
                ("heads", _) | ("signature" | "encryption", _) => d.skip_value()?,
                ("links", Item::Array(n)) => {
                    d.next_item()?;
                    for _ in 0..n {
                        let mut lm = MapReader::new(&mut d)?;
                        if lm.remaining() != 2 {
                            return Ok(false);
                        }
                        while let Some(lk) = lm.next_key(&mut d)? {
                            if lk != "link" && lk != "name" {
                                return Ok(false);
                            }
                            d.skip_value()?;
                        }
                    }
                },
                _ => return Ok(false),
            }
        }
        Ok(true)
    }
    walk(bytes).unwrap_or(false)
}

/// An accepted block re-encodes to a block that says the same and is its own canonical form; a block in plain
/// canonical form re-encodes to its own bytes.
#[ephyra::test(gen = block_bytes(), tests = 20_000)]
fn accepted_blocks_re_encode_canonically(input: Vec<u8>) {
    let Ok(block) = BlockRef::parse(&input) else { return };
    let l = logical(&block);
    let again = encode_logical(&l);
    let again = again.unwrap_or_else(|e| panic!("an accepted block does not re-encode: {e:?}"));
    let reparsed = BlockRef::parse(&again).unwrap_or_else(|e| panic!("a re-encoded block does not parse: {e:?}"));
    assert_eq!(logical(&reparsed), l, "the re-encoded block says something else");
    if plain_block(&input) {
        assert!(again == input, "a plain canonical block re-encodes to other bytes: {again:02x?}");
    }
}

/// `encode_block` with a too-small buffer refuses and writes nothing.
#[ephyra::test(gen = block_bytes(), tests = 5_000)]
fn encode_block_refuses_a_short_buffer_untouched(input: Vec<u8>) {
    let Ok(block) = BlockRef::parse(&input) else { return };
    let l = logical(&block);
    let Ok(full) = encode_logical(&l) else { return };
    let cid = |b: &Vec<u8>| Cid::from_bytes(b).expect("valid");
    let mut heads: Vec<Cid> = l.heads.iter().map(cid).collect();
    let mut links: Vec<Link<'_>> = l.links.iter().map(|(c, n)| Link { name: n, cid: cid(c) }).collect();
    let mut parts = BlockParts {
        delta: &l.delta,
        heads: &mut heads,
        links: &mut links,
        encryption: l.encryption.as_ref().map(cid),
        signature: l.signature.as_ref().map(cid),
    };
    let short = full.len() - 1;
    let mut out = vec![0x5au8; short];
    assert!(encode_block(&mut out, &mut parts).is_err());
    assert!(out.iter().all(|&b| b == 0x5a), "a refused encode_block wrote into the buffer");
}

// ---------------------------------------------------------------------------------------------------------------
// CAR archives.

fn car_bytes() -> BoxGen<(Vec<u8>, usize)> {
    (|g: &mut Source| {
        let roots: Vec<Cid> = (0..g.int(0usize..=3)).map(|_| cid_gen(g)).collect();
        let blocks: Vec<Vec<u8>> = (0..g.int(0usize..=4)).map(|_| delta_gen(g)).collect();
        let size = CarWriter::header_len(&roots)
            + blocks.iter().map(|b| CarWriter::section_len(Cid::for_block(DAG_CBOR, SHA2_256, b).expect("ok").as_ref(), b)).sum::<usize>();
        let mut buf = vec![0u8; size];
        let mut w = CarWriter::new(&mut buf, &roots).expect("sized");
        for b in &blocks {
            let cid = if g.bool_with(0.9) { Cid::for_block(DAG_CBOR, SHA2_256, b).expect("ok") } else { cid_gen(g) };
            if w.section(cid.as_ref(), b).is_err() {
                break;
            }
        }
        let mut out = w.written().to_vec();
        if g.bool_with(0.6) {
            for _ in 0..g.int(1u8..=2) {
                out = mangle(g, &out);
            }
        }
        let max = *g.pick(&[8usize, 40, 100, 1 << 20]);
        (out, max)
    })
    .with_shrink(|c: &(Vec<u8>, usize), visit: &mut dyn FnMut((Vec<u8>, usize)) -> ControlFlow<()>| {
        shrink_bytes(&c.0, &mut |b| visit((b, c.1)))
    })
    .boxed()
}

#[derive(Debug, PartialEq)]
enum Outcome {
    Complete,
    Truncated,
    Failed(CarError),
}

/// The streamed decoder, fed by the contract (append exactly what `NeedMore` asks), and the whole-buffer reader agree
/// on the roots, every section and how the input ends; `NeedMore` never asks for zero bytes.
#[ephyra::test(gen = car_bytes(), tests = 20_000)]
fn car_decoder_agrees_with_the_reader(case: (Vec<u8>, usize)) {
    let (input, max) = case;
    for verify in [false, true] {
        // The reader.
        let mut r_items: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        let (r_roots, r_end) = match CarReader::new(&input, max) {
            Err(CarError::Truncated { .. }) => (None, Outcome::Truncated),
            Err(e) => (None, Outcome::Failed(e)),
            Ok(reader) => {
                let reader = reader.with_verify(verify);
                let roots: Vec<Vec<u8>> = reader.roots().map(|c| c.as_bytes().to_vec()).collect();
                let mut end = Outcome::Complete;
                for s in reader.sections() {
                    match s {
                        Ok((cid, block)) => r_items.push((cid.as_bytes().to_vec(), block.to_vec())),
                        Err(CarError::Truncated { .. }) => end = Outcome::Truncated,
                        Err(e) => end = Outcome::Failed(e),
                    }
                }
                (Some(roots), end)
            },
        };
        // The decoder.
        let mut dec = CarDecoder::new(max).with_verify(verify);
        let (mut start, mut avail) = (0usize, 0usize);
        let mut d_roots = None;
        let mut d_items: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
        let mut d_end = None;
        for _ in 0..=2 * input.len() + 4 {
            match dec.decode(&input[start..avail]) {
                Ok(Decoded::NeedMore(n)) => {
                    assert!(n > 0, "NeedMore(0) would never end");
                    if avail == input.len() {
                        d_end = Some(if avail == start && d_roots.is_some() { Outcome::Complete } else { Outcome::Truncated });
                        break;
                    }
                    avail = (avail + n).min(input.len());
                },
                Ok(Decoded::Header { consumed, roots }) => {
                    d_roots = Some(roots.map(|c: CidRef<'_>| c.as_bytes().to_vec()).collect::<Vec<_>>());
                    start += consumed;
                },
                Ok(Decoded::Section { consumed, cid, block }) => {
                    d_items.push((cid.as_bytes().to_vec(), block.to_vec()));
                    start += consumed;
                },
                Err(e) => {
                    d_end = Some(Outcome::Failed(e));
                    break;
                },
            }
            assert!(start <= avail);
        }
        let d_end = d_end.expect("the decoder loop ended");
        assert_eq!(d_roots, r_roots, "roots differ (verify {verify})");
        assert_eq!(d_items, r_items, "sections differ (verify {verify})");
        assert_eq!(d_end, r_end, "the end differs (verify {verify})");
    }
}
