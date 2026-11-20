//! Trace generation for the byte formats of the node's delay-tolerant layer: the resume records of `dtn_save.rs` (a
//! delivered bundle, a held bundle, a partial bundle and its runs) and the frames of `dtn_wire.rs`, written and read
//! by the node's own code (`pinc-node`, built with the `trace` feature, through `dtn_save_probe` and
//! `dtn_wire_probe`), recorded as ndjson (`dtn_codec_node.ndjson`) for the TLA+ trace check
//! (`TraceNodeDtnCodec.tla`).
//!
//! Records are written for real signed heads of every identity algorithm and read back; every proper prefix (a
//! sample of them for the long records), every changed byte (a sample for the long records) and a byte added are
//! read; runs are checked and taken for every pair of edge offsets, torn at several cuts and overlapping. Frames
//! are written for every type and the body lengths around the cap, and parsed whole, cut and followed by more bytes;
//! the readers of a `u64` and a `u16` take every length of input. Seeded random byte strings go to every reader.
//!
//! The test checks, without the model: every record written is read back as written, a received record is 10 bytes
//! and a held one `48 + head`, every prefix of a held or received record is refused, a partial prefix inside the
//! head is refused and one inside the runs keeps exactly the whole runs before the cut, a changed version, kind,
//! custody byte, unknown algorithm tag or head byte is refused, `check` true implies `take` is `Some`, the buffer
//! `take` returns holds each run's bytes at its place and zeros elsewhere, and a frame is taken exactly when it is
//! whole. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    unreachable_pub,
    clippy::manual_is_multiple_of,
    clippy::needless_pass_by_value,
    clippy::range_plus_one
)]

mod dtn_common;

use std::collections::BTreeSet;

use dtn_common::{ALGS, bytes, keypair, make, plan, recipient};
use pinc_crypto::IdentityAlg;
use pinc_dtn::head::SignedHead;
use pinc_node::dtn_save_probe::{self as save, Read};
use pinc_node::dtn_wire_probe as wire;
use pinc_tests::{SplitMix64, trace_cases};

/// A run: `a..b` and its bytes.
type Run = (u64, u64, Vec<u8>);

fn arr(b: &[u8]) -> String {
    let parts: Vec<String> = b.iter().map(ToString::to_string).collect();
    format!("[{}]", parts.join(","))
}

fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn line(out: &mut String, s: &str) {
    out.push_str(s);
    out.push('\n');
}

fn enc(s: &SignedHead) -> Vec<u8> {
    let mut v = vec![0; s.encoded_len()];
    s.encode(&mut v).unwrap();
    v
}

fn runs_json(runs: &[Run]) -> String {
    let parts: Vec<String> = runs
        .iter()
        .map(|(a, b, d)| format!("[{},{},{}]", limbs(*a), limbs(*b), arr(d)))
        .collect();
    format!("[{}]", parts.join(","))
}

fn refs(runs: &[Run]) -> Vec<(u64, u64, &[u8])> {
    runs.iter().map(|(a, b, d)| (*a, *b, d.as_slice())).collect()
}

/// A head with what the runs of its bundle depend on.
struct Head {
    signed: SignedHead,
    alg: IdentityAlg,
    total: u64,
    g: u64,
    seed: u64,
}

fn heads(out: &mut String) -> Vec<Head> {
    let mut v = Vec::new();
    for alg in ALGS {
        for (seed, p, len) in [
            (1u64, plan(1, 0, 0), 300),
            (2, plan(1, 0, 0), 300),
            (3, plan(1, 0, 0), 300),
            (4, plan(4, 2, 0), 5000),
        ] {
            let s = make(
                &keypair(alg, seed),
                &recipient(alg, seed + 10, 1),
                p,
                &bytes(seed, len),
                seed,
            )
            .signed;
            let (total, g) = save::layout(&s).unwrap();
            assert!(total < 1 << 30);
            line(
                out,
                &format!("{{\"t\":\"dcodec\",\"op\":\"head\",\"h\":{}}}", arr(&enc(&s))),
            );
            v.push(Head {
                signed: s,
                alg,
                total,
                g,
                seed,
            });
        }
    }
    v
}

fn res_json(r: Option<&Read>) -> String {
    match r {
        None => r#"{"ok":false,"k":"err"}"#.to_string(),
        Some(Read::Received { expires }) => {
            format!("{{\"ok\":true,\"k\":\"received\",\"expires\":{}}}", limbs(*expires))
        }
        Some(Read::Held {
            copies,
            custody,
            alg,
            key,
            bytes,
            signed,
        }) => format!(
            "{{\"ok\":true,\"k\":\"held\",\"copies\":{copies},\"custody\":{custody},\"alg\":{alg},\"key\":{},\"bytes\":{},\"head\":{}}}",
            arr(key),
            limbs(*bytes),
            arr(&enc(signed))
        ),
        Some(Read::Partial { signed, runs }) => {
            format!(
                "{{\"ok\":true,\"k\":\"partial\",\"head\":{},\"runs\":{}}}",
                arr(&enc(signed)),
                arr(runs)
            )
        }
    }
}

fn read(out: &mut String, b: &[u8]) -> Option<Read> {
    let r = save::read(b);
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"read\",\"b\":{},\"r\":{}}}",
            arr(b),
            res_json(r.as_ref())
        ),
    );
    r
}

fn w_received(out: &mut String, expires: u64) -> Vec<u8> {
    let b = save::received(expires);
    assert_eq!(b.len(), 10);
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"received\",\"expires\":{},\"b\":{}}}",
            limbs(expires),
            arr(&b)
        ),
    );
    b
}

fn w_held(
    out: &mut String,
    copies: u16,
    custody: bool,
    alg: IdentityAlg,
    key: [u8; 32],
    by: u64,
    h: &SignedHead,
) -> Vec<u8> {
    let b = save::held(copies, custody, alg, key, by, h).unwrap();
    assert_eq!(b.len(), 48 + h.encoded_len(), "a held record is 48 bytes and the head");
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"held\",\"copies\":{copies},\"custody\":{custody},\"alg\":{},\"key\":{},\"bytes\":{},\"head\":{},\"b\":{}}}",
            alg.tag(),
            arr(&key),
            limbs(by),
            arr(&enc(h)),
            arr(&b)
        ),
    );
    b
}

fn w_partial(out: &mut String, h: &SignedHead, runs: &[Run]) -> Vec<u8> {
    let b = save::partial(h, &refs(runs)).unwrap();
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"partial\",\"head\":{},\"runs\":{},\"b\":{}}}",
            arr(&enc(h)),
            runs_json(runs),
            arr(&b)
        ),
    );
    b
}

fn w_append(out: &mut String, runs: &[Run]) -> Vec<u8> {
    let b = save::append(&refs(runs));
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"append\",\"runs\":{},\"b\":{}}}",
            runs_json(runs),
            arr(&b)
        ),
    );
    b
}

/// `check_runs` and `take_runs` of `b` for the bundle of `h`, recorded.
fn chk(out: &mut String, h: &Head, b: &[u8]) -> (bool, Option<(Vec<u8>, Vec<u64>, usize)>) {
    let c = save::check_runs(b, h.total, h.g);
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"check\",\"b\":{},\"total\":{},\"slice\":{},\"r\":{c}}}",
            arr(b),
            limbs(h.total),
            limbs(h.g)
        ),
    );
    let t = save::take_runs(&h.signed, b);
    let (ok, rest, held) = t
        .as_ref()
        .map_or((false, 0, Vec::new()), |(_, held, rest)| (true, *rest, held.clone()));
    let held_json = format!(
        "[{}]",
        held.iter().map(ToString::to_string).collect::<Vec<_>>().join(",")
    );
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"take\",\"b\":{},\"total\":{},\"slice\":{},\"ok\":{ok},\"rest\":{rest},\"held\":{held_json}}}",
            arr(b),
            limbs(h.total),
            limbs(h.g)
        ),
    );
    if c {
        assert!(t.is_some(), "check_runs accepted runs that take_runs refused: {b:?}");
    }
    (c, t)
}

/// The buffer and the slices held after taking `runs` in order, as a reader should leave them.
fn expect(runs: &[Run], total: u64, g: u64) -> (Vec<u8>, Option<Vec<u64>>) {
    let mut sealed = vec![0u8; total as usize];
    let mut held = BTreeSet::new();
    let mut aligned = true;
    for (a, b, d) in runs {
        if a < b && *b <= total && d.len() as u64 == b - a {
            sealed[*a as usize..*b as usize].copy_from_slice(d);
            aligned &= a % g == 0 && b % g == 0;
            held.extend(a / g..b / g);
        }
    }
    (sealed, aligned.then(|| held.into_iter().collect()))
}

/// The runs `runs` followed by the torn bytes `tail`, checked and taken; `must` when the bytes are good.
fn runs_case(out: &mut String, h: &Head, runs: &[Run], tail: &[u8], must: bool) {
    let mut b = save::append(&refs(runs));
    b.extend_from_slice(tail);
    let (c, t) = chk(out, h, &b);
    if let Some((sealed, held, rest)) = &t {
        let (want, want_held) = expect(runs, h.total, h.g);
        assert_eq!(*sealed, want, "the buffer of {} runs", runs.len());
        assert_eq!(*rest, tail.len(), "the torn tail");
        if let Some(w) = want_held {
            assert_eq!(*held, w, "the slices held");
        }
    }
    if must {
        assert!(c && t.is_some(), "good runs were refused");
    }
}

fn run_of(h: &Head, a: u64, b: u64) -> Run {
    (a, b, bytes(h.seed * 1000 + a / h.g, (b - a) as usize))
}

/// The prefix lengths to read of a record of `len` bytes: all when it is short, else the ends, a stride and the
/// neighbourhood of each of `bounds`.
fn picks(len: usize, bounds: &[usize]) -> Vec<usize> {
    if len <= 700 {
        return (0..len).collect();
    }
    let mut s = BTreeSet::new();
    // the quick profile takes every twentieth of the cuts at the ends, the stride and the bounds
    let thin = trace_cases(20, 1);
    s.extend((0..120.min(len)).step_by(thin));
    s.extend((len.saturating_sub(120)..len).step_by(thin));
    s.extend((0..len).step_by(61 * thin));
    for &b in bounds {
        s.extend((b.saturating_sub(18)..(b + 19).min(len)).step_by(thin));
    }
    s.into_iter().collect()
}

fn mut_pos(len: usize) -> Vec<usize> {
    if len <= 700 {
        return (0..len).collect();
    }
    let mut s = BTreeSet::new();
    let thin = trace_cases(20, 1);
    s.extend((0..56).step_by(thin));
    s.extend(len - 8..len);
    s.extend((0..len).step_by(211 * thin));
    s.into_iter().collect()
}

/// Records of each kind, written for every head and read back.
fn round_trips(out: &mut String, heads: &[Head], rng: &mut SplitMix64) {
    for (hi, h) in heads.iter().enumerate() {
        let he = enc(&h.signed);
        for e in [0, 1, u64::MAX, rng.next_u64()] {
            let b = w_received(out, e);
            assert!(matches!(read(out, &b), Some(Read::Received { expires }) if expires == e));
        }
        let mut cases = Vec::new();
        for (i, (c, t)) in [0u16, 1, 65535]
            .into_iter()
            .flat_map(|c| [false, true].map(|t| (c, t)))
            .enumerate()
        {
            cases.push((c, t, ALGS[(i + hi) % 4], [0, 1, u64::MAX][(i + hi) % 3]));
        }
        for alg in ALGS {
            cases.push((1, true, alg, rng.next_u64()));
        }
        for (c, t, alg, by) in cases {
            let key: [u8; 32] = bytes(rng.next_u64(), 32).try_into().unwrap();
            let b = w_held(out, c, t, alg, key, by, &h.signed);
            match read(out, &b) {
                Some(Read::Held {
                    copies,
                    custody,
                    alg: a,
                    key: k,
                    bytes: n,
                    signed,
                }) => {
                    assert_eq!((copies, custody, a, k, n), (c, t, alg.tag(), key, by));
                    assert_eq!(enc(&signed), he);
                }
                _ => panic!("a held record was not read back"),
            }
        }
        let n = h.total / h.g;
        let mut sets: Vec<Vec<Run>> = vec![Vec::new(), vec![run_of(h, 0, h.g)]];
        sets.push((0..n).map(|i| run_of(h, i * h.g, (i + 1) * h.g)).collect());
        if n >= 2 {
            sets.push((0..n / 2).map(|i| run_of(h, 2 * i * h.g, (2 * i + 2) * h.g)).collect());
        }
        for runs in &sets {
            let b = w_partial(out, &h.signed, runs);
            match read(out, &b) {
                Some(Read::Partial { signed, runs: rb }) => {
                    assert_eq!(enc(&signed), he);
                    assert_eq!(rb, save::append(&refs(runs)), "the runs of a partial record");
                }
                _ => panic!("a partial record was not read back"),
            }
            runs_case(out, h, runs, &[], true);
        }
        for runs in [
            vec![run_of(h, 0, h.g)],
            vec![run_of(h, 0, h.g), run_of(h, h.g, h.total.min(2 * h.g))],
        ] {
            if runs.iter().all(|r| r.0 < r.1) {
                w_append(out, &runs);
                runs_case(out, h, &runs, &[], true);
            }
        }
    }
}

/// Every proper prefix of a record of each kind.
fn prefixes(out: &mut String, heads: &[Head]) {
    let b = w_received(out, 12345);
    for p in 0..b.len() {
        assert!(read(out, &b[..p]).is_none(), "a received record cut at {p} was read");
    }
    for h in heads.iter().filter(|h| h.seed == 1) {
        let key = [7u8; 32];
        let b = w_held(out, 3, true, h.alg, key, 777, &h.signed);
        for p in picks(b.len(), &[]) {
            assert!(read(out, &b[..p]).is_none(), "a held record cut at {p} was read");
        }
    }
    for h in heads.iter().filter(|h| h.seed == 4) {
        let runs: Vec<Run> = (0..3).map(|i| run_of(h, i * h.g, (i + 1) * h.g)).collect();
        let rec = w_partial(out, &h.signed, &runs);
        let step = 16 + h.g as usize;
        let head_end = rec.len() - 3 * step;
        let bounds: Vec<usize> = (0..=3).map(|i| head_end + i * step).collect();
        for p in picks(rec.len(), &bounds).into_iter().chain([head_end, head_end + 16]) {
            let r = read(out, &rec[..p]);
            if p < head_end {
                assert!(r.is_none(), "a partial record cut inside its head at {p} was read");
                continue;
            }
            let Some(Read::Partial { runs: rb, .. }) = r else {
                panic!("a partial record cut in its runs at {p} was refused");
            };
            assert_eq!(rb, rec[head_end..p]);
            let whole = (p - head_end) / step;
            let tail = &rec[head_end + whole * step..p];
            runs_case(out, h, &runs[..whole], tail, true);
            if !tail.is_empty() {
                let cut = &rec[..head_end + whole * step];
                match read(out, cut) {
                    Some(Read::Partial { runs: rb, .. }) => assert_eq!(rb, save::append(&refs(&runs[..whole]))),
                    _ => panic!("a partial record cut at a run was refused"),
                }
                let mut again = cut.to_vec();
                again.extend_from_slice(&save::append(&refs(&runs[whole..])));
                assert_eq!(
                    again, rec,
                    "appending the runs after the cut did not give the record back"
                );
            }
        }
    }
}

/// One byte of a record changed, and one added.
fn mutations(out: &mut String, rec: &[u8], kind: u8, head: Option<std::ops::Range<usize>>) {
    for pos in mut_pos(rec.len()) {
        let old = rec[pos];
        let mut vals: Vec<u8> = if rec.len() <= 700 {
            vec![0, 1, 2, 3, 5, 255]
        } else {
            vec![0, 255]
        };
        vals.push(old ^ 0x80);
        vals.sort_unstable();
        vals.dedup();
        for v in vals.into_iter().filter(|v| *v != old) {
            let mut m = rec.to_vec();
            m[pos] = v;
            let r = read(out, &m);
            let refused = pos < 2
                || (kind == 0 && pos == 4 && v > 1)
                || (kind == 0 && pos == 5 && IdentityAlg::from_tag(v).is_none())
                || head.as_ref().is_some_and(|h| h.contains(&pos));
            assert!(
                !refused || r.is_none(),
                "kind {kind}: byte {pos} changed to {v} was read"
            );
        }
    }
    let mut m = rec.to_vec();
    m.push(0);
    let r = read(out, &m);
    assert!(
        kind == 1 || r.is_none(),
        "a byte added to a record of kind {kind} was read"
    );
}

fn changed(out: &mut String, heads: &[Head]) {
    let b = w_received(out, 0x0102_0304_0506_0708);
    mutations(out, &b, 2, None);
    for h in heads.iter().filter(|h| h.seed == 1) {
        let b = w_held(out, 5, true, h.alg, [9u8; 32], 4242, &h.signed);
        mutations(out, &b, 0, Some(48..b.len()));
        let rec = w_partial(out, &h.signed, &[run_of(h, 0, h.g)]);
        let head_end = rec.len() - 16 - h.g as usize;
        mutations(out, &rec, 1, Some(4..head_end));
    }
}

/// Runs with header offsets from the edges, torn runs, overlapping and repeated runs.
fn runs(out: &mut String, h: &Head) {
    let (t, g) = (h.total, h.g);
    let v: BTreeSet<u64> = [0, 1, g - 1, g, 2 * g, t - g, t, t + 1, u64::MAX].into_iter().collect();
    for &a in &v {
        for &b in &v {
            let d = if a < b && b <= t {
                bytes(h.seed + a, (b - a) as usize)
            } else {
                Vec::new()
            };
            let r = (a, b, d);
            runs_case(out, h, std::slice::from_ref(&r), &[], false);
            runs_case(out, h, &[run_of(h, 0, g), r], &[], false);
        }
    }
    let good = save::append(&[(g, 2 * g, run_of(h, g, 2 * g).2.as_slice())]);
    for cut in [1, 7, 8, 9, 15, 16, good.len() - 1] {
        runs_case(out, h, &[], &good[..cut], true);
        runs_case(out, h, &[run_of(h, 0, g)], &good[..cut], true);
    }
    let (r0, r1, r2) = (run_of(h, 0, g), run_of(h, g, 2 * g), run_of(h, 0, 2 * g));
    for set in [
        vec![r0.clone(), r0.clone()],
        vec![r2.clone(), r1.clone()],
        vec![r1.clone(), r0.clone()],
        vec![r0, r1, r2],
    ] {
        runs_case(out, h, &set, &[], false);
    }
}

fn frames(out: &mut String) {
    let max = wire::BODY_MAX;
    for ty in [1u8, 2, 3, 4, 5, 0, 255] {
        for n in [0, 1, 16, 1000, max - 1, max, max + 1] {
            let body = vec![0xabu8; n];
            let f = wire::frame(ty, &body);
            assert_eq!(f.len(), 5 + n);
            assert_eq!(f[5..], body[..]);
            line(
                out,
                &format!(
                    "{{\"t\":\"dcodec\",\"op\":\"frame\",\"ty\":{ty},\"body\":{n},\"b\":{}}}",
                    arr(&f[..5])
                ),
            );
            let mut longer = f.clone();
            longer.extend_from_slice(&[1, 2, 3, 4, 5, 6, 7]);
            let cases: [(&[u8], usize); 8] = [
                (&f[..], f.len()),
                (&longer[..f.len() + 1], f.len() + 1),
                (&longer[..], f.len() + 7),
                (&f[..0], 0),
                (&f[..1], 1),
                (&f[..4], 4),
                (&f[..5], 5),
                (&f[..f.len() - 1], f.len() - 1),
            ];
            for (inb, len) in cases {
                let r = next(out, inb);
                assert_eq!(inb.len(), len);
                let want = if len < 5 {
                    Ok(None)
                } else if n > max {
                    Err(())
                } else if len >= 5 + n {
                    Ok(Some((ty, 5 + n)))
                } else {
                    Ok(None)
                };
                assert_eq!(r, want, "next on a frame of type {ty}, body {n}, input {len} bytes");
            }
        }
    }
    for announced in [1u32 << 24, 1 << 31, u32::MAX] {
        for len in [5, 6] {
            let mut inb = vec![3u8];
            inb.extend_from_slice(&announced.to_be_bytes());
            inb.resize(len, 0);
            assert_eq!(next(out, &inb), Err(()), "a body of {announced} bytes was announced");
        }
    }
}

fn next(out: &mut String, inb: &[u8]) -> Result<Option<(u8, usize)>, ()> {
    let r = wire::next(inb);
    let res = match r {
        Ok(None) => r#"{"k":"none","ty":0,"n":0}"#.to_string(),
        Err(()) => r#"{"k":"err","ty":0,"n":0}"#.to_string(),
        Ok(Some((ty, n))) => {
            assert!(n <= inb.len(), "next returned a length past the input");
            format!("{{\"k\":\"ok\",\"ty\":{ty},\"n\":{n}}}")
        }
    };
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"next\",\"h\":{},\"len\":{},\"r\":{res}}}",
            arr(&inb[..inb.len().min(5)]),
            inb.len()
        ),
    );
    r
}

fn take_u64(out: &mut String, s: &[u8]) {
    let r = wire::take_u64(s);
    let (ok, v, rest) = r.map_or((false, 0, 0), |(v, rest)| (true, v, rest));
    assert_eq!(r.is_some(), s.len() >= 8);
    if let Some((v, rest)) = r {
        assert_eq!(v.to_be_bytes()[..], s[..8]);
        assert_eq!(rest, s.len() - 8);
    }
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"u64\",\"s\":{},\"ok\":{ok},\"v\":{},\"rest\":{rest}}}",
            arr(s),
            limbs(v)
        ),
    );
}

fn take_u16(out: &mut String, s: &[u8]) {
    let r = wire::take_u16(s);
    let (ok, v, rest) = r.map_or((false, 0, 0), |(v, rest)| (true, v, rest));
    assert_eq!(r.is_some(), s.len() >= 2);
    if let Some((v, rest)) = r {
        assert_eq!(v.to_be_bytes()[..], s[..2]);
        assert_eq!(rest, s.len() - 2);
    }
    line(
        out,
        &format!(
            "{{\"t\":\"dcodec\",\"op\":\"u16\",\"s\":{},\"ok\":{ok},\"v\":{v},\"rest\":{rest}}}",
            arr(s)
        ),
    );
}

fn readers(out: &mut String) {
    for v in [0u64, 1, 255, 256, u64::MAX] {
        for extra in [0, 3] {
            let mut s = v.to_be_bytes().to_vec();
            s.extend(std::iter::repeat_n(0x5a, extra));
            take_u64(out, &s);
        }
    }
    for v in [0u16, 1, 255, 256, 65535] {
        for extra in [0, 3] {
            let mut s = v.to_be_bytes().to_vec();
            s.extend(std::iter::repeat_n(0x5a, extra));
            take_u16(out, &s);
        }
    }
    for len in 0..8 {
        take_u64(out, &bytes(len as u64 + 1, len));
    }
    for len in 0..2 {
        take_u16(out, &bytes(len as u64 + 20, len));
    }
}

fn random(out: &mut String, h: &Head) {
    let mut rng = SplitMix64::new(0x6e64_6300);
    for _ in 0..trace_cases(300, 3000) {
        let mut b = vec![0u8; (rng.next_u64() % 120) as usize];
        rng.fill(&mut b);
        if rng.next_u64() % 2 == 0 && b.len() >= 2 {
            b[0] = 2;
            b[1] = (rng.next_u64() % 4) as u8;
        }
        read(out, &b);
    }
    for _ in 0..trace_cases(100, 1000) {
        let mut b = vec![0u8; (rng.next_u64() % 120) as usize];
        rng.fill(&mut b);
        if rng.next_u64() % 2 == 0 && b.len() >= 16 {
            b[..8].copy_from_slice(&0u64.to_be_bytes());
            b[8..16].copy_from_slice(&h.g.to_be_bytes());
        }
        chk(out, h, &b);
    }
    for _ in 0..trace_cases(100, 1000) {
        let mut b = vec![0u8; (rng.next_u64() % 12) as usize];
        rng.fill(&mut b);
        let _ = next(out, &b);
        take_u64(out, &b);
        take_u16(out, &b);
    }
}

#[test]
fn node_dtn_codec() {
    let mut out = String::new();
    let hs = heads(&mut out);
    let mut rng = SplitMix64::new(0x6e64_6301);
    round_trips(&mut out, &hs, &mut rng);
    prefixes(&mut out, &hs);
    changed(&mut out, &hs);
    runs(&mut out, hs.iter().find(|h| h.seed == 4).unwrap());
    frames(&mut out);
    readers(&mut out);
    random(&mut out, hs.iter().find(|h| h.seed == 4).unwrap());
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dtn_codec_node.ndjson"), &out).unwrap();
    }
}
