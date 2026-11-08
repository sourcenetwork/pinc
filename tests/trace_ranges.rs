//! Trace generation for the proofs: seeded random runs of the verified-range sets, the varint codec and the tree
//! layout, written as ndjson for the TLA+ trace check and the Lean replay.
//!
//! Every run is also checked here against a naive reference, so the test is meaningful without the proof tools.
//! The files are written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines
)]

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::ops::Range;

use vinc_dag::ranges::{VerifiedRanges, VerifiedRangesVec};
use vinc_dag::tree::{Layout, TreeError};
use vinc_tests::SplitMix64;
use vinc_wire::{WireError, varint};

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn json_pairs(items: &[Range<u64>]) -> String {
    let body: Vec<String> = items.iter().map(|r| format!("[{},{}]", r.start, r.end)).collect();
    format!("[{}]", body.join(","))
}

fn json_bytes(bytes: &[u8]) -> String {
    let body: Vec<String> = bytes.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// The number of maximal runs of consecutive offsets in `set`.
fn runs(set: &BTreeSet<u64>) -> usize {
    set.iter().filter(|&&x| x == 0 || !set.contains(&(x - 1))).count()
}

/// The operations the trace records, shared by the fixed-capacity and the `Vec` sets.
trait Set {
    fn insert(&mut self, r: Range<u64>) -> bool;
    fn contains(&self, x: u64) -> bool;
    fn contains_range(&self, r: Range<u64>) -> bool;
    fn covered_len(&self) -> u64;
    fn items(&self) -> Vec<Range<u64>>;
}

impl<const N: usize> Set for VerifiedRanges<N> {
    fn insert(&mut self, r: Range<u64>) -> bool {
        VerifiedRanges::insert(self, r).is_ok()
    }
    fn contains(&self, x: u64) -> bool {
        VerifiedRanges::contains(self, x)
    }
    fn contains_range(&self, r: Range<u64>) -> bool {
        VerifiedRanges::contains_range(self, r)
    }
    fn covered_len(&self) -> u64 {
        VerifiedRanges::covered_len(self)
    }
    fn items(&self) -> Vec<Range<u64>> {
        self.iter().collect()
    }
}

impl Set for VerifiedRangesVec {
    fn insert(&mut self, r: Range<u64>) -> bool {
        VerifiedRangesVec::insert(self, r);
        true
    }
    fn contains(&self, x: u64) -> bool {
        VerifiedRangesVec::contains(self, x)
    }
    fn contains_range(&self, r: Range<u64>) -> bool {
        VerifiedRangesVec::contains_range(self, r)
    }
    fn covered_len(&self) -> u64 {
        VerifiedRangesVec::covered_len(self)
    }
    fn items(&self) -> Vec<Range<u64>> {
        self.iter().collect()
    }
}

/// Drive one set through `steps` random inserts at offsets `base..base + span`, recording each step. With
/// `check`, also compare every answer against a naive set of offsets (only for small spans).
#[allow(clippy::too_many_arguments, reason = "one call site per run kind")]
fn run_set<S: Set>(
    set: &mut S,
    cap: Option<usize>,
    rng: &mut SplitMix64,
    out: &mut String,
    run: usize,
    base: u64,
    span: u64,
    steps: usize,
    check: bool,
) {
    let kind = if cap.is_some() { "fixed" } else { "vec" };
    let mut model: BTreeSet<u64> = BTreeSet::new();
    for seq in 0..steps {
        let a = base + below(rng, span);
        let len = match below(rng, 8) {
            0 => 0,
            1 => span,
            _ => below(rng, span / 3 + 1),
        };
        // One in ten ranges is reversed: the code treats it as empty.
        let range = if below(rng, 10) == 0 {
            a..a.saturating_sub(len)
        } else {
            a..a.saturating_add(len)
        };
        let before = set.items();
        let ok = set.insert(range.clone());
        if check {
            let mut grown = model.clone();
            if range.start < range.end {
                grown.extend(range.clone());
            }
            match cap {
                Some(n) if range.start < range.end && runs(&grown) > n => {
                    assert!(!ok, "insert {range:?} must fail on a full set");
                    assert_eq!(set.items(), before, "a failed insert changes nothing");
                }
                _ => {
                    assert!(ok, "insert {range:?} must succeed");
                    model = grown;
                }
            }
            assert!(cap.is_none_or(|n| runs(&model) <= n));
        }
        let items = set.items();
        let x = base + below(rng, span + 2);
        let cs = base + below(rng, span);
        let ce = cs.saturating_add(below(rng, span / 2 + 1));
        let (cx, cr, cl) = (set.contains(x), set.contains_range(cs..ce), set.covered_len());
        if check {
            assert_eq!(cx, model.contains(&x));
            assert_eq!(cr, (cs..ce).all(|y| model.contains(&y)));
            assert_eq!(cl, model.len() as u64);
            let expect: Vec<Range<u64>> = {
                let mut v: Vec<Range<u64>> = Vec::new();
                for &y in &model {
                    match v.last_mut() {
                        Some(last) if last.end == y => last.end = y + 1,
                        _ => v.push(y..y + 1),
                    }
                }
                v
            };
            assert_eq!(
                items, expect,
                "the intervals are the maximal runs of the covered offsets"
            );
        }
        let n = cap.unwrap_or(0);
        let _ = writeln!(
            out,
            "{{\"run\":{run},\"kind\":\"{kind}\",\"n\":{n},\"seq\":{seq},\"s\":{},\"e\":{},\"ok\":{ok},\"items\":{},\"cl\":{cl},\"x\":{x},\"cx\":{cx},\"cs\":{cs},\"ce\":{ce},\"cr\":{cr}}}",
            range.start,
            range.end,
            json_pairs(&items),
        );
    }
}

/// Run `seeds` sequences on a `VerifiedRanges<N>`.
fn fixed_runs<const N: usize>(out: &mut String, run: &mut usize, seeds: u64, base: u64, span: u64, check: bool) {
    for seed in 0..seeds {
        let mut rng = SplitMix64::new(0x5eed_0000 + (N as u64) * 1000 + seed);
        let mut set = VerifiedRanges::<N>::new();
        run_set(&mut set, Some(N), &mut rng, out, *run, base, span, 60, check);
        *run += 1;
    }
}

fn ranges_traces() -> (String, String) {
    let (mut narrow, mut wide) = (String::new(), String::new());
    let mut run = 0;
    fixed_runs::<1>(&mut narrow, &mut run, 6, 0, 40, true);
    fixed_runs::<2>(&mut narrow, &mut run, 6, 0, 40, true);
    fixed_runs::<3>(&mut narrow, &mut run, 8, 0, 40, true);
    fixed_runs::<4>(&mut narrow, &mut run, 6, 0, 40, true);
    fixed_runs::<6>(&mut narrow, &mut run, 6, 0, 60, true);
    for seed in 0..6 {
        let mut rng = SplitMix64::new(0x7ec0_0000 + seed);
        run_set(
            &mut VerifiedRangesVec::new(),
            None,
            &mut rng,
            &mut narrow,
            run,
            0,
            50,
            60,
            true,
        );
        run += 1;
    }
    // Offsets at the top of the u64 range: no reference set, but the same recorded answers.
    let top = u64::MAX - 64;
    fixed_runs::<2>(&mut wide, &mut run, 4, top, 60, false);
    fixed_runs::<3>(&mut wide, &mut run, 4, top, 60, false);
    for seed in 0..3 {
        let mut rng = SplitMix64::new(0x71de_0000 + seed);
        run_set(
            &mut VerifiedRangesVec::new(),
            None,
            &mut rng,
            &mut wide,
            run,
            top,
            60,
            60,
            false,
        );
        run += 1;
    }
    (narrow, wide)
}

// ---------------------------------------------------------------- varint

fn err_name(e: WireError) -> &'static str {
    match e {
        WireError::VarintTooLong => "toolong",
        WireError::Truncated { needed: 1 } => "truncated",
        WireError::VarintNonMinimal => "nonminimal",
        WireError::VarintOverflow => "overflow",
        WireError::BufferTooSmall { .. } => "small",
        other => unreachable!("unexpected varint error {other:?}"),
    }
}

fn varint_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::new(0x7a41_a001);
    let mut values: Vec<u64> = vec![0, 1, 127, 128, u64::MAX, 1 << 63, (1 << 63) - 1, (1 << 62) + 1];
    for k in 1..=9u32 {
        let edge = 1u64.checked_shl(7 * k).unwrap_or(u64::MAX);
        values.extend([edge.saturating_sub(1), edge, edge.saturating_add(1)]);
    }
    for _ in 0..400 {
        let bits = below(&mut rng, 65) as u32;
        let v = if bits == 0 { 0 } else { rng.next_u64() >> (64 - bits) };
        values.push(v);
    }
    for &v in &values {
        for cap in [16usize, (below(&mut rng, 11)) as usize] {
            let mut buf = vec![0xAAu8; cap];
            let res = varint::encode(v, &mut buf);
            match res {
                Ok(n) => {
                    assert!(v < 1 << 63 && n == varint::encoded_len(v) && n <= cap);
                    assert_eq!(varint::decode(&buf[..n]), Ok((v, n)));
                    let _ = writeln!(
                        out,
                        "{{\"t\":\"venc\",\"v\":{v},\"cap\":{cap},\"ok\":{}}}",
                        json_bytes(&buf[..n])
                    );
                }
                Err(e) => {
                    let extra = if let WireError::BufferTooSmall { needed } = e {
                        format!(",\"needed\":{needed}")
                    } else {
                        String::new()
                    };
                    assert!(buf.iter().all(|&b| b == 0xAA), "an error leaves the buffer untouched");
                    let _ = writeln!(
                        out,
                        "{{\"t\":\"venc\",\"v\":{v},\"cap\":{cap},\"err\":\"{}\"{extra}}}",
                        err_name(e)
                    );
                }
            }
        }
    }
    let mut inputs: Vec<Vec<u8>> = vec![
        vec![],
        vec![0x80],
        vec![0x80, 0],
        vec![0xff; 9],
        vec![0xff; 10],
        vec![0x80; 9],
        vec![0x80; 8],
    ];
    for _ in 0..1500 {
        let len = below(&mut rng, 13) as usize;
        let mut bytes = vec![0u8; len];
        rng.fill(&mut bytes);
        // Bias towards continuation bytes so long and truncated inputs are common, and to zero tails.
        for b in &mut bytes {
            match below(&mut rng, 4) {
                0 => *b |= 0x80,
                1 => *b &= 0x7f,
                _ => {}
            }
        }
        if len > 0 && below(&mut rng, 6) == 0 {
            bytes[len - 1] = 0;
        }
        inputs.push(bytes);
    }
    for &v in values.iter().filter(|&&v| v < 1 << 63).take(80) {
        let mut buf = [0u8; 9];
        let n = varint::encode(v, &mut buf).unwrap();
        let mut bytes = buf[..n].to_vec();
        bytes.extend([0x00, 0xff, 0x80]);
        inputs.push(bytes);
    }
    for bytes in &inputs {
        match varint::decode(bytes) {
            Ok((v, n)) => {
                let _ = writeln!(
                    out,
                    "{{\"t\":\"vdec\",\"bytes\":{},\"ok\":[{v},{n}]}}",
                    json_bytes(bytes)
                );
            }
            Err(e) => {
                let _ = writeln!(
                    out,
                    "{{\"t\":\"vdec\",\"bytes\":{},\"err\":\"{}\"}}",
                    json_bytes(bytes),
                    err_name(e)
                );
            }
        }
    }
    out
}

// ---------------------------------------------------------------- layout

fn layout_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::new(0x1a70_0001);
    for _ in 0..1200 {
        let log = below(&mut rng, 21) as u32;
        let group = 1024u64 << log;
        let len = match below(&mut rng, 4) {
            0 => below(&mut rng, 3 * group),
            1 => group * below(&mut rng, 40),
            2 => rng.next_u64() >> below(&mut rng, 64),
            _ => group * below(&mut rng, 40) + 1,
        };
        let layout = Layout::new(len, log).unwrap();
        let edge = |rng: &mut SplitMix64| match below(rng, 4) {
            0 => group * below(rng, 40),
            1 => (group * below(rng, 40)).saturating_sub(1),
            2 => below(rng, len.saturating_add(group)),
            _ => len,
        };
        let (s, e) = (edge(&mut rng), edge(&mut rng));
        let head = format!(
            "\"t\":\"grange\",\"len\":{len},\"log\":{log},\"groups\":{},\"s\":{s},\"e\":{e}",
            layout.groups()
        );
        match layout.group_range(&(s..e)) {
            Ok(r) => {
                let _ = writeln!(out, "{{{head},\"ok\":[{},{}]}}", r.start, r.end);
            }
            Err(TreeError::RangeOutOfBounds) => {
                let _ = writeln!(out, "{{{head},\"err\":\"range\"}}");
            }
            Err(other) => unreachable!("unexpected layout error {other:?}"),
        }
    }
    out
}

#[test]
fn proof_traces_are_consistent_with_the_reference() {
    let (narrow, wide) = ranges_traces();
    let (varint_trace, layout_trace) = (varint_traces(), layout_traces());
    assert!(
        narrow.contains("\"ok\":false"),
        "the runs must exercise a capacity failure"
    );
    assert!(narrow.lines().count() > 2000);
    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    for (name, body) in [
        ("ranges.ndjson", narrow),
        ("ranges_wide.ndjson", wide),
        ("varint.ndjson", varint_trace),
        ("layout.ndjson", layout_trace),
    ] {
        std::fs::write(dir.join(name), body).unwrap();
    }
}
