//! Trace generation for the TLA+ specifications of the machine-integer code: the varint codec, the tree layout, the
//! range encoder and `encoded_len`.
//!
//! TLC integers are 32 bits wide, so every `u64` of these traces is written as four 16-bit limbs, least significant
//! first (`[l0,l1,l2,l3]`), which `U64.tla` reads. The real code runs on the same boundary sets the TLA+ models
//! enumerate (for every `j`, `2^j - 1`, `2^j` and `2^j + 1`, the edges of every group size, the full byte range of
//! short inputs) and on seeded random values; every result is also checked here against a naive reference, so the
//! test is meaningful without the proof tools. The files go to `tla/` under `PINC_TRACE_DIR` when it is set;
//! otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines
)]

use std::fmt::Write as _;
use std::ops::Range;

use pinc_dag::tree::{Layout, RangeEncoder, Step, TreeError, encode_range, encoded_len};
use pinc_tests::SplitMix64;
use pinc_wire::{WireError, varint};

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// A `u64` as the four 16-bit limbs `U64.tla` reads.
fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        v >> 48
    )
}

fn json_bytes(bytes: &[u8]) -> String {
    let body: Vec<String> = bytes.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// For every `j` in `0..=64`, `2^j - 1`, `2^j` and `2^j + 1` that are `u64`s: the boundary values of every width.
fn edge_values() -> Vec<u64> {
    let mut out = Vec::new();
    for j in 0..=64u32 {
        let p = 1u128 << j;
        for v in [p.wrapping_sub(1), p, p + 1] {
            if let Ok(v) = u64::try_from(v)
                && (j > 0 || v != u64::MAX)
            {
                out.push(v);
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

// ---------------------------------------------------------------- varint

fn err_name(e: WireError) -> &'static str {
    match e {
        WireError::VarintOverflow => "overflow",
        WireError::BufferTooSmall { .. } => "small",
        WireError::VarintTooLong => "toolong",
        WireError::Truncated { .. } => "truncated",
        WireError::VarintNonMinimal => "nonminimal",
        _ => "other",
    }
}

fn varint_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0x7a41_a002);
    let edges = edge_values();
    let mut values = edges.clone();
    values.extend(0..300u64);
    for _ in 0..600 {
        let bits = below(&mut rng, 65) as u32;
        values.push(if bits == 0 { 0 } else { rng.next_u64() >> (64 - bits) });
    }
    for &v in &values {
        // every buffer size for the boundary values, a few for the others
        let caps: Vec<usize> = if edges.contains(&v) {
            (0..=10).collect()
        } else {
            vec![0, below(&mut rng, 11) as usize, 16]
        };
        for cap in caps {
            let mut buf = vec![0xAAu8; cap];
            match varint::encode(v, &mut buf) {
                Ok(n) => {
                    assert!(v < 1 << 63 && n == varint::encoded_len(v) && n <= cap);
                    assert_eq!(varint::decode(&buf[..n]), Ok((v, n)));
                    let _ = writeln!(
                        out,
                        "{{\"t\":\"venc\",\"v\":{},\"cap\":{cap},\"ok\":{}}}",
                        limbs(v),
                        json_bytes(&buf[..n])
                    );
                }
                Err(e) => {
                    assert!(buf.iter().all(|&b| b == 0xAA), "an error leaves the buffer untouched");
                    let needed = if let WireError::BufferTooSmall { needed } = e {
                        format!(",\"needed\":{needed}")
                    } else {
                        String::new()
                    };
                    let _ = writeln!(
                        out,
                        "{{\"t\":\"venc\",\"v\":{},\"cap\":{cap},\"err\":\"{}\"{needed}}}",
                        limbs(v),
                        err_name(e)
                    );
                }
            }
        }
    }
    let mut inputs: Vec<Vec<u8>> = vec![vec![]];
    // every byte string of 0 to 2 bytes whose bytes are from the class alphabet of the model, and every single byte
    let alpha = [0u8, 1, 2, 64, 127, 128, 129, 192, 255];
    for b in 0..=255u8 {
        inputs.push(vec![b]);
    }
    let mut level: Vec<Vec<u8>> = vec![vec![]];
    for _ in 0..3 {
        level = level
            .iter()
            .flat_map(|s| {
                alpha.iter().map(move |&b| {
                    let mut t = s.clone();
                    t.push(b);
                    t
                })
            })
            .collect();
        inputs.extend(level.iter().cloned());
    }
    // the runs of continuation bytes, with a terminator or nothing, with and without a trailing byte
    for m in 0..=10usize {
        let runs: Vec<Vec<u8>> = if m <= 6 {
            (0..1u32 << m)
                .map(|bits| (0..m).map(|k| if bits >> k & 1 == 1 { 255 } else { 128 }).collect())
                .collect()
        } else {
            vec![vec![128; m], vec![255; m], (0..m).map(|k| [128, 255][k % 2]).collect()]
        };
        for run in runs {
            for t in [None, Some(0u8), Some(1), Some(127)] {
                for tail in [None, Some(255u8), Some(0)] {
                    let mut s = run.clone();
                    s.extend(t);
                    if t.is_some() || tail.is_none() {
                        s.extend(tail);
                    }
                    inputs.push(s);
                }
            }
        }
    }
    for _ in 0..600 {
        let len = below(&mut rng, 13) as usize;
        let mut bytes = vec![0u8; len];
        rng.fill(&mut bytes);
        for b in &mut bytes {
            match below(&mut rng, 4) {
                0 => *b |= 0x80,
                1 => *b &= 0x7f,
                _ => {}
            }
        }
        inputs.push(bytes);
    }
    // every encoding with every cut and every rest
    for &v in values.iter().filter(|&&v| v < 1 << 63).take(400) {
        let mut buf = [0u8; 9];
        let n = varint::encode(v, &mut buf).unwrap();
        for cut in 0..n {
            inputs.push(buf[..cut].to_vec());
        }
        for rest in [&[][..], &[0], &[128], &[255], &[0, 0], &[128, 128]] {
            let mut bytes = buf[..n].to_vec();
            bytes.extend_from_slice(rest);
            inputs.push(bytes);
        }
    }
    for bytes in &inputs {
        match varint::decode(bytes) {
            Ok((v, n)) => {
                let _ = writeln!(
                    out,
                    "{{\"t\":\"vdec\",\"in\":{},\"ok\":[{},{n}]}}",
                    json_bytes(bytes),
                    limbs(v)
                );
            }
            Err(e) => {
                let _ = writeln!(
                    out,
                    "{{\"t\":\"vdec\",\"in\":{},\"err\":\"{}\"}}",
                    json_bytes(bytes),
                    err_name(e)
                );
            }
        }
    }
    out
}

// ---------------------------------------------------------------- layout

/// The byte offsets of interest of a layout: the group edges, the ends and the middle of the value.
fn offsets(len: u64, group: u64) -> Vec<u64> {
    let mut v = vec![0, 1, len, len / 2, group - 1, group, group + 1];
    v.extend(len.checked_sub(1));
    v.extend(len.checked_add(1));
    v.sort_unstable();
    v.dedup();
    v
}

fn layout_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0x1a70_0a01);
    let mut cases: Vec<(u64, u32)> = Vec::new();
    for len in edge_values() {
        for log in [0u32, 1, 4, 10, 19, 20] {
            cases.push((len, log));
        }
    }
    for k in 0..=40u64 {
        for log in [0u32, 3, 20] {
            let g = 1024u64 << log;
            for d in [-1i64, 0, 1] {
                cases.push(((k * g).saturating_add_signed(d), log));
            }
        }
    }
    for _ in 0..400 {
        let bits = below(&mut rng, 65) as u32;
        let len = if bits == 0 { 0 } else { rng.next_u64() >> (64 - bits) };
        cases.push((len, below(&mut rng, 21) as u32));
    }
    for (len, log) in cases {
        let layout = Layout::new(len, log).unwrap();
        let n = layout.groups();
        let g = layout.group_len();
        // the group count, the depth and the outboard size against the naive definitions
        assert_eq!(u128::from(n), u128::from(len).div_ceil(u128::from(g)));
        assert_eq!(u128::from(layout.outboard_size()), 64 * u128::from(n.saturating_sub(1)));
        assert!(u128::from(n) <= 1u128 << layout.depth());
        let mut idx = vec![0, 1, n, n.wrapping_add(1), u64::MAX];
        idx.extend(n.checked_sub(1));
        idx.extend(n.checked_sub(2));
        let gs: Vec<String> = idx
            .iter()
            .map(|&i| format!("[{},{}]", limbs(i), limbs(layout.group_size(i))))
            .collect();
        let _ = writeln!(
            out,
            "{{\"t\":\"lay\",\"len\":{},\"log\":{log},\"groups\":{},\"depth\":{},\"ob\":{},\"gs\":[{}]}}",
            limbs(len),
            limbs(n),
            layout.depth(),
            limbs(layout.outboard_size()),
            gs.join(",")
        );
    }
    for (len, log) in [(0u64, 0u32), (1, 0), (1 << 20, 4), (u64::MAX, 20), (u64::MAX, 0)]
        .into_iter()
        .chain((0..60).map(|_| (rng.next_u64() >> below(&mut rng, 64), below(&mut rng, 21) as u32)))
    {
        let layout = Layout::new(len, log).unwrap();
        let offs = offsets(len, layout.group_len());
        for &s in &offs {
            for &e in &offs {
                let r = layout.group_range(&(s..e));
                match r {
                    Ok(r) => {
                        assert!(s <= e && e <= len);
                        let _ = writeln!(
                            out,
                            "{{\"t\":\"grange\",\"len\":{},\"log\":{log},\"s\":{},\"e\":{},\"ok\":[{},{}]}}",
                            limbs(len),
                            limbs(s),
                            limbs(e),
                            limbs(r.start),
                            limbs(r.end)
                        );
                    }
                    Err(e2) => {
                        assert_eq!(e2, TreeError::RangeOutOfBounds);
                        assert!(s > e || e > len);
                        let _ = writeln!(
                            out,
                            "{{\"t\":\"grange\",\"len\":{},\"log\":{log},\"s\":{},\"e\":{},\"err\":\"range\"}}",
                            limbs(len),
                            limbs(s),
                            limbs(e)
                        );
                    }
                }
            }
        }
    }
    let mut sizes: Vec<usize> = vec![0, 1, 1023, 1025, 3072, 2047, 2048, 5120, 1 << 40, 1 << 63];
    for k in 0..=22u32 {
        let b = 1024usize << k;
        sizes.extend([b, b - 1, b + 1, 3 * b]);
    }
    for gb in sizes {
        let r = Layout::for_group_bytes(0, gb);
        let line = match r {
            Ok(l) => format!("\"ok\":{}", l.log()),
            Err(e) => {
                assert_eq!(e, TreeError::InvalidGroupSize);
                "\"err\":\"group\"".to_string()
            }
        };
        let _ = writeln!(out, "{{\"t\":\"fgb\",\"gb\":{},{line}}}", limbs(gb as u64));
    }
    for log in 0..=70u32 {
        let ok = Layout::new(12345, log).is_ok();
        assert_eq!(ok, log <= 20);
        let _ = writeln!(out, "{{\"t\":\"new\",\"log\":{log},\"ok\":{ok}}}");
    }
    out
}

// ---------------------------------------------------------------- encoder

fn step_json(step: &Step) -> String {
    match *step {
        Step::Parent { outboard_offset } => format!("[\"p\",{}]", limbs(outboard_offset)),
        Step::Group { offset, len } => format!("[\"g\",{},{}]", limbs(offset), limbs(len)),
    }
}

/// One `enc` event: the complete step list of `RangeEncoder` for `range` of a value of `len` bytes, and the
/// `encoded_len` of it. The encoder needs only the layout, so `len` may be anything up to `u64::MAX`.
fn emit_encoder(out: &mut String, len: u64, log: u32, range: Range<u64>) {
    let layout = Layout::new(len, log).unwrap();
    let head = format!(
        "{{\"t\":\"enc\",\"len\":{},\"log\":{log},\"s\":{},\"e\":{}",
        limbs(len),
        limbs(range.start),
        limbs(range.end)
    );
    let Ok(enc) = RangeEncoder::new(layout, &range) else {
        assert!(range.start > range.end || range.end > len);
        assert_eq!(encoded_len(layout, &range), Err(TreeError::RangeOutOfBounds));
        let _ = writeln!(out, "{head},\"err\":\"range\"}}");
        return;
    };
    let steps: Vec<Step> = enc.map(|s| s.unwrap()).collect();
    let total: u128 = steps
        .iter()
        .map(|s| match s {
            Step::Parent { .. } => 64u128,
            Step::Group { len, .. } => u128::from(*len),
        })
        .sum();
    let el = match encoded_len(layout, &range) {
        Ok(n) => {
            assert_eq!(u128::from(n), total);
            format!("\"el\":{}", limbs(n))
        }
        Err(e) => {
            assert_eq!(e, TreeError::EncodedTooLong);
            assert!(total > u128::from(u64::MAX));
            "\"err\":\"toolong\"".to_string()
        }
    };
    let body: Vec<String> = steps.iter().map(step_json).collect();
    let _ = writeln!(out, "{head},{el},\"steps\":[{}]}}", body.join(","));
}

fn encoder_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0x3c0d_e901);
    // small layouts: every pair of the interesting offsets, the whole stream
    for k in 0..=12u64 {
        for log in [0u32, 1] {
            let g = 1024u64 << log;
            for d in [-1i64, 0, 1] {
                let len = (k * g).saturating_add_signed(d);
                let offs = offsets(len, g);
                for &s in &offs {
                    for &e in &offs {
                        emit_encoder(&mut out, len, log, s..e);
                    }
                }
            }
        }
    }
    // big layouts: the ranges at the start, the end and the middle of a value of up to u64::MAX bytes
    for len in edge_values() {
        for log in [0u32, 20] {
            for r in [0..1, len.saturating_sub(1)..len, len / 2..len / 2 + 1, 0..0] {
                emit_encoder(&mut out, len, log, r);
            }
        }
    }
    // random layouts of up to 2^54 groups with ranges of random size
    for _ in 0..200 {
        let log = below(&mut rng, 21) as u32;
        let bits = below(&mut rng, 65) as u32;
        let len = if bits == 0 { 0 } else { rng.next_u64() >> (64 - bits) };
        if len == 0 {
            continue;
        }
        let a = below(&mut rng, len);
        let span = 1 + below(&mut rng, (len - a).min(1 << 15));
        emit_encoder(&mut out, len, log, a..a + span);
    }
    out
}

/// `encode_range` into output buffers of every size around the stream length, with a genuine value and outboard.
fn encout_traces() -> String {
    let mut out = String::new();
    let mut rng = SplitMix64::traced(0x3c0d_e902);
    for case in 0..160u64 {
        let log = below(&mut rng, 3) as u32;
        let g = 1024u64 << log;
        let groups = if case < 12 { case } else { below(&mut rng, 20) };
        let len = match below(&mut rng, 3) {
            0 => groups * g,
            _ if groups == 0 => 0,
            _ => (groups - 1) * g + 1 + below(&mut rng, g),
        };
        let mut value = vec![0u8; len as usize];
        rng.fill(&mut value);
        let layout = Layout::new(len, log).unwrap();
        let outboard = vec![0u8; layout.outboard_size() as usize];
        let offs = offsets(len, g);
        for _ in 0..4 {
            let a = offs[below(&mut rng, offs.len() as u64) as usize];
            let b = offs[below(&mut rng, offs.len() as u64) as usize];
            let (a, b) = (a.min(len), b.min(len));
            let range = a.min(b)..a.max(b);
            let total = encoded_len(layout, &range).unwrap();
            for olen in [0, total.saturating_sub(1), total, total + 1, 2 * total + 3] {
                let mut buf = vec![0u8; olen as usize];
                let res = encode_range(&value, &outboard, log, &range, &mut buf);
                let tail = match res {
                    Ok(n) => {
                        assert!(olen >= total && n as u64 == total);
                        format!("\"res\":\"ok\",\"n\":{n}")
                    }
                    Err(e) => {
                        assert_eq!(e, TreeError::OutputTooSmall);
                        assert!(olen < total);
                        "\"res\":\"small\"".to_string()
                    }
                };
                let _ = writeln!(
                    out,
                    "{{\"t\":\"encout\",\"len\":{},\"log\":{log},\"s\":{},\"e\":{},\"olen\":{olen},{tail}}}",
                    limbs(len),
                    limbs(range.start),
                    limbs(range.end)
                );
            }
        }
        // a reversed range and a range past the end are refused before anything is written
        let mut buf = vec![0u8; 16];
        let bad = len + 1 + below(&mut rng, 5);
        assert_eq!(
            encode_range(&value, &outboard, log, &(0..bad), &mut buf),
            Err(TreeError::RangeOutOfBounds)
        );
        let _ = writeln!(
            out,
            "{{\"t\":\"encout\",\"len\":{},\"log\":{log},\"s\":{},\"e\":{},\"olen\":16,\"res\":\"range\"}}",
            limbs(len),
            limbs(0),
            limbs(bad)
        );
        // an outboard of the wrong size
        if !outboard.is_empty() {
            assert_eq!(
                encode_range(&value, &outboard[1..], log, &(0..len), &mut buf),
                Err(TreeError::OutboardSize)
            );
            let _ = writeln!(
                out,
                "{{\"t\":\"encout\",\"len\":{},\"log\":{log},\"s\":{},\"e\":{},\"olen\":16,\"oblen\":{},\"res\":\"outboard\"}}",
                limbs(len),
                limbs(0),
                limbs(len),
                outboard.len() - 1
            );
        }
    }
    out
}

#[test]
fn tla_traces_are_consistent_with_the_code() {
    let varint_trace = varint_traces();
    assert!(varint_trace.lines().count() > 5000);
    let layout_trace = layout_traces();
    assert!(layout_trace.lines().count() > 3000);
    let encoder_trace = encoder_traces();
    assert!(encoder_trace.lines().count() > 5000);
    let encout_trace = encout_traces();
    assert!(encout_trace.lines().count() > 1500);
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir).join("tla");
    std::fs::create_dir_all(&dir).unwrap();
    for (name, body) in [
        ("varint.ndjson", varint_trace),
        ("layout.ndjson", layout_trace),
        ("encoder.ndjson", encoder_trace),
        ("encout.ndjson", encout_trace),
    ] {
        std::fs::write(dir.join(name), body).unwrap();
    }
}
