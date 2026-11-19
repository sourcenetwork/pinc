//! Trace generation for the encoded sizes of `pinc-dag` (`cbor_len.rs`): the real `head_len`, `text_len` and `cid_len`
//! (through the probe `pinc_dag::cbor_len_trace` of the `trace` feature) and the `pinc-wire` encoder, recorded as ndjson
//! (`tla/dag_sizes.ndjson` under `PINC_TRACE_DIR`) for the TLA+ trace check (`TraceDagCborLen.tla`).
//!
//! A `u64` or `usize` is written as four 16-bit limbs, least significant first, which `U64.tla` reads (TLC integers are
//! 32 bits wide). The functions run on every argument below 300, on `2^j - 1`, `2^j` and `2^j + 1` for every `j`, and on
//! seeded random values; for arguments below 300 the encoder writes the same piece and its length is recorded beside
//! the function's. The test also checks every size against a naive table and the encoder, so it is meaningful without
//! the proof tools. Nothing is written when `PINC_TRACE_DIR` is unset.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::needless_range_loop,
    clippy::too_many_lines
)]

use std::fmt::Write as _;

use pinc_dag::cbor_len_trace::{cid_len, head_len, text_len};
use pinc_tests::SplitMix64;
use pinc_wire::WireError;
use pinc_wire::cbor::Encoder;

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

/// A JSON array of the bytes.
fn arr(bytes: &[u8]) -> String {
    let body: Vec<String> = bytes.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// What `piece` writes into a fresh buffer of `cap` bytes.
fn written(cap: usize, piece: impl FnOnce(&mut Encoder<'_>) -> Result<(), WireError>) -> Vec<u8> {
    let mut buf = vec![0u8; cap];
    let mut enc = Encoder::new(&mut buf);
    piece(&mut enc).unwrap();
    enc.written().to_vec()
}

/// Every argument below 300, `2^j - 1`, `2^j` and `2^j + 1` for every `j` that fit a `u64`, and 2000 seeded values,
/// half of them cut to a random bit width.
fn values() -> Vec<u64> {
    let mut out: Vec<u64> = (0..300).collect();
    for j in 0..=64u32 {
        let p = 1u128 << j;
        for v in [p - 1, p, p + 1] {
            if let Ok(v) = u64::try_from(v) {
                out.push(v);
            }
        }
    }
    let mut rng = SplitMix64::traced(0xda9c_0b01);
    for i in 0..2000 {
        let v = rng.next_u64();
        out.push(if i % 2 == 0 { v >> (rng.next_u64() % 64) } else { v });
    }
    out
}

/// The header size by the table of the format, apart from the code.
fn naive_head(a: u64) -> usize {
    match a {
        0..=23 => 1,
        24..=0xff => 2,
        0x100..=0xffff => 3,
        0x1_0000..=0xffff_ffff => 5,
        _ => 9,
    }
}

fn head_events(values: &[u64]) -> String {
    let mut out = String::new();
    for &a in values {
        let len = head_len(a);
        assert_eq!(len, naive_head(a));
        let bytes = written(16, |e| e.unsigned(a));
        let lens = [
            bytes.len(),
            written(16, |e| e.negative(a)).len(),
            written(16, |e| e.array(a)).len(),
            written(16, |e| e.map(a)).len(),
        ];
        assert!(
            lens.iter().all(|&l| l == len),
            "head_len({a}) is not what the encoder writes: {lens:?}"
        );
        assert_eq!(bytes[0] >> 5, 0);
        let _ = writeln!(
            out,
            r#"{{"t":"head","a":{},"len":{len},"bytes":{},"w":[{},{},{},{}]}}"#,
            limbs(a),
            arr(&bytes),
            lens[0],
            lens[1],
            lens[2],
            lens[3]
        );
    }
    out
}

fn text_events(values: &[u64]) -> String {
    let mut out = String::new();
    let mut sizes: Vec<usize> = values.iter().map(|&v| v as usize).collect();
    sizes.push(usize::MAX);
    for n in sizes {
        let len = text_len(n);
        if (n as u64) < 1 << 63 {
            assert_eq!(Some(len), head_len(n as u64).checked_add(n), "text_len({n}) saturated");
        }
        let w = if n < 300 {
            let text = written(320, |e| e.text(&"a".repeat(n)));
            let bytes = written(320, |e| e.bytes(&vec![0u8; n]));
            assert_eq!((text.len(), bytes.len()), (len, len));
            format!("[{},{}]", limbs(text.len() as u64), limbs(bytes.len() as u64))
        } else {
            "[]".to_owned()
        };
        let _ = writeln!(
            out,
            r#"{{"t":"text","n":{},"len":{},"w":{w}}}"#,
            limbs(n as u64),
            limbs(len as u64)
        );
    }
    assert_eq!(text_len(usize::MAX), usize::MAX, "text_len does not saturate");
    out
}

fn cid_events(values: &[u64]) -> String {
    let mut out = String::new();
    // `cid_len` adds one to its argument as a u64, so `usize::MAX` is out of its domain (CIDs are at most 84 bytes).
    for n in values.iter().map(|&v| v as usize).filter(|&n| n != usize::MAX) {
        let len = cid_len(n);
        if (n as u64) < 1 << 63 {
            assert_eq!(
                Some(len),
                3usize
                    .checked_add(head_len(n as u64 + 1))
                    .and_then(|l| l.checked_add(n)),
                "cid_len({n}) saturated"
            );
        }
        let w = if n < 300 {
            let cid: Vec<u8> = (0..n).map(|i| (i % 256) as u8).collect();
            let tagged = written(320, |e| e.tag_cid(&cid));
            assert_eq!(tagged.len(), len);
            format!("[{}]", limbs(tagged.len() as u64))
        } else {
            "[]".to_owned()
        };
        let _ = writeln!(
            out,
            r#"{{"t":"cid","n":{},"len":{},"w":{w}}}"#,
            limbs(n as u64),
            limbs(len as u64)
        );
    }
    out
}

#[test]
fn dag_sizes_traces_are_consistent_with_the_code() {
    let values = values();
    let mut trace = head_events(&values);
    trace.push_str(&text_events(&values));
    trace.push_str(&cid_events(&values));
    assert!(trace.lines().count() > 7000);
    let Some(dir) = std::env::var_os("PINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir).join("tla");
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("dag_sizes.ndjson"), trace).unwrap();
}
