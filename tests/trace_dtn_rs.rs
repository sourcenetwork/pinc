//! Trace generation for the GF(2^8) arithmetic, its slice kernels and the Reed-Solomon code: real runs of `inv`, `mul`,
//! `xor_into`, `mul_add`, `scale`, `Rs::new`, `Rs::encode` and `Rs::reconstruct` through the public API, recorded as
//! ndjson (`dtn_rs.ndjson`) for the TLA+ trace check (`TraceDtnRs.tla`) and the Lean replay (`Pinc/TraceDtnRs.lean`).
//!
//! What is recorded: every value of `inv` (all 256), `mul` for every first operand against a fixed set of second
//! operands and a seeded spread of pairs, the three slice kernels on random slices of lengths around the eight-byte
//! chunk (including the unequal-length case), `Rs::new` on valid and invalid parameters, and seeded runs of `encode`
//! and `reconstruct` over many `(k, m, len)` with random erasure patterns (more than `m` erasures too, which is
//! `Incomplete`), wrong block and `present` sizes (`Buffer`), and the two largest solves (`k + m = 255` with 127
//! missing data symbols). Absent symbols are scrambled before the call. The Lean replay runs the proved model on the
//! recorded inputs and requires the recorded output.
//!
//! The test asserts everything itself (the products against a shift-and-add reference written here, the field laws,
//! and that every successful reconstruction returns the whole original block), so it is meaningful without the proof
//! tools. The trace is written to the directory in `PINC_TRACE_DIR` when it is set; otherwise nothing is written.
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
    clippy::needless_pass_by_value,
    clippy::type_complexity,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_dtn::error::DtnError;
use pinc_dtn::gf256::{inv, mul, mul_add, scale, xor_into};
use pinc_dtn::rs::Rs;
use pinc_tests::{SplitMix64, trace_cases};

/// The product by shift-and-add with reduction by 0x11d: the definition, independent of the tables.
fn ref_mul(a: u8, b: u8) -> u8 {
    let (mut a, mut b, mut p) = (u16::from(a), b, 0u16);
    while b != 0 {
        if b & 1 == 1 {
            p ^= a;
        }
        a <<= 1;
        if a & 0x100 != 0 {
            a ^= 0x11d;
        }
        b >>= 1;
    }
    p as u8
}

fn arr<T: std::fmt::Display>(v: &[T]) -> String {
    let mut s = String::from("[");
    for (i, x) in v.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

fn bits(p: &[bool]) -> String {
    arr(&p.iter().map(|b| u8::from(*b)).collect::<Vec<_>>())
}

fn rand_bytes(rng: &mut SplitMix64, n: usize) -> Vec<u8> {
    let mut v = vec![0; n];
    rng.fill(&mut v);
    v
}

fn err_name(e: DtnError) -> &'static str {
    match e {
        DtnError::Buffer => "buffer",
        DtnError::Incomplete => "incomplete",
        DtnError::Params => "params",
        _ => panic!("unexpected error {e}"),
    }
}

#[test]
fn field_and_code_trace() {
    let mut rng = SplitMix64::traced(0xD7_0F_E1);
    let mut out: Vec<String> = Vec::new();

    // inv for every byte, mul against fixed operands for every byte, and a random spread of pairs.
    for a in 0..=255u8 {
        let r = inv(a);
        if a != 0 {
            assert_eq!(mul(a, r), 1, "inverse of {a}");
        } else {
            assert_eq!(r, 0);
        }
        out.push(format!(r#"{{"t":"ginv","a":{a},"r":{r}}}"#));
    }
    let fixed = [0u8, 1, 2, 3, 29, 128, 129, 254, 255, 0x53, 0xca, 0x1d];
    for a in 0..=255u8 {
        for &b in &fixed {
            let r = mul(a, b);
            assert_eq!(r, ref_mul(a, b));
            assert_eq!(r, mul(b, a));
            out.push(format!(r#"{{"t":"gmul","a":{a},"b":{b},"r":{r}}}"#));
        }
    }
    for _ in 0..trace_cases(300, 1500) {
        let (a, b, c) = (rng.next_u64() as u8, rng.next_u64() as u8, rng.next_u64() as u8);
        let r = mul(a, b);
        assert_eq!(r, ref_mul(a, b));
        assert_eq!(mul(a, b ^ c), r ^ mul(a, c), "distributive");
        assert_eq!(mul(mul(a, b), c), mul(a, mul(b, c)), "associative");
        out.push(format!(r#"{{"t":"gmul","a":{a},"b":{b},"r":{r}}}"#));
    }
    // The generator 2 has order 255.
    let mut x = 1u8;
    for i in 1..=255 {
        x = mul(x, 2);
        assert_eq!(x == 1, i == 255);
    }

    // The slice kernels: equal and unequal lengths around the eight-byte chunk.
    for len in [0usize, 1, 2, 7, 8, 9, 15, 16, 17, 23, 24, 25, 40] {
        for (dl, sl) in [(len, len), (len, len / 2), (len / 2 + 1, len)] {
            for c in [0u8, 1, 2, 29, 77, 255, rng.next_u64() as u8] {
                let (dst, src) = (rand_bytes(&mut rng, dl), rand_bytes(&mut rng, sl));
                let mut d = dst.clone();
                mul_add(&mut d, &src, c);
                for i in 0..dl {
                    let want = if i < sl { dst[i] ^ mul(c, src[i]) } else { dst[i] };
                    assert_eq!(d[i], want);
                }
                out.push(format!(
                    r#"{{"t":"gkern","op":"muladd","c":{c},"dst":{},"src":{},"out":{}}}"#,
                    arr(&dst),
                    arr(&src),
                    arr(&d)
                ));
            }
            let (dst, src) = (rand_bytes(&mut rng, dl), rand_bytes(&mut rng, sl));
            let mut d = dst.clone();
            xor_into(&mut d, &src);
            for i in 0..dl {
                assert_eq!(d[i], if i < sl { dst[i] ^ src[i] } else { dst[i] });
            }
            out.push(format!(
                r#"{{"t":"gkern","op":"xor","c":0,"dst":{},"src":{},"out":{}}}"#,
                arr(&dst),
                arr(&src),
                arr(&d)
            ));
        }
        for c in [0u8, 1, 2, 29, 255, rng.next_u64() as u8] {
            let buf = rand_bytes(&mut rng, len);
            let mut b = buf.clone();
            scale(&mut b, c);
            for i in 0..len {
                assert_eq!(b[i], mul(c, buf[i]));
            }
            out.push(format!(
                r#"{{"t":"gkern","op":"scale","c":{c},"dst":{},"src":[],"out":{}}}"#,
                arr(&buf),
                arr(&b)
            ));
        }
    }

    // Rs::new: valid and invalid parameters.
    for (k, m) in [
        (0usize, 0usize),
        (0, 5),
        (1, 0),
        (1, 254),
        (1, 255),
        (2, 253),
        (2, 254),
        (127, 128),
        (128, 128),
        (255, 0),
        (255, 1),
        (256, 0),
        (300, 4),
        (3, 250),
    ] {
        let r = Rs::new(k, m);
        assert_eq!(r.is_ok(), k >= 1 && k + m <= 255, "k={k} m={m}");
        out.push(format!(r#"{{"t":"rsnew","k":{k},"m":{m},"ok":{}}}"#, r.is_ok()));
    }

    // Encode and reconstruct runs.
    let configs: [(usize, usize); 14] = [
        (1, 0),
        (1, 1),
        (1, 3),
        (2, 2),
        (3, 3),
        (4, 3),
        (5, 4),
        (6, 2),
        (3, 6),
        (8, 4),
        (10, 5),
        (7, 9),
        (16, 3),
        (2, 12),
    ];
    for &(k, m) in &configs {
        let rs = Rs::new(k, m).unwrap();
        let n = rs.n();
        for len in [1usize, 2, 5] {
            for trial in 0..trace_cases(2, 6) {
                // Encode over garbage parity: the parity is overwritten, the data is left alone.
                let mut block = rand_bytes(&mut rng, n * len);
                let before = block.clone();
                rs.encode(len, &mut block).unwrap();
                assert_eq!(block[..k * len], before[..k * len]);
                out.push(format!(
                    r#"{{"t":"rsenc","k":{k},"m":{m},"len":{len},"ok":true,"block":{},"out":{}}}"#,
                    arr(&before),
                    arr(&block)
                ));
                let whole = block.clone();
                // A random present set: sometimes below k, sometimes everything.
                let present: Vec<bool> = match trial {
                    0 => vec![true; n],
                    1 => (0..n).map(|s| s >= m).collect(),
                    _ => (0..n).map(|_| !rng.next_u64().is_multiple_of(3)).collect(),
                };
                let mut b = whole.clone();
                for (s, p) in present.iter().enumerate() {
                    if !p {
                        let junk = rand_bytes(&mut rng, len);
                        b[s * len..(s + 1) * len].copy_from_slice(&junk);
                    }
                }
                let input = b.clone();
                let held = present.iter().filter(|p| **p).count();
                let r = rs.reconstruct(len, &mut b, &present);
                match r {
                    Ok(()) => {
                        assert!(held >= k);
                        assert_eq!(b, whole, "k={k} m={m} len={len}");
                    }
                    Err(e) => {
                        assert_eq!(e, DtnError::Incomplete);
                        assert!(held < k);
                        assert_eq!(b, input);
                    }
                }
                let tail = match r {
                    Ok(()) => r#""ok":true"#.to_string(),
                    Err(e) => format!(r#""ok":false,"err":"{}""#, err_name(e)),
                };
                out.push(format!(
                    r#"{{"t":"rsrec","k":{k},"m":{m},"len":{len},{tail},"block":{},"present":{},"out":{}}}"#,
                    arr(&input),
                    bits(&present),
                    arr(&b)
                ));
            }
        }
        // Buffer errors: an empty symbol, a short or long block, a short or long present vector.
        let len = 3;
        let whole = {
            let mut w = rand_bytes(&mut rng, n * len);
            rs.encode(len, &mut w).unwrap();
            w
        };
        let present_all = vec![true; n];
        let cases: [(usize, Vec<u8>, Vec<bool>); 5] = [
            (0, whole.clone(), present_all.clone()),
            (len, whole[..whole.len() - 1].to_vec(), present_all.clone()),
            (len, [whole.clone(), vec![0]].concat(), present_all.clone()),
            (len, whole.clone(), present_all[..n - 1].to_vec()),
            (len, whole.clone(), [present_all.clone(), vec![true]].concat()),
        ];
        for (l, blk, pres) in cases {
            let mut b = blk.clone();
            let r = rs.reconstruct(l, &mut b, &pres);
            assert_eq!(r.err(), Some(DtnError::Buffer));
            assert_eq!(b, blk);
            out.push(format!(
                r#"{{"t":"rsrec","k":{k},"m":{m},"len":{l},"ok":false,"err":"buffer","block":{},"present":{},"out":{}}}"#,
                arr(&blk),
                bits(&pres),
                arr(&b)
            ));
        }
        let mut b = whole[..whole.len() - 1].to_vec();
        let blk = b.clone();
        assert_eq!(rs.encode(len, &mut b).err(), Some(DtnError::Buffer));
        out.push(format!(
            r#"{{"t":"rsenc","k":{k},"m":{m},"len":{len},"ok":false,"err":"buffer","block":{},"out":{}}}"#,
            arr(&blk),
            arr(&b)
        ));
        let mut e = Vec::new();
        assert_eq!(rs.encode(0, &mut e).err(), Some(DtnError::Buffer));
        out.push(format!(
            r#"{{"t":"rsenc","k":{k},"m":{m},"len":0,"ok":false,"err":"buffer","block":[],"out":[]}}"#
        ));
    }

    // The largest solves: k + m = 255 with 127 missing data symbols replaced by 127 parity symbols.
    for (k, m) in [(128usize, 127usize), (127, 128), (200, 55), (55, 200)] {
        // the quick profile solves one of the two 127-symbol shapes (about 8 s of replay each)
        if (k, m) == (127, 128) && trace_cases(0, 1) == 0 {
            continue;
        }
        let rs = Rs::new(k, m).unwrap();
        let (n, len) = (rs.n(), 2);
        let mut whole = rand_bytes(&mut rng, n * len);
        rs.encode(len, &mut whole).unwrap();
        let drop_data = k.min(127);
        for shape in 0..2 {
            let present: Vec<bool> = (0..n)
                .map(|s| {
                    if s < k {
                        s >= drop_data || (shape == 1 && s % 2 == 1)
                    } else {
                        shape == 0 || (s - k) % 3 != 0
                    }
                })
                .collect();
            let held = present.iter().filter(|p| **p).count();
            let mut b = whole.clone();
            for (s, p) in present.iter().enumerate() {
                if !p {
                    b[s * len..(s + 1) * len].fill(0xA5);
                }
            }
            let input = b.clone();
            let r = rs.reconstruct(len, &mut b, &present);
            let tail = match r {
                Ok(()) => {
                    assert_eq!(b, whole);
                    r#""ok":true"#.to_string()
                }
                Err(e) => {
                    assert!(held < k);
                    format!(r#""ok":false,"err":"{}""#, err_name(e))
                }
            };
            out.push(format!(
                r#"{{"t":"rsrec","k":{k},"m":{m},"len":{len},{tail},"block":{},"present":{},"out":{}}}"#,
                arr(&input),
                bits(&present),
                arr(&b)
            ));
        }
    }

    assert!(out.len() > 3000);
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        let mut text = out.join("\n");
        text.push('\n');
        std::fs::write(std::path::Path::new(&dir).join("dtn_rs.ndjson"), text).unwrap();
    }
}
