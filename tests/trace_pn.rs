//! Trace generation for the packet-number codec: seeded calls of the real `encode_pn`, `decode_pn` and `pn_len_for`
//! (`pinc-transport`), recorded as ndjson (`pn.ndjson`) for the TLA+ trace check (`TracePn.tla`) and the Lean replay
//! (`Pinc/TracePn.lean`).
//!
//! The expansion is called with numbers near the edges of the window of every width (just inside and just outside half
//! a window of the next number expected), with and without a largest received, and with the truncated number beyond
//! its width. The encoding is called with every width, including the refused ones, and with numbers at and above
//! `2^62 - 1`. A second file (`pn_wide.ndjson`, read by the Lean replay only: the TLA+ checker has 32-bit integers)
//! takes numbers up to `2^64 - 1` and the width 4.
//!
//! The test asserts the round trip itself (the number comes back whenever it is within half a window) so it is
//! meaningful without the proof tools.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::cast_possible_truncation,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::packet::{MAX_PN, PacketError, WIDE_WINDOW, decode_pn, encode_pn, pn_len_for};

fn err_name(e: &PacketError) -> &'static str {
    match e {
        PacketError::PacketNumber => "PacketNumber",
        PacketError::PnLength => "PnLength",
        _ => "other",
    }
}

fn enc(out: &mut String, full: u64, len: usize) -> Option<[u8; 3]> {
    match encode_pn(full, len) {
        Ok(b) => {
            let _ = writeln!(
                out,
                r#"{{"t":"txpn","op":"enc","full":{full},"len":{len},"err":"ok","b":[{},{},{}]}}"#,
                b[0], b[1], b[2]
            );
            Some(b)
        }
        Err(e) => {
            let _ = writeln!(
                out,
                r#"{{"t":"txpn","op":"enc","full":{full},"len":{len},"err":"{}","b":[0,0,0]}}"#,
                err_name(&e)
            );
            None
        }
    }
}

fn dec(out: &mut String, t: u32, len: usize, lg: Option<u64>) -> u64 {
    let r = decode_pn(t, len, lg);
    let _ = writeln!(
        out,
        r#"{{"t":"txpn","op":"dec","tr":{t},"len":{len},"lg":{},"r":{r}}}"#,
        lg.map_or(-1, i128::from)
    );
    r
}

fn run(rng: &mut SplitMix64, out: &mut String, wide: bool, n: u32) {
    let top: u64 = if wide { 1 << 62 } else { 1 << 30 };
    for _ in 0..n {
        let len = if wide {
            1 + (rng.next_u64() % 4) as usize
        } else {
            1 + (rng.next_u64() % 3) as usize
        };
        let w: u64 = 1 << (8 * len);
        let h = w / 2;
        let lg = if rng.next_u64().is_multiple_of(6) {
            None
        } else if wide && rng.next_u64().is_multiple_of(8) {
            Some([u64::MAX, u64::MAX - 1, MAX_PN, MAX_PN + 1, 1 << 62, (1 << 62) + 5][(rng.next_u64() % 6) as usize])
        } else {
            Some(rng.next_u64() % top)
        };
        let e = lg.map_or(0, |l| l.saturating_add(1));
        // a number near the edges of the window around the next one expected
        let delta = i128::from(rng.next_u64() % (w + 8)) - i128::from(h) - 4;
        let nn = (i128::from(e) + delta).clamp(0, i128::from(MAX_PN));
        let n_full = u64::try_from(nn).unwrap();
        let t = (n_full % w) as u32;
        let r = dec(out, t, len, lg);
        // within half a window of the next expected, the number comes back
        if e < n_full + h && n_full <= e.saturating_add(h) && n_full <= MAX_PN {
            assert_eq!(r, n_full, "pn {n_full} width {len} largest {lg:?} did not come back");
        }
        assert_eq!(
            r % w,
            u64::from(t) % w,
            "the expansion is not congruent to the truncated number"
        );
        if rng.next_u64().is_multiple_of(5) {
            // the truncated number beyond its width
            let big = (rng.next_u64() >> 32) as u32;
            if wide || len < 4 {
                let _ = dec(out, if wide { big } else { big & 0x7fff_ffff }, len, lg);
            }
        }
        // the encoding, with every width including the refused ones
        let elen = (rng.next_u64() % 6) as usize;
        let full = [n_full, MAX_PN, MAX_PN + 1, 0, rng.next_u64() % top][(rng.next_u64() % 5) as usize];
        let full = if wide { full } else { full.min((1 << 31) - 1) };
        if let Some(b) = enc(out, full, elen) {
            // what it wrote expands back to the number within the window
            let v = b.iter().take(elen).fold(0u32, |a, x| (a << 8) | u32::from(*x));
            assert_eq!(u64::from(v), full % (1 << (8 * elen)));
        }
        let win = [
            0,
            1,
            WIDE_WINDOW,
            WIDE_WINDOW + 1,
            u64::MAX,
            rng.next_u64() % 100_000_000,
        ][(rng.next_u64() % 6) as usize];
        let win = if wide { win } else { win.min((1 << 31) - 1) };
        let _ = writeln!(out, r#"{{"t":"txpn","op":"for","w":{win},"len":{}}}"#, pn_len_for(win));
    }
}

#[test]
fn packet_number_calls_match_the_models() {
    let mut rng = SplitMix64::traced(0x504e_0001);
    let mut out = String::new();
    run(&mut rng, &mut out, false, 6000);
    let mut wide = String::new();
    run(&mut rng, &mut wide, true, 6000);
    for needle in [r#""err":"ok""#, r#""err":"PnLength""#, r#""op":"dec""#, r#""op":"for""#] {
        assert!(
            pinc_tests::soaking() || out.contains(needle),
            "the calls never reach {needle}"
        );
    }
    assert!(
        pinc_tests::soaking() || wide.contains(r#""err":"PacketNumber""#),
        "the wide calls never reach PacketNumber"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("pn.ndjson"), &out).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("pn_wide.ndjson"), &wide).unwrap();
    }
}
