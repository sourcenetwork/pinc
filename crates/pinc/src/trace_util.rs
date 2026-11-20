//! Helpers the in-crate trace tests share: the seeded random numbers, a byte string as a JSON array, and the write of an
//! ndjson file under `PINC_TRACE_DIR`.

#![allow(clippy::unwrap_used, reason = "tests assert")]

use alloc::string::String;
use core::fmt::Write as _;

/// The next number of a splitmix64 stream.
pub(crate) fn mix(s: &mut u64) -> u64 {
    *s = s.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut z = *s;
    z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    z ^ (z >> 31)
}

/// A number below `n` (`n > 0`).
pub(crate) fn below(s: &mut u64, n: usize) -> usize {
    usize::try_from(mix(s) % n as u64).unwrap_or(0)
}

/// A byte string as the JSON array of its numbers.
pub(crate) fn jb(d: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, b) in d.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        let _ = write!(s, "{b}");
    }
    s.push(']');
    s
}

/// Write `out` as `name` under `PINC_TRACE_DIR`, if that is set.
pub(crate) fn write_trace(name: &str, out: &str) {
    if let Some(dir) = std::env::var_os("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join(name), out).unwrap();
    }
}
