//! Helpers the in-crate trace tests share: a byte string as a JSON array, and the write of an
//! ndjson file under `PINC_TRACE_DIR`.

#![allow(clippy::unwrap_used, reason = "tests assert")]

use alloc::string::String;
use core::fmt::Write as _;

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
