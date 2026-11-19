//! The shared writer of the membership trace test: one ndjson file per proof part, written to `$PINC_TRACE_DIR`
//! when the variable is set.
#![allow(dead_code, unreachable_pub, clippy::unwrap_used, clippy::expect_used)]

use std::collections::BTreeMap;
use std::fmt::Write as _;

/// The ndjson files of the membership proofs (the node machine, the hub stream codec, the incarnation).
pub const FILES: [&str; 3] = ["membership.ndjson", "mcodec.ndjson", "minc.ndjson"];

/// One String of ndjson lines per output file.
#[derive(Debug, Default)]
pub struct TraceWriter {
    files: BTreeMap<String, String>,
}

impl TraceWriter {
    /// A writer with every file empty.
    pub fn new() -> Self {
        let mut files = BTreeMap::new();
        for f in FILES {
            files.insert(f.to_owned(), String::new());
        }
        Self { files }
    }

    /// Append one line (without its newline) to `file`.
    pub fn line(&mut self, file: &str, s: &str) {
        let f = self.files.entry(file.to_owned()).or_default();
        f.push_str(s);
        f.push('\n');
    }

    /// How many lines `file` holds.
    pub fn count(&self, file: &str) -> usize {
        self.files.get(file).map_or(0, |s| s.lines().count())
    }

    /// Write every file into `$PINC_TRACE_DIR`, if it is set.
    pub fn finish(&self) {
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            for (name, text) in &self.files {
                std::fs::write(std::path::Path::new(&dir).join(name), text).unwrap();
            }
        }
    }
}

/// The four 16-bit limbs of a u64, as the traces record it.
pub fn limbs(v: u64) -> String {
    format!(
        "[{},{},{},{}]",
        v & 0xffff,
        (v >> 16) & 0xffff,
        (v >> 32) & 0xffff,
        (v >> 48) & 0xffff
    )
}

/// A byte list as a JSON array.
pub fn list(bytes: &[u8]) -> String {
    let mut s = String::from("[");
    for (i, x) in bytes.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        write!(s, "{x}").unwrap();
    }
    s.push(']');
    s
}

/// A bool as JSON.
pub fn b(x: bool) -> &'static str {
    if x { "true" } else { "false" }
}

/// An optional u64 as a list of length 0 or 1 of limbs.
pub fn opt_limbs(v: Option<u64>) -> String {
    v.map_or_else(|| "[]".to_owned(), |x| format!("[{}]", limbs(x)))
}

/// An optional small number as a list of length 0 or 1.
pub fn opt_num(v: Option<u64>) -> String {
    v.map_or_else(|| "[]".to_owned(), |x| format!("[{x}]"))
}
