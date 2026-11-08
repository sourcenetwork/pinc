//! Hex helpers shared by the crypto tests.
#![allow(dead_code, missing_docs, clippy::unwrap_used, clippy::indexing_slicing)]

/// Decode a hex string (any case, no separators).
pub(crate) fn hex(s: &str) -> Vec<u8> {
    assert!(s.len().is_multiple_of(2), "odd hex length");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

/// Decode a hex string of exactly `N` bytes.
pub(crate) fn arr<const N: usize>(s: &str) -> [u8; N] {
    hex(s).try_into().unwrap()
}
