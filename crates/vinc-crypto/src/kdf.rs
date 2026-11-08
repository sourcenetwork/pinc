//! The key derivation functions over BLAKE3, and the domain-separation labels.
//!
//! Invariants: `extract` is exactly `blake3::keyed_hash`; `expand` is `derive_key` over `prk || ctx` read as an
//! XOF, so two different labels never give related output. Every label is a `pub const` in [`labels`] and starts
//! with `"VINC 2026 v1 "`.

use zeroize::Zeroize;

/// Domain-separation labels. Each one is unique and starts with [`PREFIX`](labels::PREFIX).
pub mod labels {
    /// The prefix of every label.
    pub const PREFIX: &str = "VINC 2026 v1 ";
    /// Derives a node id from an algorithm tag and a public key.
    pub const NODE_ID: &str = "VINC 2026 v1 node id";
    /// Domain of the message digest both halves of a hybrid signature sign.
    pub const HYBRID_SIGNATURE: &str = "VINC 2026 v1 hybrid signature";

    /// Every label above except [`PREFIX`], for tests that check uniqueness and the prefix.
    pub const ALL: [&str; 2] = [NODE_ID, HYBRID_SIGNATURE];
}

/// Extract a pseudo-random key from the input keying material `ikm`, keyed by `salt`.
pub fn extract(salt: &[u8; 32], ikm: &[u8]) -> [u8; 32] {
    *blake3::keyed_hash(salt, ikm).as_bytes()
}

/// Fill `out` with key material derived from `prk` and `ctx` under `label`.
///
/// `label` must be one of the constants in [`labels`]. `out` may be any length: it is read from the BLAKE3 XOF.
pub fn expand(prk: &[u8; 32], label: &'static str, ctx: &[u8], out: &mut [u8]) {
    let mut hasher = blake3::Hasher::new_derive_key(label);
    hasher.update(prk);
    hasher.update(ctx);
    hasher.finalize_xof().fill(out);
    hasher.zeroize();
}
