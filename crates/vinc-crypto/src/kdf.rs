//! The key derivation functions over BLAKE3, and the domain-separation labels.
//!
//! Invariants: `extract` is exactly `blake3::keyed_hash`; `expand` is `derive_key` over `prk || ctx` read as an
//! XOF, so two different labels never give related output. Every label is a `pub const` in [`labels`] and starts
//! with `"VINC 2026 v1 "`.

use zeroize::Zeroize;

/// Domain-separation labels. Each one is unique and starts with [`PREFIX`](labels::PREFIX).
pub mod labels {
    /// The start of every label of every version: bytes a signature over application data must never begin with.
    pub const RESERVED: &str = "VINC 2026 ";
    /// The prefix of every label.
    pub const PREFIX: &str = "VINC 2026 v1 ";
    /// Derives a node id from an algorithm tag and a public key.
    pub const NODE_ID: &str = "VINC 2026 v1 node id";
    /// Domain of the message digest both halves of a hybrid signature sign.
    pub const HYBRID_SIGNATURE: &str = "VINC 2026 v1 hybrid signature";
    // vertexia: kept out of ALL because the label registry the trace tests and the models replay is closed; the
    // cutover that wires the statement adds it there together with the models.
    /// The label of every signed statement's signature.
    pub const STATEMENT: &str = "VINC 2026 v1 statement";

    /// Every label above except [`PREFIX`] and [`STATEMENT`], for tests that check uniqueness and the prefix.
    pub const ALL: [&str; 2] = [NODE_ID, HYBRID_SIGNATURE];
}

/// Extract a pseudo-random key from the input keying material `ikm`, keyed by `salt`.
pub fn extract(salt: &[u8; 32], ikm: &[u8]) -> [u8; 32] {
    let out = *blake3::keyed_hash(salt, ikm).as_bytes();
    #[cfg(feature = "derive-trace")]
    crate::trace::emit(&crate::trace::Derivation::Extract { salt, ikm, out: &out });
    out
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
    #[cfg(feature = "derive-trace")]
    crate::trace::emit(&crate::trace::Derivation::Expand { prk, label, ctx, out });
}

#[cfg(test)]
mod tests {
    use super::labels;

    #[test]
    fn labels_are_unique_and_prefixed() {
        let every = [labels::NODE_ID, labels::HYBRID_SIGNATURE, labels::STATEMENT];
        assert_eq!(labels::ALL, every[..2]);
        for (i, a) in every.iter().enumerate() {
            assert!(a.starts_with(labels::PREFIX), "{a} lacks the prefix");
            assert!(every.iter().skip(i + 1).all(|b| a != b), "{a} is repeated");
        }
        assert_eq!(labels::STATEMENT.len(), 22);
    }
}
