//! Every domain-separation label of the delay-tolerant layer.
//!
//! Invariants: each label is a `pub const` that starts with [`PREFIX`], and all labels are distinct from each other
//! and from the labels of `vinc-crypto` and `vinc-security`, so no derivation, transcript or signature of this layer
//! shares a domain with another. A label is used for exactly one purpose.

/// The prefix of every label.
pub const PREFIX: &str = "VINC 2026 v1 ";
/// Domain of the initial chaining key of the one-shot encryption.
pub const CHAIN: &str = "VINC 2026 v1 dtn chain";
/// Domain of the transcript that binds the public values, the recipient and the bundle id into the key.
pub const TRANSCRIPT: &str = "VINC 2026 v1 dtn transcript";
/// Derives the slice AEAD key from the extracted secret and the transcript hash.
pub const SLICE_KEY: &str = "VINC 2026 v1 dtn slice key";
/// Domain of the bundle id.
pub const BUNDLE_ID: &str = "VINC 2026 v1 dtn bundle id";
/// Domain of the digest the sender's identity signs over a bundle head.
pub const HEAD: &str = "VINC 2026 v1 dtn head";
/// Domain of the digest a custodian's identity signs over a custody acknowledgement.
pub const CUSTODY_ACK: &str = "VINC 2026 v1 dtn custody ack";

/// Every label above except [`PREFIX`], for tests that check uniqueness and the prefix.
pub const ALL: [&str; 6] = [CHAIN, TRANSCRIPT, SLICE_KEY, BUNDLE_ID, HEAD, CUSTODY_ACK];
