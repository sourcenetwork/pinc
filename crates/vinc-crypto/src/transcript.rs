//! The handshake transcript: an incremental BLAKE3 hash over length-prefixed fields.
//!
//! Invariant: every field is written as its multiformats varint length followed by its bytes, so the encoding of a
//! sequence of fields is injective: two different sequences of fields (including different splits of the same
//! bytes) never hash the same input.

use vinc_wire::varint;

/// An incremental transcript hash.
#[derive(Clone, Debug)]
pub struct Transcript(blake3::Hasher);

impl Default for Transcript {
    fn default() -> Self {
        Self::new()
    }
}

impl Transcript {
    /// An empty transcript.
    pub fn new() -> Self {
        Self(blake3::Hasher::new())
    }

    /// An empty transcript in the BLAKE3 `derive_key` mode, domain-separated by `label` (see [`crate::labels`]).
    pub fn with_label(label: &'static str) -> Self {
        Self(blake3::Hasher::new_derive_key(label))
    }

    /// Absorb one field: its varint length, then its bytes.
    pub fn absorb(&mut self, field: &[u8]) {
        let mut prefix = [0u8; varint::MAX_LEN];
        // A slice is at most `isize::MAX` bytes, always below the varint limit of 2^63, so this cannot fail.
        let n = varint::encode(field.len() as u64, &mut prefix).unwrap_or(0);
        self.0.update(prefix.get(..n).unwrap_or(&[]));
        self.0.update(field);
    }

    /// The hash of everything absorbed so far. The transcript keeps absorbing afterwards.
    pub fn snapshot(&self) -> [u8; 32] {
        *self.0.clone().finalize().as_bytes()
    }
}
