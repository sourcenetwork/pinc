//! The handshake transcript: an incremental BLAKE3 hash over length-prefixed fields.
//!
//! Invariant: every field is written as its multiformats varint length followed by its bytes, so the encoding of a
//! sequence of fields is injective: two different sequences of fields (including different splits of the same
//! bytes) never hash the same input.
//!
//! Every field is absorbed under a tag that names it. The tag never reaches the hash; with the `trace` feature a
//! transcript also keeps the tags and lengths it absorbed, in order, for trace validation (see [`trace`]).

use pinc_wire::varint;

#[cfg(feature = "trace")]
pub mod trace;

/// An incremental transcript hash.
#[derive(Clone, Debug)]
pub struct Transcript {
    hasher: blake3::Hasher,
    #[cfg(feature = "trace")]
    seen: trace::Seen,
}

impl Default for Transcript {
    fn default() -> Self {
        Self::new()
    }
}

impl Transcript {
    /// An empty transcript.
    pub fn new() -> Self {
        Self {
            hasher: blake3::Hasher::new(),
            #[cfg(feature = "trace")]
            seen: trace::Seen::new(""),
        }
    }

    /// An empty transcript in the BLAKE3 `derive_key` mode, domain-separated by `label` (see [`crate::labels`]).
    pub fn with_label(label: &'static str) -> Self {
        Self {
            hasher: blake3::Hasher::new_derive_key(label),
            #[cfg(feature = "trace")]
            seen: trace::Seen::new(label),
        }
    }

    /// Absorb one field: its varint length, then its bytes. `tag` names the field for trace validation and is not
    /// hashed.
    pub fn absorb(&mut self, tag: &'static str, field: &[u8]) {
        #[cfg(feature = "trace")]
        self.seen.push(tag, field.len());
        #[cfg(not(feature = "trace"))]
        let _ = tag;
        let mut prefix = [0u8; varint::MAX_LEN];
        // A slice is at most `isize::MAX` bytes, always below the varint limit of 2^63, so this cannot fail.
        let n = varint::encode(field.len() as u64, &mut prefix).unwrap_or(0);
        self.hasher.update(prefix.get(..n).unwrap_or(&[]));
        self.hasher.update(field);
    }

    /// The hash of everything absorbed so far. The transcript keeps absorbing afterwards.
    pub fn snapshot(&self) -> [u8; 32] {
        #[cfg(feature = "trace")]
        self.seen.publish();
        *self.hasher.clone().finalize().as_bytes()
    }
}
