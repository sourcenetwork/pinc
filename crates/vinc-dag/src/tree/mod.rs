//! BLAKE3 verified streaming over chunk groups.
//!
//! A value is cut into 1024-byte chunks grouped into groups of `2^k` chunks (default k = 4, 16 KiB). The root of
//! the BLAKE3 tree equals `blake3::hash(value)`; the parents above the group level form the outboard, 64 bytes
//! per parent in pre-order. [`OutboardBuilder`] derives the root and outboard from streamed input,
//! [`RangeEncoder`] and [`encode_range`] produce the Bao-style stream that proves a byte range (rounded out to
//! groups), and [`RangeVerifier`] checks that stream against a root, releasing each group only once verified.
//! Every structure is fixed-capacity: one group buffer at most plus stacks of at most 64 entries.

mod builder;
mod encode;
mod error;
mod layout;
mod stack;
mod verify;

#[cfg(feature = "alloc")]
pub use builder::build_outboard_vec;
pub use builder::{OutboardBuilder, build_outboard};
pub use encode::{RangeEncoder, Step, encode_range, encoded_len};
pub use error::TreeError;
pub use layout::{CHUNK_LEN, DEFAULT_GROUP_LOG, Layout, MAX_GROUP_LOG, PARENT_LEN};
pub use verify::{Fed, RangeVerifier, Verified};

/// A 32-byte BLAKE3 chaining value or root hash.
pub type Cv = [u8; 32];
