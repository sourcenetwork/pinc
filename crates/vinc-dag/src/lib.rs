//! The lite VINC DAG library: CIDs and blocks in `DefraDB`'s format, CAR v1 archives, BLAKE3 verified streaming and
//! verified-range sets. It contains no networking, membership or session code.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

pub mod block;
pub mod car;
mod cbor_len;
pub mod cid;
pub mod ranges;
pub mod tree;
