//! VINC encodings: canonical, bounded, length-prefixed codecs parsed in place from borrowed bytes.
//!
//! Everything here reads from a borrowed `&[u8]` and writes into a caller-provided `&mut [u8]`: no codec path
//! allocates, panics, or reads a byte twice. Malformed input is always reported as a [`WireError`].
#![no_std]

pub mod cbor;
pub mod error;
pub mod reader;
pub mod varint;
pub mod writer;

pub use error::WireError;
pub use reader::Reader;
pub use writer::Writer;
