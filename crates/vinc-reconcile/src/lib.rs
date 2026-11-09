//! VINC set reconciliation whose cost scales with the difference, not with the sets.
//!
//! Two peers each hold a sorted set of byte-string items. They compare range fingerprints (the XOR of keyed hashes),
//! split a differing range 16 ways, and exchange the items of small ranges, so the bytes and rounds follow the
//! symmetric difference and the logarithm of the set size. A small or cold side streams its whole list instead. The
//! initiator learns the exact difference; the responder learns nothing and the initiator reports. The result is
//! exact: ids can collide, so a final fingerprint check follows any exchange that used leaves, and a disagreement is
//! resolved by items.
//!
//! The crate is `no_std` and never uses `unsafe`. Without the `alloc` feature it offers the hashes, the message
//! decoders, the [`ItemIndex`] trait and the channel types; with it, the [`Initiator`] and [`Responder`] state
//! machines, the drivers over a [`Channel`], and [`MemIndex`]. Memory is bounded by [`Limits`] and no input can make
//! any call panic. See [`wire`] for the message format and [`session`] for the protocol rules.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "alloc")]
pub mod channel;
#[cfg(feature = "alloc")]
mod core;
#[cfg(feature = "alloc")]
pub mod drive;
pub mod error;
pub mod hash;
pub mod index;
pub mod limits;
#[cfg(feature = "alloc")]
pub mod mem;
#[cfg(feature = "alloc")]
pub mod session;
pub mod wire;

#[cfg(feature = "alloc")]
pub use channel::{Channel, Recv};
#[cfg(feature = "alloc")]
pub use drive::RunError;
pub use error::{Error, Reason};
pub use hash::{FP_LEN, Fingerprint, ID_LEN, item_id};
pub use index::ItemIndex;
pub use limits::Limits;
#[cfg(feature = "alloc")]
pub use mem::{MemError, MemIndex};
#[cfg(feature = "alloc")]
pub use session::{Entries, Initiator, Report, Responder, Step};
pub use wire::{first_set_ref, frame_body, frame_len};
