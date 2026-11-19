//! PINC delay-tolerant delivery (DTN): bundles that cross links which are rarely up, with no live handshake.
//!
//! A sender encrypts a payload once to the recipient's static ML-KEM-768 and X25519 keys ([`seal`]), cuts it into
//! equal sealed slices, adds Reed-Solomon parity per block ([`rs`]) and commits to every slice with one BLAKE3 root
//! ([`bundle`]). The signed [`head::SignedHead`] names the bundle; any slice is checked against the root with a range
//! proof, so a partial bundle is usable and a reception is resumable. Custody ([`custody`]) moves responsibility
//! for a bundle between nodes with signed acknowledgements. The charged [`store::Ledger`] bounds what a node keeps,
//! and the [`forward::Forwarder`] decides where the limited copies go.
//!
//! The crate is `no_std`, never allocates (every table is a const-generic array and every buffer is the caller's),
//! never reads a clock or randomness (time and seeds are inputs) and never panics on any input. Every state machine
//! is deterministic: the same inputs give the same outputs, which is what the TLA+ and Lean models rely on.
#![no_std]
#![forbid(unsafe_code)]

pub mod bundle;
pub mod custody;
mod endorse;
pub mod error;
pub mod forward;
pub mod gf256;
pub mod head;
pub mod held;
pub mod labels;
pub mod layout;
pub mod rs;
pub mod seal;
pub mod store;

pub use error::DtnError;
/// The hybrid logical clock lives in `pinc-wire`; it is re-exported so this crate's API is unchanged.
pub use pinc_wire::hlc;
