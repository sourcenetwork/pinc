//! VINC primitives behind one static interface.
//!
//! The [`Provider`] trait covers the per-packet and per-handshake primitives (AEAD, header protection, SHA-256,
//! X25519, ML-KEM-768); [`Software`] implements it from vetted pure-Rust crates. [`identity`] holds the signature
//! algorithms and node ids, [`kdf`] the BLAKE3 key derivation, [`Transcript`] the injective handshake hash and
//! [`Drbg`] the seeded generator.
//!
//! The crate is `no_std`, never allocates, never reads randomness (every key generation takes seed bytes from the
//! caller) and never panics on any input. Secrets are zeroized on drop and compared in constant time.
//!
//! The test-only `trace` feature records what every [`Transcript`] absorbs once a thread arms it (it needs `std` and
//! allocates then); it is off by default and costs nothing off.
#![no_std]
#![forbid(unsafe_code)]

#[cfg(feature = "trace")]
extern crate std;

pub mod drbg;
pub mod error;
pub mod identity;
pub mod kdf;
pub mod provider;
pub mod secret;
pub mod software;
pub mod transcript;

pub use drbg::Drbg;
pub use error::CryptoError;
pub use identity::{IdentityAlg, Keypair, NodeId};
pub use kdf::{expand, extract, labels};
pub use provider::{Aead, Capabilities, Provider};
pub use secret::{Secret, ct_eq};
pub use software::Software;
pub use transcript::Transcript;
