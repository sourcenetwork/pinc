//! PINC primitives behind one static interface.
//!
//! The [`Provider`] trait covers the per-packet and per-handshake primitives (AEAD, header protection, SHA-256,
//! X25519, ML-KEM-768); [`Software`] implements it from vetted pure-Rust crates. [`identity`] holds the signature
//! algorithms and node ids, [`kdf`] the BLAKE3 key derivation, [`setsum`] the multiset hash over the Ristretto group, [`Transcript`] the injective handshake hash and
//! [`Drbg`] the seeded generator.
//!
//! The crate is `no_std`; with the `alloc` feature it allocates in one place, once per ML-DSA-65 or hybrid key pair:
//! [`identity::Keypair::from_seed`] boxes the expanded key (see [`identity`]). Ed25519 and P-256 key pairs never
//! allocate, and no wire, sign or verify path does; when a key pair is built (at setup) is the caller's choice. The
//! feature is off by default and the crate never allocates without it; the facade, the node crate, the key store and
//! the transport's own `alloc` feature turn it on. It never reads randomness (every key generation takes seed bytes
//! from the caller) and never panics on any input. Secrets are zeroized on drop and compared in constant time.
//!
//! The test-only `trace` feature records what every [`Transcript`] absorbs once a thread arms it (it needs `std` and
//! allocates then); it is off by default and costs nothing off.
//! The optional `derive-trace` feature (for test and simulation builds only; it needs `std`) lets a host observe
//! every [`extract`] and [`expand`] call through [`trace`], so a simulator can follow which secrets a key derives from.
#![cfg_attr(not(feature = "derive-trace"), no_std)]
#![forbid(unsafe_code)]

#[cfg(feature = "trace")]
extern crate std;

pub mod drbg;
pub mod error;
pub mod identity;
pub mod kdf;
pub mod provider;
pub mod secret;
pub mod setsum;
pub mod software;
#[cfg(feature = "derive-trace")]
pub mod trace;
pub mod transcript;

pub use drbg::Drbg;
pub use error::CryptoError;
pub use identity::{IdentityAlg, Keypair, NodeId};
pub use kdf::{expand, extract, labels};
pub use provider::{Aead, Capabilities, Provider};
pub use secret::{Secret, ct_eq};
pub use setsum::SetSum;
pub use software::Software;
pub use transcript::Transcript;
