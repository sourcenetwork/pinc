//! The instrumented crypto: real cryptography that records where every secret came from, so the security gates are
//! decided on the real keys instead of on a symbolic model.
//!
//! [`Registry`] is the shared ledger of a run. [`Tracked`] is the [`pinc_crypto::Provider`] every node uses: it does
//! the real work (through [`pinc_crypto::Software`]), counts it for the CPU cost model ([`DeviceCosts`]) and records
//! the provenance [`Term`] of each secret. [`payload`] generates the self-identifying bytes of values and messages,
//! which lets the ledger find application payload in plaintext and tell whose bytes a datagram carries.
//! [`Registry::sec_verdict`] then decides the harvest-now-decrypt-later, forward-secrecy, nonce-reuse, plaintext and
//! amplification checks of the security gate.
//!
//! Invariants: one ledger per run and per thread, shared by all nodes of the run, because the term algebra is
//! shared (both ends of a Diffie-Hellman exchange get the same term). A secret is identified by its bytes. The key
//! schedule derives through `pinc_crypto::extract` and `expand`, not through the provider, so the ledger also
//! subscribes to those (see [`Registry::install`]); a key whose derivation was not seen has an unknown provenance,
//! and an unknown provenance that protected payload fails the verdict instead of passing it.
mod costs;
pub mod payload;
mod provider;
mod registry;
mod verdict;

pub use costs::{DeviceCosts, Work};
pub use payload::{BLOCK_LEN, MsgId, PayloadError, PayloadKind};
pub use provider::{Tracked, TrackedAeadKey, TrackedDecapsKey, TrackedEncapsKey, TrackedX25519};
pub use registry::{PayloadKey, Registry, Term, TermId};
pub use verdict::{Finding, NonceReuse, SecReport, WireScan};
