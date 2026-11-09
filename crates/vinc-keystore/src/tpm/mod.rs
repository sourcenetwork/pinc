//! TPM 2.0 backend (feature `hwenc`): a pure-Rust client over `tpm2-protocol` and [`TpmStore`] on top of it.
//!
//! Only ECDSA P-256 identity keys and the sealing key can live in a TPM; everything else stays in a
//! [`SoftwareStore`](crate::SoftwareStore). Objects are created under a storage key derived from the owner seed,
//! so a blob created by one connection loads on any other connection to the same TPM.
//!
//! Invariants: transient TPM handles are flushed when the store is dropped, when an operation fails after loading
//! one, and when a key is made persistent (a flush the TPM refuses is retried before the next load); a command the TPM
//! answers with a "send it again" warning is resent within a bounded retry policy; the public key and node id of a key are read from the TPM, never
//! assumed; every signature is normalized to the low-`s` form `vinc_crypto` requires.

mod client;
mod store;
mod template;
mod transport;

pub use client::{
    Blob, EccPoint, MAX_AUTH_LEN, RC_INITIALIZE, RC_RETRY, RC_TESTING, RC_YIELDED, RetryPolicy, TpmClient,
};
pub use store::{TpmConfig, TpmStore};
pub use transport::{DeviceTransport, SimTransport, Transport};
