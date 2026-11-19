//! What survives a restart, on the endpoint.
//!
//! [`export_state`](Endpoint::export_state) gives the bytes to keep; a restarted endpoint with the same identity takes them
//! back with [`restore_state`](Endpoint::restore_state) before it dials, and its first dial to a peer from before the
//! restart resumes the session ([`Connection::resumed`](crate::Connection::resumed)). The bytes hold pre-shared keys:
//! seal them with [`seal_state`](Endpoint::seal_state) before they reach a disk.

use crate::endpoint::{Discovery, Endpoint};
use crate::engine::{Restored, Try};
use crate::error::Result;
use crate::host::Hosted;
use alloc::vec::Vec;

impl<H: Hosted, D: Discovery> Endpoint<H, D> {
    /// The state to keep across a restart: resumption tickets, per-peer round trips and prekey caches, and the address
    /// book. Secret: see [`seal_state`](Self::seal_state).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the state does not fit its buffer.
    pub async fn export_state(&self) -> Result<Vec<u8>> {
        self.0.shared.run(|core, now| Try::Done(core.export_state(now))).await
    }

    /// Load state made by [`export_state`](Self::export_state) by an endpoint with this identity; tickets that expired are
    /// skipped. Nothing changes when the bytes are not exactly one state.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] for bytes that are not a state.
    pub async fn restore_state(&self, state: &[u8]) -> Result<Restored> {
        self.0
            .shared
            .run(|core, now| Try::Done(core.restore_state(now, state)))
            .await
    }

    /// Seal `state` with the identity's key store, for a disk.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the store fails.
    pub async fn seal_state(&self, state: &[u8]) -> Result<Vec<u8>> {
        self.0.shared.run(|core, _| Try::Done(core.seal(state))).await
    }

    /// Open bytes made by [`seal_state`](Self::seal_state).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the bytes were altered or sealed by another store.
    pub async fn unseal_state(&self, sealed: &[u8]) -> Result<Vec<u8>> {
        self.0.shared.run(|core, _| Try::Done(core.unseal(sealed))).await
    }
}
