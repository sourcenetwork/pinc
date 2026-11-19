//! [`KeyHost`]: answers the handshake's key requests from a [`KeyStore`].
//!
//! The handshake machines never touch a long-term key. They name one by a [`pinc_security::KeyHandle`] and ask the
//! host to sign or decapsulate ([`KeyRequest`]). A `KeyHost` binds those handles to the store's own and serves the
//! request, so the endpoint and every relay carrier of a node use one path, and a key in a TPM or HSM serves both.
//!
//! Invariants: a request that names an unbound handle, asks for an algorithm other than the bound key's, or fails in
//! the store is answered [`KeyResponse::Failed`] and never with a guess; the signature buffer is wiped on drop.

use alloc::vec::Vec;

use pinc_security::{KeyHandle as SecHandle, KeyRequest, KeyResponse};
use zeroize::Zeroize;

use crate::{KeyHandle, KeyStore};

/// The longest signature any identity algorithm produces.
const SIG_MAX: usize = pinc_crypto::identity::MAX_SIGNATURE_LEN;

/// A store plus the binding from handshake key handles to its keys.
pub struct KeyHost<S: KeyStore> {
    store: S,
    bound: Vec<(SecHandle, KeyHandle)>,
    sig: [u8; SIG_MAX],
}

impl<S: KeyStore> core::fmt::Debug for KeyHost<S> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("KeyHost")
            .field("bound", &self.bound.len())
            .finish_non_exhaustive()
    }
}

impl<S: KeyStore> Drop for KeyHost<S> {
    fn drop(&mut self) {
        self.sig.zeroize();
    }
}

impl<S: KeyStore> KeyHost<S> {
    /// A host over `store` with no bindings.
    pub const fn new(store: S) -> Self {
        Self {
            store,
            bound: Vec::new(),
            sig: [0; SIG_MAX],
        }
    }

    /// Answer requests naming `handle` with the store's `key`. Binding a handle again replaces the earlier key.
    pub fn bind(&mut self, handle: SecHandle, key: KeyHandle) {
        self.bound.retain(|(h, _)| *h != handle);
        self.bound.push((handle, key));
    }

    /// The store, for the operations that are not key requests (random bytes, sealing).
    pub fn store(&mut self) -> &mut S {
        &mut self.store
    }

    /// Serve one request. The answer borrows the host's signature buffer until the next call.
    pub fn answer(&mut self, req: &KeyRequest<'_>) -> KeyResponse<'_> {
        match req {
            KeyRequest::Sign { key, alg, message } => {
                let Some((_, k)) = self.bound.iter().find(|(h, _)| h == key) else {
                    return KeyResponse::Failed;
                };
                let Ok(sig) = self.store.sign(k, message) else {
                    return KeyResponse::Failed;
                };
                let bytes = sig.as_bytes();
                match self.sig.get_mut(..bytes.len()) {
                    Some(dst) if sig.alg() == *alg => {
                        dst.copy_from_slice(bytes);
                        KeyResponse::Signature(self.sig.get(..bytes.len()).unwrap_or_default())
                    }
                    _ => KeyResponse::Failed,
                }
            }
            KeyRequest::Decapsulate { key, ct } => {
                let Some((_, k)) = self.bound.iter().find(|(h, _)| h == key) else {
                    return KeyResponse::Failed;
                };
                self.store
                    .decapsulate(k, *ct)
                    .map_or(KeyResponse::Failed, KeyResponse::SharedSecret)
            }
        }
    }
}
