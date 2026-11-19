//! The discovery hook of the builder: where an endpoint looks for the addresses of a node the caller gave none for.
//!
//! Invariants: a discovery is asked before a dial starts, so dropping the dial while it runs leaves nothing behind.

use alloc::vec::Vec;
use core::future::Future;
use core::net::SocketAddr;

use pinc_crypto::NodeId;

/// Finds addresses for a node the caller gave none for. It may do I/O; it runs before the dial starts, so dropping the
/// dial while it runs leaves nothing behind.
pub trait Discovery {
    /// The addresses `node` may be reached at; empty if unknown.
    fn lookup(&self, node: &NodeId) -> impl Future<Output = Vec<SocketAddr>>;

    /// Called once as the endpoint is built, with the seed and the secrets for the hash tables the discovery keeps; a
    /// discovery with no table ignores them.
    #[doc(hidden)]
    fn seed_maps(&self, _seed: u64, _secrets: &'static [u64; 7]) {}
}

/// No discovery: a dial without addresses uses the address book only.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoDiscovery;

impl Discovery for NoDiscovery {
    fn lookup(&self, _node: &NodeId) -> impl Future<Output = Vec<SocketAddr>> {
        core::future::ready(Vec::new())
    }
}
