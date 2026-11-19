//! The access policy: who may hold a carrier.
//!
//! The relay asks once per carrier, after the handshake has shown which node opened it and before the carrier is
//! admitted. The answer is a plain yes or no from the embedder's own state; the relay never holds a lock or a borrow of
//! the embedder across the call. To withdraw a right later, the embedder calls `Part::close_carrier`.

use pinc_crypto::NodeId;

/// Decides which nodes may hold a carrier.
pub trait Access {
    /// Whether `node`, whose handshake has just finished, may hold a carrier. A refusal closes the carrier and counts it
    /// in `Stats::carriers_denied`.
    fn admit(&mut self, node: &NodeId) -> bool;
}

/// Every node that proves its identity may hold a carrier.
#[derive(Debug, Clone, Copy, Default)]
pub struct AllowAll;

impl Access for AllowAll {
    fn admit(&mut self, _: &NodeId) -> bool {
        true
    }
}
