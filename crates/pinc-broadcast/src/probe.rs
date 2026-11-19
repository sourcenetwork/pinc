//! Read-only views of a node's topic state for the trace tests (`tests/trace_broadcast_push.rs`,
//! `trace_broadcast_repair.rs`, `trace_broadcast_subs.rs`), behind the `trace` feature. Nothing here changes state.

use pinc_membership::NodeId;

use crate::node::Topics;

impl Topics {
    /// The hub's log of `topic`: the sequence number of its oldest entry, the one after its newest, and the ring
    /// bytes in use; `(0, 0, 0)` while nothing was logged.
    pub fn log_bounds(&self, topic: &[u8]) -> (u64, u64, usize) {
        self.topics
            .get(topic)
            .and_then(|st| st.log.as_ref())
            .map_or((0, 0, 0), |l| (l.base(), l.end(), l.used()))
    }

    /// Whether the hub's log of `topic` holds the message `mid` (keyed as `hub_store` keys it).
    pub fn log_holds(&self, topic: &[u8], mid: &[u8; 8]) -> bool {
        self.topics
            .get(topic)
            .and_then(|st| st.log.as_ref())
            .is_some_and(|l| l.contains(u64::from_le_bytes(*mid)))
    }

    /// A subscriber's place in the hub's log of `topic`: the sequence number of the first message it has not been
    /// sent, and whether it was let go; `None` when it is not behind.
    pub fn push_place(&self, topic: &[u8], peer: &NodeId) -> Option<(u64, bool)> {
        self.topics.get(topic)?.behind.get(peer).map(|b| (b.next, b.held))
    }
}
