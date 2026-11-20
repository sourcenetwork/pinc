//! Probes of the access gate (feature `trace`), read and driven by `tests/trace_facade_gate.rs`.

use pinc_crypto::NodeId;

use super::Endpoint;
use crate::engine::trace_gate::GateProbe;
use crate::host::Hosted;

impl<H: Hosted, D> Endpoint<H, D> {
    /// The gate's tables for `peers` and the sessions the facade holds up; `None` while an endpoint call holds the core.
    #[doc(hidden)]
    pub fn trace_gate(&self, peers: &[NodeId]) -> Option<GateProbe> {
        let now = self.0.shared.now();
        self.0.shared.lock().map(|core| core.trace_gate(now, peers))
    }

    /// Whether an endpoint call holds the core now (the hook runs inside such a call).
    #[doc(hidden)]
    pub fn trace_busy(&self) -> bool {
        self.0.shared.lock().is_none()
    }

    /// Whether the node is thin now, as a dial handed over now would be told (the handshake has no early end then);
    /// `None` while an endpoint call holds the core.
    #[doc(hidden)]
    pub fn trace_thin(&self) -> Option<bool> {
        self.0.shared.lock().map(|core| core.node_stats().thin)
    }

    /// The endpoint's answer for `peer` runs out, as after 30 s.
    #[doc(hidden)]
    pub fn trace_expire(&self, peer: &NodeId) {
        if let Some(mut core) = self.0.shared.lock() {
            core.trace_expire(peer);
        }
    }

    /// The allow the facade remembers for `peer` runs out, as after 30 s.
    #[doc(hidden)]
    pub fn trace_lapse(&self, peer: &NodeId) {
        if let Some(mut core) = self.0.shared.lock() {
            core.trace_lapse(peer);
        }
    }
}
