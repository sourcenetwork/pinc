//! Probes of the access gate for `tests/trace_facade_gate.rs` (feature `trace`): what the endpoint's per-peer answers,
//! the facade's remembered allows and the facade's live sessions hold, and the two lapses of time those answers have.
//!
//! Invariant: `trace_gate` only reads; `trace_expire` and `trace_lapse` drop what the clock would drop after 30 s.

use alloc::vec::Vec;

use pinc_core::{Answer, Query};
use pinc_crypto::NodeId;
use pinc_keystore::KeyStore;

use super::{Admit, Core, Direction};

/// What the gate's tables hold for the peers a probe asked about, at one instant.
#[derive(Debug, Clone, Default)]
#[doc(hidden)]
pub struct GateProbe {
    /// Per asked peer: the endpoint's answer while it stands (`Some(allow)`), else `None`.
    pub cache: Vec<Option<bool>>,
    /// Per asked peer: the allow the facade remembers (protocol, direction) while it stands, else `None`.
    pub known: Vec<Option<(Vec<u8>, Direction)>>,
    /// The sessions the facade holds up: peer, protocol, whether this node dialed.
    pub sessions: Vec<(NodeId, Vec<u8>, bool)>,
}

impl<S: KeyStore, A: Admit> Core<S, A> {
    /// The gate's tables for `peers` at `now`.
    pub(crate) fn trace_gate(&self, now: u64, peers: &[NodeId]) -> GateProbe {
        GateProbe {
            cache: peers
                .iter()
                .map(|p| match self.node.endpoint().query(Query::Access(*p)) {
                    Answer::Access { allow, until } if until > now => Some(allow),
                    _ => None,
                })
                .collect(),
            known: peers
                .iter()
                .map(|p| self.known.peek(now, p).map(|(a, d)| (a.as_bytes().to_vec(), d)))
                .collect(),
            sessions: self
                .sessions
                .values()
                .map(|s| (s.info.node, s.info.alpn.as_bytes().to_vec(), s.info.dialer))
                .collect(),
        }
    }

    /// The endpoint's answer for `peer` runs out.
    pub(crate) fn trace_expire(&mut self, peer: &NodeId) {
        self.node.forget_access(&peer.bytes);
    }

    /// The allow the facade remembers for `peer` runs out.
    pub(crate) fn trace_lapse(&mut self, peer: &NodeId) {
        self.known.forget(&peer.bytes);
    }
}
