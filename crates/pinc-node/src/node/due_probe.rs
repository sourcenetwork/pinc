//! A probe of the node's deadline cache, for the trace check (cargo feature `trace`): it reads the cache, answers
//! [`Node::poll_timeout`]'s question as the host would and works the answer out again from nothing.

use pinc_crypto::Provider;

use super::{Due, Node};
use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;

/// What [`Node::trace_due`] read of the deadline cache.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DueProbe {
    /// The cache before the ask: 0 stale, 1 the endpoint's part only, 2 known.
    pub kind: u8,
    /// The answer of the node's deadline.
    pub due: Option<Nanos>,
    /// The endpoint's deadline.
    pub ep: Option<Nanos>,
    /// The layers' part the answer used.
    pub layers: Option<Nanos>,
    /// The layers' deadline worked out again at the clock that part was taken at.
    pub layers_at: Option<Nanos>,
    /// The deadline of the endpoint and the layers worked out at the clock now.
    pub fresh: Option<Nanos>,
    /// The layers' deadline worked out at the clock now.
    pub fresh_layers: Option<Nanos>,
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// Read the deadline cache, answer the node's deadline as the host would and work the answer out fresh.
    pub fn trace_due(&self) -> DueProbe {
        let (kind, held) = match self.deadline.get() {
            Due::Stale => (0, None),
            Due::Endpoint(l) => (1, Some(l)),
            Due::Known(_, l) => (2, Some(l)),
        };
        let due = self.due();
        let fresh_layers = self.layers_deadline(self.io.now);
        DueProbe {
            kind,
            due,
            ep: self.ep_deadline(),
            layers: held.map_or(fresh_layers, |l| l.due),
            layers_at: held.map_or(fresh_layers, |l| self.layers_deadline(l.at)),
            fresh: self.with_endpoint(fresh_layers),
            fresh_layers,
        }
    }
}
