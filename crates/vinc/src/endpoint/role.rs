//! The relay role on the endpoint's surface: the builder call that gives an endpoint the role, and the role's counters,
//! events and carrier control on the endpoint's handle. What the role is and how it is driven is in [`crate::role`].
//!
//! Invariants: nothing here borrows the role across a call of the host; an endpoint without the role answers every
//! call with nothing.

use vinc_crypto::NodeId;
use vinc_keystore::SoftwareStore;

use super::{Builder, Discovery, Endpoint};
use crate::host::Hosted;
use crate::role::{RelayRole, Role};

impl<S, D, A, C, Q> Builder<S, D, A, C, Q> {
    /// Give the endpoint the relay role: it serves as a relay for other nodes beside being a node itself, on its own
    /// identity, socket and clock. `relay` holds the relay's limits, record store and access rule (start it with
    /// [`relay::Relay::builder`](crate::relay::Relay::builder); its identity and tunnel are the endpoint's), and
    /// `carriers` are the host's byte streams: where the streams its members open arrive (accept) and how they are read,
    /// written and closed (see [`relay::CarrierFns`](crate::relay::CarrierFns)). Members of the relay name this
    /// endpoint with [`relays`](Self::relays), and with [`hub`](Self::hub) it is their hub too.
    ///
    /// The role is driven by [`Endpoint::run`]: await it for as long as the relay should serve, and on that one
    /// future only (the other futures of the endpoint wait on it instead of driving the endpoint themselves), because
    /// the operations of the carriers in flight live in it. The counters and events of the relay are
    /// [`Endpoint::relay_stats`] and [`Endpoint::next_relay_event`].
    #[must_use]
    pub fn relay_role<RC, St, RA>(
        self,
        relay: crate::relay::Builder<SoftwareStore, St, RA>,
        carriers: RC,
    ) -> Builder<S, D, A, C, RelayRole<RC, St, RA>>
    where
        RC: crate::relay::Carriers,
        St: crate::relay::Store,
        RA: crate::relay::Access,
    {
        Builder {
            identity: self.identity,
            alpns: self.alpns,
            relays: self.relays,
            discovery: self.discovery,
            limits: self.limits,
            admission: self.admission,
            batch: self.batch,
            mtu: self.mtu,
            local: self.local,
            carriers: self.carriers,
            hub: self.hub,
            connected_topics: self.connected_topics,
            connect_timeout: self.connect_timeout,
            role: RelayRole {
                builder: relay,
                carriers,
            },
        }
    }
}

impl<H: Hosted, D: Discovery> Endpoint<H, D> {
    /// The counters of the relay role; `None` if the endpoint has none ([`Builder::relay_role`]).
    pub fn relay_stats(&self) -> Option<crate::relay::Stats> {
        self.0.shared.role()?.stats()
    }

    /// The oldest event of the relay role nobody has read yet; `None` if there is none or the endpoint has no relay role.
    pub fn next_relay_event(&self) -> Option<crate::relay::Event> {
        self.0.shared.role()?.next_event()
    }

    /// End the relay carrier of `node`, if it holds one here (its right to a relay was withdrawn); whether it did.
    pub fn close_relay_carrier(&self, node: &NodeId) -> bool {
        let closed = self.0.shared.role().is_some_and(|mut r| r.close_carrier(node));
        if closed && let Some(mut core) = self.0.shared.lock() {
            core.wake_driver();
        }
        closed
    }
}
