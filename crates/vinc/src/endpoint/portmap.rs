//! The port mapping on the endpoint's surface: the builder calls that turn it on and name the gateway, and the handle's
//! read of the mapping held. What the client does is in `vinc-portmap`; the endpoint starts it on build, routes its
//! datagrams and HTTP exchanges, and releases the mapping when it closes.
//!
//! Invariants: an endpoint built with [`Builder::port_mapping`] off or on a loopback address sends nothing for port
//! mapping and holds no mapping.

use std::net::{IpAddr, SocketAddr};

use super::{Builder, Discovery, Endpoint};
use crate::engine::Try;
use crate::host::Hosted;

impl<S, D, A, C, Q> Builder<S, D, A, C, Q> {
    /// Ask the home gateway for a UDP mapping of the endpoint's socket, so peers behind address translation of their
    /// own reach it directly (on by default). The endpoint tries PCP, then NAT-PMP, then `UPnP-IGD`, renews the lease
    /// before it ends, and deletes the mapping when it closes. The mapped address leads the addresses its signed
    /// record lists, and the endpoint's reachability is port-mapped while it holds one.
    ///
    /// PCP and NAT-PMP need the gateway's address ([`gateway`](Self::gateway)); without it only `UPnP` is tried, by an
    /// SSDP search. PCP and `UPnP` name the endpoint's own address, so an endpoint bound to the unspecified address
    /// tries NAT-PMP only. `UPnP`'s HTTP calls go over the host's carriers ([`carriers`](Self::carriers)): `open` is
    /// then asked for a TCP stream to a [`Relay`](crate::Relay) whose id is the endpoint's own and whose only address
    /// is the gateway's control address. An endpoint on a loopback address asks nothing.
    #[must_use]
    pub const fn port_mapping(mut self, on: bool) -> Self {
        self.port_mapping.on = on;
        self
    }

    /// The default gateway of the host's network: where PCP and NAT-PMP requests go, and the only address an SSDP
    /// answer is taken from.
    #[must_use]
    pub const fn gateway(mut self, gateway: IpAddr) -> Self {
        self.port_mapping.gateway = Some(gateway);
        self
    }
}

impl<H: Hosted, D: Discovery> Endpoint<H, D> {
    /// The external address of the port mapping the gateway granted (see [`Builder::port_mapping`]), if one is held.
    pub async fn port_mapping(&self) -> Option<SocketAddr> {
        self.0
            .shared
            .run(|core, _| Try::Done(core.node.port_mapping().map(|(a, _)| a)))
            .await
    }
}
