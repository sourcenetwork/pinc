//! The port mapping on the endpoint's surface: the builder calls that turn it on and name the gateway, and the handle's
//! read of the mapping held. What the client does is in `pinc-portmap`; the endpoint starts it on build, routes its
//! datagrams and HTTP exchanges, and releases the mapping when it closes.
//!
//! Invariants: an endpoint built without [`Builder::port_mapping`], on a loopback address or with the relay role sends
//! nothing for port mapping and holds no mapping.

use core::net::{IpAddr, SocketAddr};

use super::{Builder, Discovery, Endpoint};
use crate::engine::Try;
use crate::host::Hosted;

impl<S, D, A, C, Q, Pf> Builder<S, D, A, C, Q, Pf> {
    /// Ask the home gateway for a UDP mapping of the endpoint's socket, so peers behind address translation of their
    /// own reach it directly (off by default). The endpoint tries PCP, then NAT-PMP, then `UPnP-IGD`, renews the lease
    /// before it ends, and deletes the mapping when it closes. A mapped address is published, first in the endpoint's
    /// signed record, only once a relay saw the endpoint at its IP, and the endpoint's reachability is then
    /// port-mapped. An external address no peer could reach (private, carrier-grade, loopback, link-local, multicast
    /// or unspecified) is never held.
    ///
    /// What an endpoint sends when it is on (an endpoint with the relay role, one on a loopback address and one with
    /// this off send nothing):
    ///
    /// | bound to | sent |
    /// |---|---|
    /// | a private IPv4 address (RFC 1918, 100.64.0.0/10), no [`gateway`](Self::gateway) | an `M-SEARCH` of 137 bytes to `239.255.255.250:1900` at 0, 1 and 2 s, again every 5 minutes |
    /// | a private IPv4 address and a gateway | PCP (60 bytes, three tries), then NAT-PMP, then the search; again every 5 minutes |
    /// | a public IPv4 address and a gateway | PCP, then NAT-PMP, again every 5 minutes; no search |
    /// | the unspecified address and a gateway | NAT-PMP only, every 5 minutes |
    /// | an IPv6 address and a gateway | PCP and NAT-PMP, three tries each, again every 5 minutes; no search |
    /// | a public IPv4 address, the unspecified address or IPv6, no gateway | nothing |
    ///
    /// With `UPnP` the description and control requests go to whatever TCP port the answering gateway names, so a host on
    /// the link that can spoof the gateway's address can make the endpoint send one HTTP request to any port of the
    /// gateway (and, with no gateway given, of any private host that answers the search). That is one reason the feature
    /// is off by default.
    ///
    /// `UPnP`'s HTTP calls go over the host's carriers ([`carriers`](Self::carriers)): `open` is asked for a TCP
    /// stream to a [`Relay`](crate::Relay) whose id is the endpoint's own and whose only address is the host that
    /// answered the search.
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
    /// A held mapping is not yet published: that waits for a relay to see the endpoint at its IP.
    pub async fn port_mapping(&self) -> Option<SocketAddr> {
        self.0
            .shared
            .run(|core, _| Try::Done(core.node.port_mapping().map(|(a, _)| a)))
            .await
    }

    /// What the port-mapping client dropped, by reason, and how often drawing its nonce failed; all zero when port
    /// mapping is off (see [`Builder::port_mapping`]).
    pub async fn port_mapping_stats(&self) -> crate::PortMapStats {
        self.0
            .shared
            .run(|core, _| Try::Done(core.node.port_mapping_stats()))
            .await
    }
}
