//! The node's port-mapping client (`vinc-portmap`): the host turns it on with the node's socket and its default
//! gateway, the node routes the gateway's datagrams to it, sends what it wants sent, runs its timers, and gives the
//! mapped address to the connectivity client, which lists it first in the signed record and classifies the node as
//! port-mapped. The client's HTTP requests (`UPnP`) are the host's to carry over TCP.
//!
//! Invariants: the connectivity client holds exactly the address the port-mapping client holds, after every call that
//! could change it; a node whose host never turned port mapping on sends nothing for it and arms no timer for it.

use core::net::{IpAddr, SocketAddr};

use vinc_crypto::Provider;
use vinc_portmap::{Config, PortMap, Proto};

use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;
use crate::node::{Due, Node};

/// The port-mapping client and the address the connectivity client was last given.
#[derive(Debug)]
pub(crate) struct Pm {
    client: PortMap,
    given: Option<SocketAddr>,
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// Ask the gateway for a UDP mapping of the socket `local`, from `now` on, for leases of `lifetime` seconds.
    /// `gateway` is the host's default gateway; without it only `UPnP` is tried. A call while one runs starts over.
    pub fn start_port_mapping(&mut self, now: Nanos, gateway: Option<IpAddr>, local: SocketAddr, lifetime: u32) {
        self.begin(now);
        let mut nonce = [0u8; 12];
        // A nonce nothing secret depends on: it only tells this client's PCP answers from others'.
        let _ = self.drbg.fill(&mut nonce);
        let mut cfg = Config::new(gateway, local, nonce);
        cfg.lifetime = lifetime;
        self.pm = Some(alloc::boxed::Box::new(Pm {
            client: PortMap::new(cfg, now),
            given: None,
        }));
        self.settle(now);
    }

    /// Drop the mapping and ask the gateway to delete it; the host sends what [`Node::poll_udp`] and
    /// [`Node::poll_http`] give next.
    pub fn stop_port_mapping(&mut self, now: Nanos) {
        self.begin(now);
        if let Some(pm) = &mut self.pm {
            pm.client.stop(now);
        }
        self.pm_apply(now);
    }

    /// Whether the port-mapping client has nothing more to do: never turned on, or stopped and its release sent.
    pub fn port_mapping_done(&self) -> bool {
        self.pm.as_ref().is_none_or(|pm| pm.client.stopped())
    }

    /// The mapping held: its external address and the protocol that granted it.
    pub fn port_mapping(&self) -> Option<(SocketAddr, Proto)> {
        let pm = self.pm.as_ref()?;
        Some((pm.client.mapped()?, pm.client.protocol()?))
    }

    /// The next HTTP request of the port-mapping client: where to open a TCP connection and the request's length in
    /// `buf` ([`vinc_portmap::upnp::MAX_REQUEST`] bytes hold any). The host writes it, reads the answer until the server closes it (at most
    /// [`vinc_portmap::MAX_RESPONSE`] bytes) and hands it to [`Node::handle_http`].
    pub fn poll_http(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.deadline.set(Due::Stale);
        self.pm.as_mut()?.client.poll_http(buf)
    }

    /// The answer to the last HTTP request, or `None` if its connection failed.
    pub fn handle_http(&mut self, now: Nanos, resp: Option<&[u8]>) {
        self.begin(now);
        if let Some(pm) = &mut self.pm {
            pm.client.handle_http(now, resp);
        }
        self.pm_apply(now);
        self.settle(now);
    }

    /// A datagram from `remote` for the port-mapping client: handled, and true; otherwise false.
    pub(crate) fn pm_datagram(&mut self, now: Nanos, remote: SocketAddr, d: &[u8]) -> bool {
        let Some(pm) = &mut self.pm else { return false };
        if !pm.client.owns(remote, d) {
            return false;
        }
        pm.client.handle_datagram(now, remote, d);
        self.pm_apply(now);
        true
    }

    pub(crate) fn pm_timeout(&mut self, now: Nanos) {
        if let Some(pm) = &mut self.pm
            && pm.client.poll_timeout().is_some_and(|t| t <= now)
        {
            pm.client.handle_timeout(now);
            self.pm_apply(now);
        }
    }

    pub(crate) fn pm_deadline(&self) -> Option<Nanos> {
        self.pm.as_ref()?.client.poll_timeout()
    }

    pub(crate) fn pm_poll_udp(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.pm.as_mut()?.client.poll_datagram(buf)
    }

    /// Give the connectivity client the address the port-mapping client holds, if it changed.
    fn pm_apply(&mut self, now: Nanos) {
        let Some(pm) = &mut self.pm else { return };
        let held = pm.client.mapped();
        if held == pm.given {
            return;
        }
        pm.given = held;
        self.deadline.set(Due::Stale);
        match held {
            Some(a) => self.conn.set_mapped(now, &[a]),
            None => self.conn.set_mapped(now, &[]),
        }
    }
}
