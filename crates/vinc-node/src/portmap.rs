//! The node's port-mapping client (`vinc-portmap`): the host turns it on with the node's socket and its default
//! gateway, the node routes the gateway's datagrams to it, sends what it wants sent, runs its timers, and gives the
//! mapped address to the connectivity client, which lists it first in the signed record and classifies the node as
//! port-mapped once a relay saw the node at its IP. The client's HTTP requests (`UPnP`) are the host's to carry over TCP.
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

/// How long after a failed draw of the nonce the node draws again, in nanoseconds.
const NONCE_RETRY: Nanos = 1_000_000_000;

/// What the client is started with.
#[derive(Debug, Clone, Copy)]
struct Ask {
    gateway: Option<IpAddr>,
    local: SocketAddr,
    lifetime: u32,
}

/// The port-mapping client (none until a nonce could be drawn), what it was started with, when the draw is tried
/// again, and the address the connectivity client was last given.
#[derive(Debug)]
pub(crate) struct Pm {
    client: Option<PortMap>,
    ask: Ask,
    retry: Nanos,
    nonce_failures: u64,
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
        self.pm = Some(alloc::boxed::Box::new(Pm {
            client: None,
            ask: Ask {
                gateway,
                local,
                lifetime,
            },
            retry: now,
            nonce_failures: 0,
            given: None,
        }));
        self.pm_seed(now);
        self.settle(now);
    }

    /// Start the client once a nonce is drawn: the nonce is the only thing that tells the gateway's PCP answers from
    /// another host's, so nothing is asked without one. A failed draw is counted and tried again after
    /// [`NONCE_RETRY`].
    fn pm_seed(&mut self, now: Nanos) {
        let Some(pm) = &mut self.pm else { return };
        if pm.client.is_some() {
            return;
        }
        let mut nonce = [0u8; 12];
        if self.drbg.fill(&mut nonce).is_ok() {
            let mut cfg = Config::new(pm.ask.gateway, pm.ask.local, nonce);
            cfg.lifetime = pm.ask.lifetime;
            pm.client = Some(PortMap::new(cfg, now));
        } else {
            pm.nonce_failures = pm.nonce_failures.saturating_add(1);
            pm.retry = now.saturating_add(NONCE_RETRY);
        }
        self.deadline.set(Due::Stale);
    }

    /// Drop the mapping and ask the gateway to delete it; the host sends what [`Node::poll_udp`] and
    /// [`Node::poll_http`] give next.
    pub fn stop_port_mapping(&mut self, now: Nanos) {
        self.begin(now);
        match self.pm.as_mut().map(|pm| pm.client.as_mut()) {
            Some(Some(client)) => client.stop(now),
            // never started: nothing was asked, so nothing is released
            Some(None) => self.pm = None,
            None => {}
        }
        self.pm_apply(now);
    }

    /// The network changed: the mapping held is dropped and released, and the client asks again from the beginning.
    pub(crate) fn pm_restart(&mut self, now: Nanos) {
        if let Some(client) = self.pm.as_mut().and_then(|pm| pm.client.as_mut()) {
            client.restart(now);
        }
        self.pm_apply(now);
    }

    /// Whether the port-mapping client has nothing more to do: never turned on, or stopped and its release sent.
    pub fn port_mapping_done(&self) -> bool {
        self.pm
            .as_ref()
            .is_none_or(|pm| pm.client.as_ref().is_some_and(PortMap::stopped))
    }

    /// The mapping held: its external address and the protocol that granted it.
    pub fn port_mapping(&self) -> Option<(SocketAddr, Proto)> {
        let client = self.pm.as_ref()?.client.as_ref()?;
        Some((client.mapped()?, client.protocol()?))
    }

    /// The next HTTP request of the port-mapping client: where to open a TCP connection and the request's length in
    /// `buf` ([`vinc_portmap::upnp::MAX_REQUEST`] bytes hold any). The host writes it, reads the answer until the server closes it (at most
    /// [`vinc_portmap::MAX_RESPONSE`] bytes) and hands it to [`Node::handle_http`].
    pub fn poll_http(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.deadline.set(Due::Stale);
        self.pm.as_mut()?.client.as_mut()?.poll_http(buf)
    }

    /// Whether the port-mapping client still waits for the answer to the HTTP request it gave out. When it does not
    /// (its deadline passed), the host drops the exchange it runs and polls [`Node::poll_http`] again.
    pub fn http_awaited(&self) -> bool {
        self.pm
            .as_ref()
            .and_then(|pm| pm.client.as_ref())
            .is_some_and(PortMap::awaiting_http)
    }

    /// The answer to the last HTTP request, or `None` if its connection failed.
    pub fn handle_http(&mut self, now: Nanos, resp: Option<&[u8]>) {
        self.begin(now);
        if let Some(client) = self.pm.as_mut().and_then(|pm| pm.client.as_mut()) {
            client.handle_http(now, resp);
        }
        self.pm_apply(now);
        self.settle(now);
    }

    /// A datagram from `remote` for the port-mapping client: handled, and true; otherwise false.
    pub(crate) fn pm_datagram(&mut self, now: Nanos, remote: SocketAddr, d: &[u8]) -> bool {
        let Some(client) = self.pm.as_mut().and_then(|pm| pm.client.as_mut()) else {
            return false;
        };
        if !client.owns(remote, d) {
            return false;
        }
        client.handle_datagram(now, remote, d);
        self.pm_apply(now);
        true
    }

    pub(crate) fn pm_timeout(&mut self, now: Nanos) {
        if self
            .pm
            .as_ref()
            .is_some_and(|pm| pm.client.is_none() && pm.retry <= now)
        {
            self.pm_seed(now);
            self.pm_apply(now);
        }
        if let Some(client) = self.pm.as_mut().and_then(|pm| pm.client.as_mut())
            && client.poll_timeout().is_some_and(|t| t <= now)
        {
            client.handle_timeout(now);
            self.pm_apply(now);
        }
    }

    pub(crate) fn pm_deadline(&self) -> Option<Nanos> {
        let pm = self.pm.as_ref()?;
        match &pm.client {
            Some(client) => client.poll_timeout(),
            None => Some(pm.retry),
        }
    }

    pub(crate) fn pm_poll_udp(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.pm.as_mut()?.client.as_mut()?.poll_datagram(buf)
    }

    /// Give the connectivity client the address the port-mapping client holds, if it changed.
    fn pm_apply(&mut self, now: Nanos) {
        let Some(pm) = &mut self.pm else { return };
        let held = pm.client.as_ref().and_then(PortMap::mapped);
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
