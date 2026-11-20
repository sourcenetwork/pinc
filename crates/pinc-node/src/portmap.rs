//! The node's port-mapping client (`pinc-portmap`): the host turns it on with the node's socket and its default
//! gateway, the node routes the gateway's datagrams to it, sends what it wants sent, runs its timers, and gives the
//! mapped address to the connectivity client, which lists it first in the signed record and classifies the node as
//! port-mapped once a relay saw the node at its IP. The client's HTTP requests (`UPnP`) are the host's to carry over TCP.
//!
//! Invariants: the connectivity client holds exactly the address the port-mapping client holds, after every call that
//! could change it; a node whose host never turned port mapping on sends nothing for it and arms no timer for it.

use core::net::{IpAddr, SocketAddr};

use pinc_crypto::Provider;
use pinc_portmap::{Config, PortMap, Proto};

use crate::apps::{Apps, ServeSource};
use crate::config::{Nanos, Store};
use crate::ep::Ep;
use crate::node::{Due, Node};

/// What the port-mapping client dropped, and how often the node failed to draw its nonce.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct PortMapStats {
    /// What the client dropped, by reason.
    pub client: pinc_portmap::Stats,
    /// Draws of the nonce that failed: the client starts at the next try.
    pub nonce_failures: u64,
    /// Releases of earlier starts that were replaced, unsent, because more than four waited.
    pub release_overflows: u64,
}

/// What [`Node::pm_view`] gives.
#[cfg(feature = "trace")]
#[doc(hidden)]
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[allow(clippy::struct_excessive_bools, reason = "independent flags of the view")]
pub struct PmView {
    /// The host turned port mapping on (a `Pm` exists).
    pub on: bool,
    /// The client exists (its nonce was drawn).
    pub client: bool,
    /// The address the client holds (`PortMap::mapped`).
    pub held: Option<SocketAddr>,
    /// The address the connectivity client was last given.
    pub given: Option<SocketAddr>,
    /// The first mapped address the connectivity client holds.
    pub conn: Option<SocketAddr>,
    /// Retiring slots taken.
    pub retiring: usize,
    /// `release_overflows`.
    pub overflows: u64,
    /// `halted`.
    pub halted: bool,
    /// `pm_deadline().is_some()`.
    pub timer: bool,
    /// `nonce_failures`.
    pub nonce_failures: u64,
}

/// The most stopped clients whose release is still on the way.
const RETIRING: usize = 4;

/// How long after a failed draw of the nonce the node draws again, in nanoseconds.
const NONCE_RETRY: Nanos = 1_000_000_000;

/// What the client is started with.
#[derive(Debug, Clone, Copy)]
struct Ask {
    gateway: Option<IpAddr>,
    local: SocketAddr,
    lifetime: u32,
}

/// The port-mapping client (none until a nonce could be drawn), the stopped client of an earlier start while its release
/// is still on the way, what the client was started with, when the draw is tried again, and the address the
/// connectivity client was last given.
#[derive(Debug)]
pub(crate) struct Pm {
    client: Option<PortMap>,
    retiring: [Option<PortMap>; RETIRING],
    overflows: u64,
    ask: Ask,
    retry: Nanos,
    halted: bool,
    nonce_failures: u64,
    given: Option<SocketAddr>,
}

impl Pm {
    /// The clients that send, the one retiring first: its release goes out before the new client asks.
    fn sending(&mut self) -> impl Iterator<Item = &mut PortMap> {
        self.retiring.iter_mut().flatten().chain(self.client.iter_mut())
    }

    /// Forget a retiring client whose release is sent.
    fn reap(&mut self) {
        for r in &mut self.retiring {
            *r = r.take().filter(|c| !c.stopped());
        }
        // Keep the queue in the order the clients were stopped: the oldest first, no gap before a client.
        let mut next = 0;
        for i in 0..RETIRING {
            if self.retiring.get(i).is_some_and(Option::is_some) {
                self.retiring.swap(next, i);
                next += 1;
            }
        }
    }
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
    /// `gateway` is the host's default gateway; without it only `UPnP` is tried. A call while one runs starts over: the
    /// old client is stopped, its release goes out, and the address it published is withdrawn before the new client
    /// asks.
    pub fn start_port_mapping(&mut self, now: Nanos, gateway: Option<IpAddr>, local: SocketAddr, lifetime: u32) {
        self.begin(now);
        // The stopped client waits for its release in a fixed queue; a start that finds it full replaces the oldest
        // release, counted in the statistics (a release is one datagram, or a delete over HTTP).
        let old = self.pm.take();
        let mut given = None;
        let mut overflows = 0;
        let mut retiring: [Option<PortMap>; RETIRING] = core::array::from_fn(|_| None);
        if let Some(old) = old {
            given = old.given;
            overflows = old.overflows;
            retiring = old.retiring;
            if let Some(mut c) = old.client {
                c.stop(now);
                if !c.stopped() {
                    let slot = retiring.iter().position(Option::is_none).unwrap_or_else(|| {
                        overflows = overflows.saturating_add(1);
                        // The oldest release goes: it moves to the end and is overwritten there.
                        retiring.rotate_left(1);
                        RETIRING - 1
                    });
                    if let Some(r) = retiring.get_mut(slot) {
                        *r = Some(c);
                    }
                }
            }
        }
        self.pm = Some(alloc::boxed::Box::new(Pm {
            client: None,
            retiring,
            overflows,
            ask: Ask {
                gateway,
                local,
                lifetime,
            },
            retry: now,
            halted: false,
            nonce_failures: 0,
            given,
        }));
        self.pm_seed(now);
        self.pm_apply(now);
        self.settle(now);
    }

    /// Start the client once a nonce is drawn: the nonce is the only thing that tells the gateway's PCP answers from
    /// another host's, so nothing is asked without one. A failed draw is counted and tried again after
    /// [`NONCE_RETRY`].
    fn pm_seed(&mut self, now: Nanos) {
        let Some(pm) = &mut self.pm else { return };
        if pm.client.is_some() || pm.halted {
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
            // never started: nothing was asked, so nothing is released, and nothing is started later
            Some(None) => {
                if let Some(pm) = &mut self.pm {
                    pm.halted = true;
                    if pm.retiring.iter().all(Option::is_none) {
                        self.pm = None;
                    }
                }
            }
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
        self.pm.as_ref().is_none_or(|pm| {
            let client = pm.client.as_ref().map_or(pm.halted, PortMap::stopped);
            client && pm.retiring.iter().flatten().all(PortMap::stopped)
        })
    }

    /// Whether the host turned port mapping on: when it did not, there is nothing to poll for HTTP or datagrams.
    pub fn has_port_mapping(&self) -> bool {
        self.pm.is_some()
    }

    /// Whether the answer of [`Node::poll_timeout`] is cached, as a probe (with the `trace` feature, which the tests
    /// enable): a call that cannot move the deadline must not clear it.
    #[cfg(feature = "trace")]
    #[doc(hidden)]
    pub fn deadline_cached(&self) -> bool {
        matches!(self.deadline.get(), Due::Known(..))
    }

    /// Whether the layers' part of the deadline is cached, as a probe (with the `trace` feature): a call that moves
    /// only the endpoint must not clear it.
    #[cfg(feature = "trace")]
    #[doc(hidden)]
    pub fn layers_deadline_cached(&self) -> bool {
        matches!(self.deadline.get(), Due::Known(..) | Due::Endpoint(_))
    }

    /// What the port-mapping client dropped, and the draws of its nonce that failed; zero before it is turned on.
    pub fn port_mapping_stats(&self) -> PortMapStats {
        self.pm.as_ref().map_or_else(PortMapStats::default, |pm| PortMapStats {
            client: pm.client.as_ref().map(PortMap::stats).unwrap_or_default(),
            nonce_failures: pm.nonce_failures,
            release_overflows: pm.overflows,
        })
    }

    /// The port-mapping client's state, as a probe (with the `trace` feature, which the tests enable).
    #[cfg(feature = "trace")]
    #[doc(hidden)]
    pub fn pm_view(&self) -> PmView {
        let conn = self.conn.mapped_held()[0];
        self.pm.as_ref().map_or(
            PmView {
                conn,
                ..PmView::default()
            },
            |pm| PmView {
                on: true,
                client: pm.client.is_some(),
                held: pm.client.as_ref().and_then(PortMap::mapped),
                given: pm.given,
                conn,
                retiring: pm.retiring.iter().flatten().count(),
                overflows: pm.overflows,
                halted: pm.halted,
                timer: self.pm_deadline().is_some(),
                nonce_failures: pm.nonce_failures,
            },
        )
    }

    /// The mapping held: its external address and the protocol that granted it.
    pub fn port_mapping(&self) -> Option<(SocketAddr, Proto)> {
        let client = self.pm.as_ref()?.client.as_ref()?;
        Some((client.mapped()?, client.protocol()?))
    }

    /// The next HTTP request of the port-mapping client: where to open a TCP connection and the request's length in
    /// `buf` ([`pinc_portmap::upnp::MAX_REQUEST`] bytes hold any). The host writes it, reads the answer until the server closes it (at most
    /// [`pinc_portmap::MAX_RESPONSE`] bytes) and hands it to [`Node::handle_http`].
    pub fn poll_http(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        // With no client nothing can move the deadline, so the answer stays cached.
        if !self
            .pm
            .as_ref()
            .is_some_and(|pm| pm.client.is_some() || pm.retiring.iter().any(Option::is_some))
        {
            return None;
        }
        self.deadline.set(Due::Stale);
        self.pm.as_mut()?.sending().find_map(|c| c.poll_http(&mut *buf))
    }

    /// Whether the port-mapping client still waits for the answer to the HTTP request it gave out. When it does not
    /// (its deadline passed), the host drops the exchange it runs and polls [`Node::poll_http`] again.
    pub fn http_awaited(&self) -> bool {
        self.pm.as_ref().is_some_and(|pm| {
            pm.client
                .iter()
                .chain(pm.retiring.iter().flatten())
                .any(PortMap::awaiting_http)
        })
    }

    /// The answer to the last HTTP request, or `None` if its connection failed.
    pub fn handle_http(&mut self, now: Nanos, resp: Option<&[u8]>) {
        self.begin(now);
        if let Some(pm) = &mut self.pm {
            if let Some(c) = pm.sending().find(|c| c.awaiting_http()) {
                c.handle_http(now, resp);
            }
            pm.reap();
        }
        self.pm_apply(now);
        self.settle(now);
    }

    /// A datagram from `remote` for the port-mapping client: handled, and true; otherwise false.
    pub(crate) fn pm_datagram(&mut self, now: Nanos, remote: SocketAddr, d: &[u8]) -> bool {
        let Some(pm) = &mut self.pm else { return false };
        // The new client first: its answers are the ones a gateway sends now.
        let Some(client) = pm
            .client
            .iter_mut()
            .chain(pm.retiring.iter_mut().flatten())
            .find(|c| c.owns(remote, d))
        else {
            return false;
        };
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
        if let Some(pm) = &mut self.pm {
            for c in pm.sending().filter(|c| c.poll_timeout().is_some_and(|t| t <= now)) {
                c.handle_timeout(now);
            }
            pm.reap();
            self.pm_apply(now);
        }
    }

    pub(crate) fn pm_deadline(&self) -> Option<Nanos> {
        let pm = self.pm.as_ref()?;
        let seed = (pm.client.is_none() && !pm.halted).then_some(pm.retry);
        pm.client
            .iter()
            .chain(pm.retiring.iter().flatten())
            .filter_map(PortMap::poll_timeout)
            .chain(seed)
            .min()
    }

    pub(crate) fn pm_poll_udp(&mut self, buf: &mut [u8]) -> Option<(SocketAddr, usize)> {
        let pm = self.pm.as_mut()?;
        let out = pm.sending().find_map(|c| c.poll_datagram(&mut *buf));
        pm.reap();
        out
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
