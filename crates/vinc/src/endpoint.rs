//! The builder and the endpoint handle.
//!
//! [`Vinc::builder`] collects an identity, protocols, relays, discovery, limits and an access hook;
//! [`bind`](Builder::bind) takes the host's datagram socket and timer and returns the [`Endpoint`] and the
//! [`Driver`](vinc_driver::Driver) future. The host spawns the driver on its own executor, on the core that owns the
//! socket; the library starts no thread and runs no loop of its own. The endpoint is `Clone + Send + Sync + 'static`;
//! every method is an async call into the driver through bounded queues.
//!
//! The endpoint runs while any handle to it, to a connection of it or to a stream of it lives, or until
//! [`close`](Endpoint::close).

use std::future::Future;
use std::net::{Ipv4Addr, SocketAddr};
use std::sync::Arc;

use vinc_crypto::NodeId;
pub use vinc_driver::AllowAll;
use vinc_driver::{
    Ctl, Datagrams, Driver, Identity, Limits, LoopStats, Receiver, Request, Result, SessionShared, Settings, Timer,
};
use vinc_keystore::{KeyHandle, KeyStore, SoftwareStore};

use crate::addr::NodeAddr;
use crate::conn::{Connection, Incoming};
use crate::protocol::{Protocol, Registered};

pub use vinc_driver::Direction;
// The access hook: whether a peer may connect, be dialed or be a gossip neighbour. It runs on the driver's task for
// connections and must not block.
pub use vinc_driver::Admit as Admission;

/// Finds addresses for a node the caller gave none for. It may do I/O; it runs before the dial starts, so dropping the
/// dial while it runs leaves nothing behind.
pub trait Discovery: Send + Sync + 'static {
    /// The addresses `node` may be reached at; empty if unknown.
    fn lookup(&self, node: &NodeId) -> impl Future<Output = Vec<SocketAddr>> + Send;
}

/// No discovery: a dial without addresses uses the address book only.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoDiscovery;

impl Discovery for NoDiscovery {
    fn lookup(&self, _node: &NodeId) -> impl Future<Output = Vec<SocketAddr>> + Send {
        std::future::ready(Vec::new())
    }
}

/// What [`Builder::bind`] makes: the endpoint and the future that drives it.
pub type Bound<D, A, U, T, S> = (Endpoint<D, A>, Driver<U, T, S, Arc<A>>);

/// The entry point: `Vinc::builder()`.
#[derive(Debug, Clone, Copy)]
pub struct Vinc;

impl Vinc {
    /// A builder with a fresh random identity.
    pub fn builder() -> Builder {
        Builder {
            identity: Identity::generate().ok(),
            alpns: Vec::new(),
            relays: Vec::new(),
            discovery: NoDiscovery,
            limits: Limits::default(),
            admission: AllowAll,
            batch: 8,
        }
    }
}

/// Collects the settings of an endpoint. The key store `S`, the discovery `D` and the access hook `A` are types the
/// setters change; the defaults are an in-memory store, no discovery and a hook that admits everyone.
pub struct Builder<S = SoftwareStore, D = NoDiscovery, A = AllowAll> {
    identity: Option<Identity<S>>,
    alpns: Vec<Vec<u8>>,
    relays: Vec<String>,
    discovery: D,
    limits: Limits,
    admission: A,
    batch: usize,
}

impl<S, D, A> core::fmt::Debug for Builder<S, D, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Builder").finish_non_exhaustive()
    }
}

impl<D, A> Builder<SoftwareStore, D, A> {
    /// Use the Ed25519 identity made from this 32-byte seed. The node id is its public key.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store cannot start.
    pub fn seed(mut self, seed: &[u8; 32]) -> Result<Self> {
        self.identity = Some(Identity::from_seed(seed)?);
        Ok(self)
    }
}

impl<S, D, A> Builder<S, D, A> {
    /// Use the identity key `handle` of `store`, such as a TPM store (`hwenc` feature of `vinc-keystore`).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the store holds no identity key under `handle`.
    pub fn key_store<K: KeyStore>(self, store: K, handle: KeyHandle) -> Result<Builder<K, D, A>> {
        Ok(self.identity(Identity::from_store(store, handle)?))
    }

    /// Use an identity built elsewhere.
    #[must_use]
    pub fn identity<K: KeyStore>(self, identity: Identity<K>) -> Builder<K, D, A> {
        Builder {
            identity: Some(identity),
            alpns: self.alpns,
            relays: self.relays,
            discovery: self.discovery,
            limits: self.limits,
            admission: self.admission,
            batch: self.batch,
        }
    }

    /// Serve the protocol `alpn` (1 to 32 bytes). At most four protocols in all, including registered ones.
    #[must_use]
    pub fn alpn(mut self, alpn: impl Into<Vec<u8>>) -> Self {
        self.alpns.push(alpn.into());
        self
    }

    /// Relay URLs. They go into [`Endpoint::addr`] so peers can be told about them; no relay client is wired into the
    /// endpoint yet, so a dial uses direct addresses only.
    #[must_use]
    pub fn relays(mut self, relays: impl IntoIterator<Item = impl Into<String>>) -> Self {
        self.relays = relays.into_iter().map(Into::into).collect();
        self
    }

    /// Find addresses for nodes dialed without any.
    #[must_use]
    pub fn discovery<N: Discovery>(self, discovery: N) -> Builder<S, N, A> {
        Builder {
            identity: self.identity,
            alpns: self.alpns,
            relays: self.relays,
            discovery,
            limits: self.limits,
            admission: self.admission,
            batch: self.batch,
        }
    }

    /// The sizes: connections, buffers and queues.
    #[must_use]
    pub const fn limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// Set the access hook: it is asked on accept, on dial, and by [`Endpoint::admit`] for gossip neighbours.
    #[must_use]
    pub fn acp<N: Admission>(self, hook: N) -> Builder<S, D, N> {
        Builder {
            identity: self.identity,
            alpns: self.alpns,
            relays: self.relays,
            discovery: self.discovery,
            limits: self.limits,
            admission: hook,
            batch: self.batch,
        }
    }

    /// The most same-size datagrams the endpoint batches into one send before the host splits them: 1 turns it off.
    #[must_use]
    pub const fn batch(mut self, n: usize) -> Self {
        self.batch = n;
        self
    }
}

impl<S: KeyStore, D: Discovery, A: Admission> Builder<S, D, A> {
    /// Make the endpoint and its driver over the host's datagram socket and timer. Nothing runs until the host spawns
    /// [`Driver::run`] on its executor; await the driver's future on the core that owns the socket.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] for an invalid setting or no identity, [`crate::ErrorKind::Unreachable`] if the
    /// socket has no address.
    pub fn bind<U: Datagrams, T: Timer>(self, udp: U, timer: T) -> Result<Bound<D, A, U, T, S>> {
        let identity = self.identity.ok_or(vinc_driver::Error::config(
            "the system has no randomness for a node identity",
        ))?;
        let public: Arc<[u8]> = identity.public_key().into();
        let admission = Arc::new(self.admission);
        let (h, driver) = vinc_driver::open(
            Settings {
                identity,
                alpns: self.alpns,
                limits: self.limits,
                admit: Arc::clone(&admission),
                batch: self.batch,
            },
            udp,
            timer,
        )?;
        let ep = Endpoint(Arc::new(Inner {
            remote: h.remote,
            incoming: h.incoming,
            local: h.local,
            node: h.node,
            public,
            stats: h.stats,
            discovery: self.discovery,
            admission,
            relays: self.relays,
        }));
        Ok((ep, driver))
    }

    /// [`bind`](Self::bind) over a UDP socket bound to `addr` on the current nuclei runtime.
    ///
    /// # Errors
    /// As [`bind`](Self::bind), and [`crate::ErrorKind::Unreachable`] if the address cannot be bound.
    #[cfg(feature = "nuclei")]
    pub async fn bind_nuclei(
        self,
        addr: SocketAddr,
    ) -> Result<(
        Endpoint<D, A>,
        Driver<vinc_nuclei::Socket, vinc_nuclei::Clock, S, Arc<A>>,
    )> {
        let socket = vinc_nuclei::Socket::bind(addr)
            .await
            .map_err(|_| vinc_driver::Error::new(vinc_driver::ErrorKind::Unreachable, "the address cannot be bound"))?;
        self.bind(socket, vinc_nuclei::Clock::new())
    }
}

struct Inner<D, A> {
    remote: vinc_driver::Remote,
    incoming: Receiver<Arc<SessionShared>>,
    local: SocketAddr,
    node: NodeId,
    public: Arc<[u8]>,
    stats: Arc<LoopStats>,
    discovery: D,
    admission: Arc<A>,
    relays: Vec<String>,
}

/// A running endpoint: dial, accept, sign, and reach the layers above.
pub struct Endpoint<D = NoDiscovery, A = AllowAll>(Arc<Inner<D, A>>);

impl<D, A> Clone for Endpoint<D, A> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<D, A> core::fmt::Debug for Endpoint<D, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Endpoint")
            .field("local", &self.0.local)
            .finish_non_exhaustive()
    }
}

impl<D: Discovery, A: Admission> Endpoint<D, A> {
    /// This node's id (for Ed25519, its public key).
    pub fn id(&self) -> NodeId {
        self.0.node
    }

    /// The public key bytes.
    pub fn public_key(&self) -> &[u8] {
        &self.0.public
    }

    /// Sign `data` with the node's identity key (Ed25519: 64 bytes). The driver signs it, so the driver must be running.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store fails, [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        let data = data.to_vec();
        self.remote().call(|reply| Request::Sign { data, reply }).await?
    }

    /// The address the socket is bound to. For a wildcard bind the IP is the wildcard.
    pub fn local_addr(&self) -> SocketAddr {
        self.0.local
    }

    /// This node's address as peers can use it: the id, the bound address with a wildcard IP replaced by loopback, and
    /// the relays the builder was given.
    pub fn addr(&self) -> NodeAddr {
        let mut a = self.local_addr();
        if a.ip().is_unspecified() {
            a.set_ip(if a.is_ipv4() {
                Ipv4Addr::LOCALHOST.into()
            } else {
                std::net::Ipv6Addr::LOCALHOST.into()
            });
        }
        NodeAddr {
            node: self.id(),
            direct: vec![a],
            relays: self.0.relays.clone(),
        }
    }

    pub(crate) fn remote(&self) -> &vinc_driver::Remote {
        &self.0.remote
    }

    /// Dial `to` for `alpn`. A peer already connected gets a sub-session at once, with no round trip. Without direct
    /// addresses in `to` the discovery hook and the address book are used. Dropping the future closes a session that
    /// was about to open.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Unreachable`] when no address works or the handshake fails, [`crate::ErrorKind::TimedOut`] when the peer does
    /// not answer, [`crate::ErrorKind::Refused`] when the access hook refused the peer, [`crate::ErrorKind::Busy`] when the connection
    /// table is full.
    pub async fn connect(&self, to: impl Into<NodeAddr>, alpn: &[u8]) -> Result<Connection> {
        let to: NodeAddr = to.into();
        let mut addrs = to.direct;
        if addrs.is_empty() {
            addrs = self.0.discovery.lookup(&to.node).await;
        }
        Connection::dial(self.remote(), to.node, alpn, addrs).await
    }

    /// Wait for the next session a peer opened on a protocol of the builder's list. `None` once the endpoint stopped.
    pub async fn accept(&self) -> Option<Incoming> {
        let shared = self.0.incoming.recv_async().await?;
        Some(Connection::incoming(shared, self.remote().clone()))
    }

    /// The peers with a session now.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn peers(&self) -> Result<Vec<NodeId>> {
        self.remote().call(|reply| Request::Peers { reply }).await
    }

    /// Close every session with `peer`.
    pub fn close_peer(&self, peer: &NodeId) {
        self.remote().ctl(Ctl::ClosePeer(*peer));
    }

    /// Remember an address for `node`; dials to it use it when they carry none.
    pub fn add_address(&self, node: NodeId, addr: SocketAddr) {
        self.remote().ctl(Ctl::AddAddr(node, addr));
    }

    /// Tell the endpoint the network changed (a new address, a link back): it probes the paths again.
    pub fn network_change(&self) {
        self.remote().ctl(Ctl::NetworkChange);
    }

    /// The node sleeps: established sessions tell their peers.
    pub fn suspend(&self) {
        self.remote().ctl(Ctl::Suspend);
    }

    /// The node woke; `moved` says its address changed meanwhile, which makes its sessions close so they are dialed again.
    pub fn resume(&self, moved: bool) {
        self.remote().ctl(Ctl::Resume(moved));
    }

    /// Ask the access hook about `peer` the way the endpoint does for connections, for a layer that takes neighbours
    /// itself. With no hook everyone is admitted.
    pub fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        self.0.admission.admit(peer, alpn, dir)
    }

    /// The node-wide counters of the endpoint.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn node_stats(&self) -> Result<vinc_driver::NodeStats> {
        self.remote().call(|reply| Request::Node { reply }).await
    }

    /// The counters of the driver: wakeups, datagrams and timers.
    pub fn loop_stats(&self) -> Arc<LoopStats> {
        Arc::clone(&self.0.stats)
    }

    /// Serve `protocol` on its ALPN: every session a peer opens on it goes to the returned [`Registered`], not to
    /// [`accept`](Self::accept). The host runs `protocol.serve` for each, on its own executor. The ALPN counts against
    /// the endpoint's four.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the ALPN is empty, too long, already registered, or one too many.
    pub async fn register<P: Protocol>(&self, protocol: Arc<P>) -> Result<Registered<P>> {
        let alpn = protocol.alpn().to_vec();
        let rx = self.remote().call(|reply| Request::Listen { alpn, reply }).await??;
        Ok(Registered::new(rx, self.remote().downgrade(), protocol))
    }

    /// Close every session with a goodbye code and stop the endpoint; returns when the sessions are closed or a second has
    /// passed.
    pub async fn close(&self) {
        let _ = self.remote().call(|reply| Request::Shutdown { reply }).await;
    }
}
