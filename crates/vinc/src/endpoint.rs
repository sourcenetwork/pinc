//! The builder and the endpoint handle.
//!
//! [`Vinc::builder`] collects an identity, protocols, relays, discovery, limits and an access hook;
//! [`bind_blocking`](Builder::bind_blocking) and [`spawn_on`](Builder::spawn_on) start the reference driver and return
//! an [`Endpoint`]. The endpoint is `Clone + Send + Sync + 'static`; every method is a call into the engine thread
//! through bounded queues, so none blocks the caller's thread except the explicitly blocking ones in
//! [`blocking`](crate::blocking).
//!
//! The endpoint runs while any handle to it, to a connection of it or to a stream of it lives, or until
//! [`close`](Endpoint::close).

use std::future::Future;
use std::net::{Ipv4Addr, SocketAddr};
use std::pin::Pin;
use std::sync::Arc;

use vinc_crypto::NodeId;
use vinc_driver::blocking::{self, LoopStats, Running, Settings};
use vinc_driver::{Admit, Ctl, Identity, Limits, Receiver, Request, Result, SessionShared, WeakRemote};
use vinc_keystore::{KeyHandle, KeyStore};

use crate::addr::NodeAddr;
use crate::conn::{Connection, Incoming};
use crate::protocol::Protocol;
use crate::rt::{Spawn, ThreadSpawner};

pub use vinc_driver::Direction;

/// Finds addresses for a node the caller gave none for. It may do I/O; it runs before the dial starts, so dropping the
/// dial while it runs leaves nothing behind.
pub trait Discovery: Send + Sync + 'static {
    /// The addresses `node` may be reached at; empty if unknown.
    fn lookup<'a>(&'a self, node: &'a NodeId) -> Pin<Box<dyn Future<Output = Vec<SocketAddr>> + Send + 'a>>;
}

/// The access hook: whether a peer may connect, be dialed or be a gossip neighbour. It runs on the engine thread for
/// connections and must not block.
pub trait Admission: Send + Sync + 'static {
    /// Whether `peer` may use `alpn` in `dir`.
    fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool;
}

struct Hook(Arc<dyn Admission>);

impl Admit for Hook {
    fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        self.0.admit(peer, alpn, dir)
    }
}

/// The entry point: `Vinc::builder()`.
#[derive(Debug, Clone, Copy)]
pub struct Vinc;

impl Vinc {
    /// A builder with a fresh random identity, binding all IPv4 interfaces on a port the system picks.
    pub fn builder() -> Builder {
        Builder {
            identity: None,
            alpns: Vec::new(),
            relays: Vec::new(),
            discovery: None,
            limits: Limits::default(),
            admission: None,
            bind: SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0)),
            batch: 8,
        }
    }
}

/// Collects the settings of an endpoint.
pub struct Builder {
    identity: Option<Identity>,
    alpns: Vec<Vec<u8>>,
    relays: Vec<String>,
    discovery: Option<Arc<dyn Discovery>>,
    limits: Limits,
    admission: Option<Arc<dyn Admission>>,
    bind: SocketAddr,
    batch: usize,
}

impl core::fmt::Debug for Builder {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Builder")
            .field("bind", &self.bind)
            .finish_non_exhaustive()
    }
}

impl Builder {
    /// Use the Ed25519 identity made from this 32-byte seed. The node id is its public key.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store cannot start.
    pub fn seed(mut self, seed: &[u8; 32]) -> Result<Self> {
        self.identity = Some(Identity::from_seed(seed)?);
        Ok(self)
    }

    /// Use the identity key `handle` of `store`, such as a TPM store (`hwenc` feature of `vinc-keystore`).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the store holds no identity key under `handle`.
    pub fn key_store(mut self, store: impl KeyStore + 'static, handle: KeyHandle) -> Result<Self> {
        self.identity = Some(Identity::from_store(store, handle)?);
        Ok(self)
    }

    /// Use an identity built elsewhere.
    #[must_use]
    pub fn identity(mut self, identity: Identity) -> Self {
        self.identity = Some(identity);
        self
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
    pub fn discovery(mut self, discovery: impl Discovery) -> Self {
        self.discovery = Some(Arc::new(discovery));
        self
    }

    /// The sizes: connections, buffers and queues.
    #[must_use]
    pub const fn limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// Set the access hook: it is asked on accept, on dial, and by [`Endpoint::admit`] for gossip neighbours.
    #[must_use]
    pub fn acp(mut self, hook: impl Admission) -> Self {
        self.admission = Some(Arc::new(hook));
        self
    }

    /// The address to bind: an IP and a port, 0 for any.
    #[must_use]
    pub const fn bind_addr(mut self, addr: SocketAddr) -> Self {
        self.bind = addr;
        self
    }

    /// The most same-size datagrams the endpoint batches into one send before the driver splits them: 1 turns it off.
    #[must_use]
    pub const fn batch(mut self, n: usize) -> Self {
        self.batch = n;
        self
    }

    /// Start the reference driver on its own thread; background tasks of registered protocols run on one thread each.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] for an invalid setting, [`crate::ErrorKind::Unreachable`] if the address cannot be bound.
    pub fn bind_blocking(self) -> Result<Endpoint> {
        self.launch(Arc::new(ThreadSpawner))
    }

    /// Start the reference driver and run background tasks of registered protocols on the host's `spawner`.
    ///
    /// The futures of the endpoint need no executor, so the spawner is only for the tasks the endpoint starts for you.
    /// The socket loop itself runs on its own thread, because std has no readiness API an executor could drive.
    ///
    /// # Errors
    /// As [`bind_blocking`](Self::bind_blocking).
    pub fn spawn_on(self, spawner: impl Spawn) -> Result<Endpoint> {
        self.launch(Arc::new(spawner))
    }

    fn launch(self, spawner: Arc<dyn Spawn>) -> Result<Endpoint> {
        let identity = match self.identity {
            Some(i) => i,
            None => Identity::generate()?,
        };
        let admit: Option<Arc<dyn Admit>> = self.admission.clone().map(|h| Arc::new(Hook(h)) as Arc<dyn Admit>);
        let running = blocking::start(Settings {
            bind: self.bind,
            identity: identity.clone(),
            alpns: self.alpns,
            limits: self.limits,
            admit,
            batch: self.batch,
        })?;
        Ok(Endpoint(Arc::new(Inner {
            running,
            identity,
            discovery: self.discovery,
            admission: self.admission,
            spawner,
            relays: self.relays,
        })))
    }
}

struct Inner {
    running: Running,
    identity: Identity,
    discovery: Option<Arc<dyn Discovery>>,
    admission: Option<Arc<dyn Admission>>,
    spawner: Arc<dyn Spawn>,
    relays: Vec<String>,
}

/// A running endpoint: dial, accept, sign, and reach the layers above.
#[derive(Clone)]
pub struct Endpoint(Arc<Inner>);

impl core::fmt::Debug for Endpoint {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Endpoint")
            .field("local", &self.0.running.local_addr())
            .finish_non_exhaustive()
    }
}

impl Endpoint {
    /// This node's id (for Ed25519, its public key).
    pub fn id(&self) -> NodeId {
        self.0.identity.node_id()
    }

    /// The public key bytes.
    pub fn public_key(&self) -> &[u8] {
        self.0.identity.public_key()
    }

    /// Sign `data` with the node's identity key (Ed25519: 64 bytes).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store fails.
    pub fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        self.0.identity.sign(data)
    }

    /// The address the socket is bound to. For a wildcard bind the IP is the wildcard.
    pub fn local_addr(&self) -> SocketAddr {
        self.0.running.local_addr()
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
        self.0.running.remote()
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
        if addrs.is_empty()
            && let Some(d) = &self.0.discovery
        {
            addrs = d.lookup(&to.node).await;
        }
        Connection::dial(self.remote(), to.node, alpn, addrs).await
    }

    /// Wait for the next session a peer opened on a protocol of the builder's list. `None` once the endpoint stopped.
    pub async fn accept(&self) -> Option<Incoming> {
        let shared = self.0.running.incoming().recv_async().await?;
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
        self.0.admission.as_ref().is_none_or(|a| a.admit(peer, alpn, dir))
    }

    /// The node-wide counters of the endpoint.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn node_stats(&self) -> Result<vinc_driver::NodeStats> {
        self.remote().call(|reply| Request::Node { reply }).await
    }

    /// The counters of the socket loop: wakeups, datagrams and timers.
    pub fn loop_stats(&self) -> Arc<LoopStats> {
        self.0.running.stats()
    }

    /// Serve `protocol` on its ALPN: every session a peer opens on it goes to `protocol.serve` as a task on the spawner,
    /// not to [`accept`](Self::accept). The ALPN counts against the endpoint's four.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the ALPN is empty, too long, already registered, or one too many.
    pub async fn register<P: Protocol>(&self, protocol: Arc<P>) -> Result<()> {
        let alpn = protocol.alpn().to_vec();
        let rx = self.remote().call(|reply| Request::Listen { alpn, reply }).await??;
        let weak = self.remote().downgrade();
        self.0
            .spawner
            .spawn(Box::pin(route(rx, weak, protocol, Arc::clone(&self.0.spawner))));
        Ok(())
    }

    /// Close every session with a goodbye code and stop the endpoint; returns when the sessions are closed or a second has
    /// passed.
    pub async fn close(&self) {
        let _ = self.remote().call(|reply| Request::Shutdown { reply }).await;
    }

    /// The blocking mirror of this endpoint.
    pub fn blocking(&self) -> crate::blocking::Endpoint {
        crate::blocking::Endpoint::from(self.clone())
    }
}

/// Take sessions off a protocol's queue and serve each on the spawner. Holds the endpoint only weakly, so a registered
/// protocol does not keep the endpoint running.
async fn route<P: Protocol>(
    rx: Receiver<Arc<SessionShared>>,
    remote: WeakRemote,
    protocol: Arc<P>,
    spawner: Arc<dyn Spawn>,
) {
    while let Some(shared) = rx.recv_async().await {
        let Some(remote) = remote.upgrade() else { break };
        spawner.spawn(Arc::clone(&protocol).serve(Connection::new(shared, remote)));
    }
}
