//! The builder and the endpoint handle.
//!
//! [`Vinc::builder`] collects an identity, protocols, relays, discovery, limits and an access hook;
//! [`build`](Builder::build) takes the host's three async closures (receive a datagram, send a datagram, sleep until an
//! instant) and returns the [`Endpoint`]. The library starts no thread and no task: the futures of the handles drive
//! the endpoint when the host polls them, on the host's executor, so an endpoint with no future being polled makes no
//! progress. A host with nothing else to await on the endpoint (a server between accepts, connections that only need
//! their keepalives) awaits [`Endpoint::run`].
//!
//! The endpoint is `Clone` and `!Send`: one endpoint per core, and its handles stay on the thread that built it, where the host
//! spawns the futures with its executor's local spawn. It lives while any handle to it, to a
//! connection of it or to a stream of it lives; dropping the last handle drops its state without sending anything, so
//! close what should be told first ([`Endpoint::close`], [`Connection::close`]).

use std::future::Future;
use std::net::{Ipv4Addr, SocketAddr};
use std::rc::Rc;
use std::time::Instant;

use vinc_crypto::NodeId;
use vinc_keystore::{KeyHandle, KeyStore, SoftwareStore};

use crate::addr::NodeAddr;
use crate::conn::{Connection, Incoming};
use crate::drive::{Shared, T0};
pub use crate::engine::AllowAll;
pub use crate::engine::{Admit as Admission, Direction};
use crate::engine::{Core, CoreConfig, Try};
use crate::error::{Error, ErrorKind, Result};
use crate::host::{BatchHost, Host, Hosted, Io, IoHost};
use crate::keys::Identity;
use crate::mem::Limits;
use crate::protocol::{Protocol, Registered};
use crate::start::build;

/// Finds addresses for a node the caller gave none for. It may do I/O; it runs before the dial starts, so dropping the
/// dial while it runs leaves nothing behind.
pub trait Discovery {
    /// The addresses `node` may be reached at; empty if unknown.
    fn lookup(&self, node: &NodeId) -> impl Future<Output = Vec<SocketAddr>>;
}

/// No discovery: a dial without addresses uses the address book only.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoDiscovery;

impl Discovery for NoDiscovery {
    fn lookup(&self, _node: &NodeId) -> impl Future<Output = Vec<SocketAddr>> {
        std::future::ready(Vec::new())
    }
}

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
            local: SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0)),
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
    local: SocketAddr,
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
            local: self.local,
        }
    }

    /// Serve the protocol `alpn` (1 to 32 bytes). At most four protocols in all, including registered ones.
    #[must_use]
    pub fn alpn(mut self, alpn: impl Into<Vec<u8>>) -> Self {
        self.alpns.push(alpn.into());
        self
    }

    /// The address the host's socket is bound to. It is what [`Endpoint::addr`] tells peers, and an IPv6 address makes
    /// the endpoint hand the socket IPv4 peers as mapped addresses. Without it the endpoint uses the IPv4 wildcard
    /// address and port 0.
    #[must_use]
    pub const fn local_addr(mut self, addr: SocketAddr) -> Self {
        self.local = addr;
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
            local: self.local,
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
            local: self.local,
        }
    }

    /// The most same-size datagrams the endpoint batches into one transmit before the facade splits them: 1 turns it off.
    #[must_use]
    pub const fn batch(mut self, n: usize) -> Self {
        self.batch = n;
        self
    }
}

/// The endpoint that [`Builder::build`] makes over the closures `R`, `S` and `Z`.
pub type Built<R, S, Z, K, D, A> = Endpoint<Host<R, S, Z, K, A>, D>;

/// The endpoint that [`Builder::build_io`] makes over a host `N`.
pub type IoBuilt<N, K, D, A> = Endpoint<IoHost<N, K, A>, D>;

/// The endpoint that [`Builder::build_batched`] makes over the closures `R`, `S` and `Z`.
pub type BatchBuilt<R, S, Z, K, D, A> = Endpoint<BatchHost<R, S, Z, K, A>, D>;

impl<K: KeyStore, D: Discovery, A: Admission> Builder<K, D, A> {
    /// Make the endpoint over the host's I/O, one datagram per call: `recv` receives one datagram into the buffer and
    /// returns its length and sender, `send` sends one datagram to an address, `sleep` sleeps until an instant. The
    /// closures are called from whichever task polls a future of the endpoint. `recv` must lose no datagram when its
    /// future is dropped before it completes, as a readiness-based receive does. A host with segmentation offload or
    /// coalesced receives calls [`build_batched`](Self::build_batched) instead.
    ///
    /// The endpoint owns its tables and builds them on the heap, so the calling thread needs no large stack: the default
    /// limits build and run on a 1 MiB stack. The memory the `connections` limit reserves is described at [`Limits`].
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] for an invalid setting or no identity.
    pub fn build<R, S, Z>(self, recv: R, send: S, sleep: Z) -> Result<Built<R, S, Z, K, D, A>>
    where
        R: AsyncFn(&mut [u8]) -> std::io::Result<(usize, SocketAddr)>,
        S: AsyncFn(&[u8], SocketAddr) -> std::io::Result<usize>,
        Z: AsyncFn(Instant),
    {
        // One datagram per send: the endpoint does not batch for a host that sends one at a time.
        let (inner, core, local) = self.assemble(1)?;
        Ok(Endpoint(Rc::new(inner.finish(
            Host::new(recv, send, sleep),
            core,
            local,
        ))))
    }

    /// As [`build`](Self::build) for a host that can move several datagrams in one call. `send` gets a whole transmit: a
    /// buffer of equal-size datagrams (the last may be shorter), the address and the segment size, as `sendmsg` with
    /// `UDP_SEGMENT` takes it, and returns how many datagrams went; the endpoint batches up to [`batch`](Self::batch)
    /// datagrams per transmit. `recv` fills the buffer and returns the length filled, the sender and the segment size, as
    /// a receive with `UDP_GRO` gives them (the length again if it coalesced nothing).
    ///
    /// # Errors
    /// As [`build`](Self::build).
    pub fn build_batched<R, S, Z>(self, recv: R, send: S, sleep: Z) -> Result<BatchBuilt<R, S, Z, K, D, A>>
    where
        R: AsyncFn(&mut [u8]) -> std::io::Result<(usize, SocketAddr, usize)>,
        S: AsyncFn(&[u8], SocketAddr, usize) -> std::io::Result<usize>,
        Z: AsyncFn(Instant),
    {
        let batch = self.batch;
        let (inner, core, local) = self.assemble(batch)?;
        Ok(Endpoint(Rc::new(inner.finish(
            BatchHost::new(recv, send, sleep),
            core,
            local,
        ))))
    }

    /// As [`build_batched`](Self::build_batched) for a host that implements [`Io`], so that the endpoint's type can be
    /// written down.
    ///
    /// # Errors
    /// As [`build`](Self::build).
    pub fn build_io<N: Io>(self, io: N) -> Result<IoBuilt<N, K, D, A>> {
        let batch = self.batch;
        let (inner, core, local) = self.assemble(batch)?;
        Ok(Endpoint(Rc::new(inner.finish(IoHost::new(io), core, local))))
    }

    /// Everything but the host: the core, built with transmits of up to `gso` datagrams.
    fn assemble(self, gso: usize) -> Result<(Parts<D>, Core<K, A>, SocketAddr)> {
        let Builder {
            identity,
            alpns,
            relays,
            discovery,
            limits,
            admission,
            batch: _,
            local,
        } = self;
        let identity = identity.ok_or(Error::config("the system has no randomness for a node identity"))?;
        let public: Rc<[u8]> = identity.public_key().into();
        let node = identity.node_id();
        let cfg = CoreConfig {
            identity,
            alpns,
            limits,
            admit: admission,
            max_gso: gso,
            locals: interfaces(local),
        };
        let core = build(cfg, T0)?;
        Ok((
            Parts {
                node,
                public,
                discovery,
                relays,
            },
            core,
            local,
        ))
    }
}

/// What an endpoint holds besides its host and its core.
struct Parts<D> {
    node: NodeId,
    public: Rc<[u8]>,
    discovery: D,
    relays: Vec<String>,
}

impl<D> Parts<D> {
    fn finish<H: Hosted>(self, host: H, core: Core<H::Keys, H::Access>, local: SocketAddr) -> Inner<H, D> {
        Inner {
            shared: Rc::new(Shared::new(host, core, local)),
            node: self.node,
            public: self.public,
            discovery: self.discovery,
            relays: self.relays,
        }
    }
}

/// The local addresses the endpoint knows: one per family the socket can carry.
fn interfaces(local: SocketAddr) -> Vec<SocketAddr> {
    match local {
        SocketAddr::V6(a) if a.ip().is_unspecified() => {
            vec![local, SocketAddr::new(Ipv4Addr::UNSPECIFIED.into(), a.port())]
        }
        a => vec![a],
    }
}

struct Inner<H: Hosted, D> {
    shared: Rc<Shared<H>>,
    node: NodeId,
    public: Rc<[u8]>,
    discovery: D,
    relays: Vec<String>,
}

/// An endpoint: dial, accept, sign, and reach the layers above.
pub struct Endpoint<H: Hosted, D = NoDiscovery>(Rc<Inner<H, D>>);

impl<H: Hosted, D> Clone for Endpoint<H, D> {
    fn clone(&self) -> Self {
        Self(Rc::clone(&self.0))
    }
}

impl<H: Hosted, D> core::fmt::Debug for Endpoint<H, D> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Endpoint")
            .field("local", &self.0.shared.local())
            .finish_non_exhaustive()
    }
}

impl<H: Hosted, D: Discovery> Endpoint<H, D> {
    /// This node's id (for Ed25519, its public key).
    pub fn id(&self) -> NodeId {
        self.0.node
    }

    /// The public key bytes.
    pub fn public_key(&self) -> &[u8] {
        &self.0.public
    }

    /// Sign `data` with the node's identity key (Ed25519: 64 bytes).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store fails, [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        self.0.shared.run(|core, _| Try::Done(core.sign(data))).await
    }

    /// The address the host said its socket is bound to. For a wildcard bind the IP is the wildcard.
    pub fn local_addr(&self) -> SocketAddr {
        self.0.shared.local()
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

    /// Drive the endpoint until it stops, and do nothing else. For a host with nothing else pending on the endpoint: a
    /// server between accepts, or connections that only need their keepalives. The host awaits or spawns it on its own
    /// executor if it wants it; nothing starts it. An endpoint with no future being polled makes no progress.
    ///
    /// # Errors
    /// The reason the endpoint failed, if the host's socket did; `Ok` after [`close`](Self::close).
    pub async fn run(&self) -> Result<()> {
        self.0.shared.run(|core, _| core.idle_poll()).await;
        match self.0.shared.lock().and_then(|c| c.stopped()) {
            Some(e) if e.kind() != ErrorKind::Shutdown => Err(e),
            _ => Ok(()),
        }
    }

    /// Dial `to` for `alpn`. A peer already connected gets a sub-session at once, with no round trip. Without direct
    /// addresses in `to` the discovery hook and the address book are used. Dropping the future closes a session that
    /// was about to open.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Unreachable`] when no address works or the handshake fails, [`crate::ErrorKind::TimedOut`] when the peer does
    /// not answer, [`crate::ErrorKind::Refused`] when the access hook refused the peer, [`crate::ErrorKind::Busy`] when the connection
    /// table is full.
    pub async fn connect(&self, to: impl Into<NodeAddr>, alpn: &[u8]) -> Result<Connection<H>> {
        let to: NodeAddr = to.into();
        let mut addrs = to.direct;
        if addrs.is_empty() {
            addrs = self.0.discovery.lookup(&to.node).await;
        }
        Connection::dial(&self.0.shared, to.node, alpn, addrs).await
    }

    /// Wait for the next session a peer opened on a protocol of the builder's list. `None` once the endpoint stopped.
    pub async fn accept(&self) -> Option<Incoming<H>> {
        let info = self.0.shared.run(|core, _| core.accept_route(0)).await?;
        Some(Connection::incoming(&self.0.shared, info))
    }

    /// The peers with a session now.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn peers(&self) -> Result<Vec<NodeId>> {
        self.0
            .shared
            .run(|core, _| Try::Done(core.stopped().map_or_else(|| Ok(core.peers()), Err)))
            .await
    }

    /// Close every session with `peer`.
    pub async fn close_peer(&self, peer: &NodeId) {
        let sh = &self.0.shared;
        sh.run(|core, now| {
            core.close_peer(now, peer);
            Try::Done(())
        })
        .await;
    }

    /// Remember an address for `node`; dials to it use it when they carry none.
    pub fn add_address(&self, node: NodeId, addr: SocketAddr) {
        if let Some(mut core) = self.0.shared.lock() {
            core.add_address(node, addr);
        }
    }

    /// Tell the endpoint the network changed (a new address, a link back): it probes the paths again.
    pub async fn network_change(&self) {
        let sh = &self.0.shared;
        sh.run(|core, now| {
            core.network_change(now);
            Try::Done(())
        })
        .await;
    }

    /// The node sleeps: established sessions tell their peers.
    pub async fn suspend(&self) {
        let sh = &self.0.shared;
        sh.run(|core, now| {
            core.suspend(now);
            Try::Done(())
        })
        .await;
    }

    /// The node woke; `moved` says its address changed meanwhile, which makes its sessions close so they are dialed again.
    pub async fn resume(&self, moved: bool) {
        let sh = &self.0.shared;
        sh.run(|core, now| {
            core.resume(now, moved);
            Try::Done(())
        })
        .await;
    }

    /// Ask the access hook about `peer` the way the endpoint does for connections, for a layer that takes neighbours
    /// itself. With no hook everyone is admitted.
    pub fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        // The hook is asked without the core when a borrow is open: it is the same hook, and holds no endpoint state.
        self.0.shared.lock().is_none_or(|core| core.admits(peer, alpn, dir))
    }

    /// The node-wide counters of the endpoint.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn node_stats(&self) -> Result<crate::NodeStats> {
        self.0.shared.run(|core, _| Try::Done(Ok(core.node_stats()))).await
    }

    /// Serve `protocol` on its ALPN: every session a peer opens on it goes to the returned [`Registered`], not to
    /// [`accept`](Self::accept). The host runs `protocol.serve` for each, on its own executor. The ALPN counts against
    /// the endpoint's four.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the ALPN is empty, too long, already registered, or one too many.
    pub async fn register<P: Protocol>(&self, protocol: Rc<P>) -> Result<Registered<P, H>> {
        let alpn = protocol.alpn();
        let route = self.0.shared.run(|core, _| Try::Done(core.listen(alpn))).await?;
        Ok(Registered::new(&self.0.shared, route, protocol))
    }

    /// Close every session with a goodbye code and stop the endpoint; returns when the sessions are closed or a second has
    /// passed.
    pub async fn close(&self) {
        self.0
            .shared
            .run(|core, now| {
                core.begin_shutdown(now);
                core.shutdown_poll()
            })
            .await;
    }
}
