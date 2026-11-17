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

use alloc::rc::Rc;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::future::{Future, poll_fn};
use core::net::{Ipv4Addr, SocketAddr};
use core::pin::pin;
use core::task::Poll;
use core::time::Duration;
use std::time::Instant;

use vinc_crypto::NodeId;
use vinc_keystore::{KeyHandle, KeyStore, SoftwareStore};

use crate::addr::NodeAddr;
use crate::carrier::CarrierKind;
use crate::carriers::{CarrierFns, Carriers, NoCarriers, Relay};
use crate::conn::{Connection, Incoming};
use crate::drive::{RoleEnd, Shared, T0};
pub use crate::engine::AllowAll;
pub use crate::engine::{Admit as Admission, Direction};
use crate::engine::{Core, CoreConfig, Try};
use crate::error::{Error, ErrorKind, Result};
use crate::host::{BatchHost, Host, Hosted, Io, IoHost};
use crate::keys::Identity;
use crate::maps::Keys;
use crate::mem::Limits;
use crate::node::RELAYS;
use crate::protocol::{Protocol, Registered};
use crate::role::{Role, RoleSpec};
use crate::start::{PortMapping, build, interfaces};

mod discovery;
#[cfg(test)]
mod map_keys_tests;
mod portmap;
mod records;
mod role;

pub use discovery::{Discovery, NoDiscovery};

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
            mtu: 1500,
            local: SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0)),
            carriers: NoCarriers,
            hub: false,
            connected_topics: false,
            envelopes: false,
            connect_timeout: DEFAULT_CONNECT_TIMEOUT,
            port_mapping: PortMapping::OFF,
            role: (),
        }
    }
}

/// How long a dial may take unless [`Builder::connect_timeout`] says otherwise.
const DEFAULT_CONNECT_TIMEOUT: Duration = Duration::from_secs(20);

/// Collects the settings of an endpoint. The key store `S`, the discovery `D` and the access hook `A` are types the
/// setters change; the defaults are an in-memory store, no discovery and a hook that admits everyone.
pub struct Builder<S = SoftwareStore, D = NoDiscovery, A = AllowAll, C = NoCarriers, Q = ()> {
    identity: Option<Identity<S>>,
    alpns: Vec<Vec<u8>>,
    relays: Vec<Relay>,
    discovery: D,
    limits: Limits,
    admission: A,
    batch: usize,
    mtu: u16,
    local: SocketAddr,
    carriers: C,
    hub: bool,
    connected_topics: bool,
    envelopes: bool,
    connect_timeout: Duration,
    port_mapping: PortMapping,
    role: Q,
}

impl<S, D, A, C, Q> core::fmt::Debug for Builder<S, D, A, C, Q> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Builder").finish_non_exhaustive()
    }
}

impl<D, A, C, Q> Builder<SoftwareStore, D, A, C, Q> {
    /// Use the Ed25519 identity made from this 32-byte seed. The node id is its public key.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the key store cannot start.
    pub fn seed(mut self, seed: &[u8; 32]) -> Result<Self> {
        self.identity = Some(Identity::from_seed(seed)?);
        Ok(self)
    }
}

impl<S, D, A, C, Q> Builder<S, D, A, C, Q> {
    /// Use the identity key `handle` of `store`, such as a TPM store (`hwenc` feature of `vinc-keystore`).
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if the store holds no identity key under `handle`.
    pub fn key_store<K: KeyStore>(self, store: K, handle: KeyHandle) -> Result<Builder<K, D, A, C, Q>> {
        Ok(self.identity(Identity::from_store(store, handle)?))
    }

    /// Use an identity built elsewhere.
    #[must_use]
    pub fn identity<K: KeyStore>(self, identity: Identity<K>) -> Builder<K, D, A, C, Q> {
        Builder {
            identity: Some(identity),
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
            envelopes: self.envelopes,
            connect_timeout: self.connect_timeout,
            port_mapping: self.port_mapping,
            role: self.role,
        }
    }

    /// Serve the protocol `alpn` (1 to 32 bytes). At most [`MAX_PROTOCOLS`](crate::MAX_PROTOCOLS) protocols in all,
    /// including registered ones.
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

    /// The relays this endpoint uses: it keeps a carrier to each, asks them for the address of a peer dialed by id, and
    /// reaches a peer through the first one until a direct path works. They are also the hubs of membership and topic
    /// broadcast. At most four; with none the endpoint reaches peers directly only. Their carriers need the host's
    /// closures: see [`carriers`](Self::carriers).
    #[must_use]
    pub fn relays(mut self, relays: impl IntoIterator<Item = Relay>) -> Self {
        self.relays = relays.into_iter().collect();
        self
    }

    /// The host's carriers to the relays: `open` a byte stream of a [`CarrierKind`] to a relay (the TCP connect, or the
    /// HTTP upgrade of a WebSocket, is the host's work), `read` into a vector, `write` a vector from an offset, and
    /// `close`. The buffers are owned and come back with the result; see [`Carriers`](crate::Carriers) for what a
    /// dropped operation may leave. Without them a relay is reached by UDP only. A TCP carrier should send every write
    /// at once (`set_nodelay(true)`): a relay frame written behind another otherwise waits for the acknowledgement of
    /// the first, a round trip on every hop.
    #[must_use]
    #[allow(
        clippy::type_complexity,
        reason = "the builder's type names the host's closures and its other choices"
    )]
    pub fn carriers<O, R, W, Cl, St>(
        self,
        open: O,
        read: R,
        write: W,
        close: Cl,
    ) -> Builder<S, D, A, CarrierFns<O, R, W, Cl, St>, Q>
    where
        O: AsyncFn(&Relay, CarrierKind) -> std::io::Result<St>,
        R: AsyncFn(&St, Vec<u8>) -> (std::io::Result<usize>, Vec<u8>),
        W: AsyncFn(&St, Vec<u8>, usize) -> (std::io::Result<usize>, Vec<u8>),
        Cl: AsyncFn(St),
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
            carriers: CarrierFns::new(open, read, write, close),
            hub: self.hub,
            connected_topics: self.connected_topics,
            envelopes: self.envelopes,
            connect_timeout: self.connect_timeout,
            port_mapping: self.port_mapping,
            role: self.role,
        }
    }

    /// Find addresses for nodes dialed without any.
    #[must_use]
    pub fn discovery<N: Discovery>(self, discovery: N) -> Builder<S, N, A, C, Q> {
        Builder {
            identity: self.identity,
            alpns: self.alpns,
            relays: self.relays,
            discovery,
            limits: self.limits,
            admission: self.admission,
            batch: self.batch,
            mtu: self.mtu,
            local: self.local,
            carriers: self.carriers,
            hub: self.hub,
            connected_topics: self.connected_topics,
            envelopes: self.envelopes,
            connect_timeout: self.connect_timeout,
            port_mapping: self.port_mapping,
            role: self.role,
        }
    }

    /// How long a [`connect`](Endpoint::connect) may take from the call to an open session, the lookup of the peer
    /// included (default 20 s). A dial that is not up by then fails with [`crate::ErrorKind::TimedOut`].
    #[must_use]
    pub const fn connect_timeout(mut self, wait: Duration) -> Self {
        self.connect_timeout = wait;
        self
    }

    /// Run this endpoint as a hub: the relays of the other endpoints are hubs, and a hub keeps the roster of its members
    /// and a log of each topic's recent messages for them. List the other hubs, if any, with [`relays`](Self::relays).
    #[must_use]
    pub const fn hub(mut self) -> Self {
        self.hub = true;
        self
    }

    /// Give topics a gossip mesh's reach through the hubs: a hub hands this endpoint a topic message only from a
    /// publisher it is linked to by a chain of the application's sessions (this endpoint's peers, their peers and so
    /// on), even when a group with no path to it shares the hub. The endpoint tells its hubs the peers it holds
    /// sessions with when that set changed, once the session events of a turn are handled and at most every 250 ms, so a
    /// burst of sessions is one signed record; a hub links two endpoints only when both name each other. Endpoints
    /// with and without this setting do not hear each other's topic messages through a hub. Off by default: a hub then
    /// reaches every member of a topic.
    ///
    /// The scope is the hubs' to keep. While no hub is reachable, a publisher sends straight to the topic's
    /// subscribers over member sessions, and members keep no records: in that fallback a message reaches every
    /// subscriber the publisher knows, in its component or not. A hub's own application and a hub's own publishes are
    /// never scoped, and on a hub this setting does nothing.
    #[must_use]
    pub const fn connected_topics(mut self) -> Self {
        self.connected_topics = true;
        self
    }

    /// Whether every topic message arrives with its signed [`Envelope`](crate::envelope::Envelope), which the
    /// application can store and later hand to anyone to verify offline (default off). Each delivered message then costs
    /// its signed head (about 122 bytes for an Ed25519 origin, several kilobytes for a hybrid one) and a second copy of
    /// the topic and the payload, in one more allocation.
    #[must_use]
    pub const fn envelopes(mut self, on: bool) -> Self {
        self.envelopes = on;
        self
    }

    /// The sizes: connections, buffers and queues.
    #[must_use]
    pub const fn limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// Set the access hook: it is asked for the protocol and direction of each session on accept and on dial, and by [`Endpoint::admit`] for gossip neighbours; see [`Admission`].
    #[must_use]
    pub fn acp<N: Admission>(self, hook: N) -> Builder<S, D, N, C, Q> {
        Builder {
            identity: self.identity,
            alpns: self.alpns,
            relays: self.relays,
            discovery: self.discovery,
            limits: self.limits,
            admission: hook,
            batch: self.batch,
            mtu: self.mtu,
            local: self.local,
            carriers: self.carriers,
            hub: self.hub,
            connected_topics: self.connected_topics,
            envelopes: self.envelopes,
            connect_timeout: self.connect_timeout,
            port_mapping: self.port_mapping,
            role: self.role,
        }
    }

    /// The MTU of the host's interface, IP and UDP headers included (1500 when not set); the endpoint takes the headers
    /// off (28 bytes on IPv4, 48 on IPv6) to size its datagrams. On a path with a round trip under 2 ms it probes
    /// datagrams of up to 8952 bytes when this allows it, so say 9000 on a jumbo-frame network and 65535 on loopback,
    /// and give the receive closure a buffer that large.
    #[must_use]
    pub const fn mtu(mut self, mtu: u16) -> Self {
        self.mtu = mtu;
        self
    }

    /// The most same-size datagrams the endpoint batches into one transmit before the facade splits them: 1 turns it off.
    #[must_use]
    pub const fn batch(mut self, n: usize) -> Self {
        self.batch = n;
        self
    }
}

/// The endpoint that [`Builder::build`] makes over the closures `R`, `S` and `Z`.
pub type Built<R, S, Z, K, D, A, C = NoCarriers, P = ()> = Endpoint<Host<R, S, Z, K, A, C, P>, D>;

/// The endpoint that [`Builder::build_io`] makes over a host `N`.
pub type IoBuilt<N, K, D, A, C = NoCarriers, P = ()> = Endpoint<IoHost<N, K, A, C, P>, D>;

/// The endpoint that [`Builder::build_batched`] makes over the closures `R`, `S` and `Z`.
pub type BatchBuilt<R, S, Z, K, D, A, C = NoCarriers, P = ()> = Endpoint<BatchHost<R, S, Z, K, A, C, P>, D>;

#[allow(
    clippy::type_complexity,
    reason = "the endpoint's type names the host's closures and the builder's choices"
)]
impl<K: KeyStore, D: Discovery, A: Admission, C: Carriers, Q: RoleSpec<K>> Builder<K, D, A, C, Q> {
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
    pub fn build<R, S, Z>(self, recv: R, send: S, sleep: Z) -> Result<Built<R, S, Z, K, D, A, C, Q::Built>>
    where
        R: AsyncFn(&mut [u8]) -> std::io::Result<(usize, SocketAddr)>,
        S: AsyncFn(&[u8], SocketAddr) -> std::io::Result<usize>,
        Z: AsyncFn(Instant),
    {
        // One datagram per send: the endpoint does not batch for a host that sends one at a time.
        let (inner, carriers, role, core, local) = self.assemble(1)?;
        Ok(Endpoint(Rc::new(inner.finish(
            Host::new(recv, send, sleep, carriers, role),
            core,
            local,
            1,
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
    pub fn build_batched<R, S, Z>(self, recv: R, send: S, sleep: Z) -> Result<BatchBuilt<R, S, Z, K, D, A, C, Q::Built>>
    where
        R: AsyncFn(&mut [u8]) -> std::io::Result<(usize, SocketAddr, usize)>,
        S: AsyncFn(&[u8], SocketAddr, usize) -> std::io::Result<usize>,
        Z: AsyncFn(Instant),
    {
        let batch = self.batch;
        let (inner, carriers, role, core, local) = self.assemble(batch)?;
        Ok(Endpoint(Rc::new(inner.finish(
            BatchHost::new(recv, send, sleep, carriers, role),
            core,
            local,
            batch,
        ))))
    }

    /// As [`build_batched`](Self::build_batched) for a host that implements [`Io`], so that the endpoint's type can be
    /// written down.
    ///
    /// # Errors
    /// As [`build`](Self::build).
    pub fn build_io<N: Io>(self, io: N) -> Result<IoBuilt<N, K, D, A, C, Q::Built>> {
        let batch = self.batch;
        let (inner, carriers, role, core, local) = self.assemble(batch)?;
        Ok(Endpoint(Rc::new(inner.finish(
            IoHost::new(io, carriers, role),
            core,
            local,
            batch,
        ))))
    }

    /// Everything but the host: the core, built with transmits of up to `gso` datagrams.
    fn assemble(self, gso: usize) -> Result<Assembled<D, C, Q::Built, K, A>> {
        let Builder {
            identity,
            alpns,
            relays,
            discovery,
            limits,
            admission,
            batch: _,
            mtu,
            local,
            carriers,
            hub,
            connected_topics,
            envelopes,
            connect_timeout,
            port_mapping,
            role,
        } = self;
        if relays.len() > RELAYS {
            return Err(Error::config("at most four relays"));
        }
        let mut identity = identity.ok_or(Error::config("the system has no randomness for a node identity"))?;
        let map_keys = Keys::draw(|out| identity.random(out))?;
        let (seed, secrets) = map_keys.parts();
        discovery.seed_maps(seed, secrets);
        let public: Rc<[u8]> = identity.public_key().into();
        let node = identity.node_id();
        let cfg = CoreConfig {
            identity,
            map_keys,
            alpns,
            limits,
            admit: admission,
            max_gso: gso,
            mtu,
            locals: interfaces(local),
            relays: relays.clone(),
            hub,
            connected_topics,
            envelopes,
            relaying: <Q::Built as Role>::ON,
            connect_timeout: u64::try_from(connect_timeout.as_nanos()).unwrap_or(u64::MAX),
            port_mapping,
        };
        let core = build(cfg, T0)?;
        // The relay's clock is the wall clock; the endpoint's is the same time from another origin, a fixed offset away.
        let offset = if <Q::Built as Role>::ON {
            crate::clock::wall_ns().saturating_sub(T0)
        } else {
            0
        };
        let role = role.build(core.identity(), local, T0.saturating_add(offset))?;
        Ok((
            Parts {
                node,
                public,
                discovery,
                home: relays.first().map_or(node, |r| r.id),
                relays,
                max_message: limits.topic_message,
                offset,
            },
            carriers,
            role,
            core,
            local,
        ))
    }
}

/// What `assemble` makes: the endpoint's parts, the host's carriers, the core and the bound address.
type Assembled<D, C, P, K, A> = (Parts<D>, C, P, Core<K, A>, SocketAddr);

/// What an endpoint holds besides its host and its core.
struct Parts<D> {
    node: NodeId,
    public: Rc<[u8]>,
    discovery: D,
    relays: Vec<Relay>,
    max_message: usize,
    home: NodeId,
    /// The relay clock minus the endpoint's, in nanoseconds.
    offset: u64,
}

impl<D> Parts<D> {
    fn finish<H: Hosted>(self, host: H, core: Core<H::Keys, H::Access>, local: SocketAddr, gso: usize) -> Inner<H, D> {
        Inner {
            shared: Rc::new(Shared::new(host, core, local, gso, self.relays.clone(), self.offset)),
            node: self.node,
            public: self.public,
            discovery: self.discovery,
            relays: self.relays.iter().map(Relay::url).collect(),
            max_message: self.max_message,
            home: self.home,
        }
    }
}

pub(crate) struct Inner<H: Hosted, D> {
    pub(crate) shared: Rc<Shared<H>>,
    pub(crate) node: NodeId,
    public: Rc<[u8]>,
    pub(crate) discovery: D,
    relays: Vec<String>,
    pub(crate) max_message: usize,
    /// The node whose relay the record names as home: the first relay, else this node.
    home: NodeId,
}

/// An endpoint: dial, accept, sign, and reach the layers above.
pub struct Endpoint<H: Hosted, D = NoDiscovery>(pub(crate) Rc<Inner<H, D>>);

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
    /// The same key signs the protocol's own statements, so `data` that begins with the start of one is refused: the
    /// label prefix `"VINC 2026 "`, `"VNCREC"` (a node record), `"VNCBCN"` (a beacon) or `"vinc-sleep"` (a sleep
    /// notice). Statements signed over a 32-byte hash, and a topic message's (`topic | id | hash | timestamp | flag`),
    /// cannot be told by a prefix: never sign bytes a peer chose without wrapping them in a format of your own.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Config`] if `data` begins with a reserved prefix or the key store fails,
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn sign(&self, data: &[u8]) -> Result<Vec<u8>> {
        crate::reserved::check(data)?;
        self.sign_unchecked(data).await
    }

    /// Sign bytes the library built itself, which may begin with a reserved prefix.
    async fn sign_unchecked(&self, data: &[u8]) -> Result<Vec<u8>> {
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
                core::net::Ipv6Addr::LOCALHOST.into()
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
        let _role = RoleEnd(&self.0.shared);
        self.0.shared.run_as(true, |core, _| core.idle_poll()).await;
        match self.0.shared.lock().and_then(|c| c.stopped()) {
            Some(e) if e.kind() != ErrorKind::Shutdown => Err(e),
            _ => Ok(()),
        }
    }

    /// Dial `to` for `alpn`. A peer already connected gets a sub-session at once, with no round trip. Without direct
    /// addresses in `to` the discovery hook and the address book are used; the hook has [`LOOKUP_WAIT`] to answer.
    /// A sub-session, and a dial towards a peer whose access was allowed in the last 25 s, return before the peer
    /// answers; [`Connection::answered`] waits for it.
    /// Dropping the future closes a session that was about to open.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Unreachable`] when no address works or the handshake fails, [`crate::ErrorKind::TimedOut`] when the peer does
    /// not answer or discovery did not answer in time, [`crate::ErrorKind::Refused`] when the access hook refused the peer or it is revoked (then nothing is sent),
    /// [`crate::ErrorKind::Busy`] when the connection table is full.
    pub async fn connect(&self, to: impl Into<NodeAddr>, alpn: &[u8]) -> Result<Connection<H>> {
        let to: NodeAddr = to.into();
        // A dial that went out would reach the peer as a session it holds until our deny arrives, long enough for its
        // own dial to ride it as a sub-session and fail after an unrevoke.
        if self.0.shared.admit.is_revoked(&to.node) {
            return Err(Error::new(ErrorKind::Refused, "the peer is revoked"));
        }
        let mut addrs = to.direct;
        if addrs.is_empty() {
            addrs = self
                .within(LOOKUP_WAIT, self.0.discovery.lookup(&to.node))
                .await
                .ok_or(Error::new(ErrorKind::TimedOut, "discovery did not answer in time"))?;
        }
        Connection::dial(&self.0.shared, to.node, alpn, addrs).await
    }

    /// `f`'s output, or `None` if `wait` passes first; the wait is the host's sleep.
    async fn within<T>(&self, wait: Duration, f: impl Future<Output = T>) -> Option<T> {
        let mut f = pin!(f);
        let mut sleep = pin!(self.0.shared.host.sleep(Instant::now() + wait));
        poll_fn(|cx| {
            if let Poll::Ready(v) = f.as_mut().poll(cx) {
                return Poll::Ready(Some(v));
            }
            if sleep.as_mut().poll(cx).is_ready() {
                return Poll::Ready(None);
            }
            Poll::Pending
        })
        .await
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

    /// Revoke `peer`: every session with it ends within this call with the code [`DENIED`](crate::DENIED), a transfer
    /// in flight included, and until [`unrevoke`](Self::unrevoke) no session with it comes up, whatever the access
    /// hook would say and whichever side dials.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Busy`] if [`REVOKED_MAX`](crate::REVOKED_MAX) peers are revoked already; nothing changed.
    pub async fn revoke(&self, peer: &NodeId) -> Result<()> {
        let sh = &self.0.shared;
        sh.run(|core, now| Try::Done(core.revoke(now, peer))).await
    }

    /// Lift the revocation of `peer`; whether it was revoked. The access hook decides about it again, from its next
    /// session on: an answer cached while it was revoked is dropped.
    pub fn unrevoke(&self, peer: &NodeId) -> bool {
        let lifted = self.0.shared.admit.lift(peer);
        // vertexia: a lift made from inside the access hook finds the core busy and leaves the node's table
        // holding the peer until the next restart; lift from outside the hook.
        if let Some(mut core) = self.0.shared.lock() {
            core.unrevoke(&peer.bytes);
        }
        lifted
    }

    /// The access hook's answer for `peer` changed (an allowlist edit): drop the answer the endpoint cached for it, so
    /// its next session asks the hook again instead of waiting out the 30 s. A session already up asks again at its
    /// next event, and closes if the hook now refuses.
    pub fn admission_changed(&self, peer: &NodeId) {
        // vertexia: called from inside the access hook the core is busy and the cached answer lasts its 30 s; call
        // it from outside the hook.
        if let Some(mut core) = self.0.shared.lock() {
            core.forget_access(&peer.bytes);
        }
    }

    /// Whether `peer` is revoked.
    pub fn is_revoked(&self, peer: &NodeId) -> bool {
        self.0.shared.admit.is_revoked(peer)
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
        let wall = crate::clock::wall_ms();
        sh.run(|core, now| {
            core.suspend(now, wall);
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
    /// itself. With no hook everyone is admitted. The hook is always asked, whatever the endpoint is doing.
    pub fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        self.0.shared.admit.admit(peer, alpn, dir)
    }

    /// The node-wide counters of the endpoint.
    ///
    /// # Errors
    /// [`crate::ErrorKind::Shutdown`] if the endpoint stopped.
    pub async fn node_stats(&self) -> Result<crate::NodeStats> {
        self.0.shared.run(|core, _| Try::Done(Ok(core.node_stats()))).await
    }

    /// How many timer calls did not move a deadline of the endpoint or of a layer above it that the call before had
    /// left due, by the layer that holds the deadline. All zero unless a layer has a defect: each such call is
    /// counted, and the endpoint asks for its next timer call a millisecond later and goes on working.
    pub fn timer_stats(&self) -> crate::TimerStats {
        self.0
            .shared
            .lock()
            .map_or_else(crate::TimerStats::default, |core| core.node.timer_stats())
    }

    /// Give the endpoint a deadline that is due now and that no call moves, as a probe (with the `trace` feature,
    /// which the tests enable): a layer that breaks the timer contract.
    #[cfg(feature = "trace")]
    #[doc(hidden)]
    pub fn stick_timer(&self) {
        let now = self.0.shared.now();
        if let Some(mut core) = self.0.shared.lock() {
            core.node.stick_timer(Some(now));
            core.wake_driver();
        }
    }

    /// The relay this endpoint is homed on now: the one its record names and a relayed path's first stop. A relay pinned
    /// with [`Relay::home`](crate::Relay::home) is it once that relay answers. `None` before any relay answered.
    pub fn home_relay(&self) -> Option<NodeId> {
        self.0.shared.lock().and_then(|core| core.home_relay())
    }

    /// Serve `protocol` on its ALPN: every session a peer opens on it goes to the returned [`Registered`], not to
    /// [`accept`](Self::accept). The host runs `protocol.serve` for each, on its own executor. The ALPN counts against
    /// the endpoint's [`MAX_PROTOCOLS`](crate::MAX_PROTOCOLS).
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

/// How long a dial by node id alone, and [`Endpoint::lookup`], wait for discovery.
pub const LOOKUP_WAIT: Duration = Duration::from_secs(3);

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use std::io;

    use vinc_crypto::IdentityAlg;

    use super::*;

    /// A hook that refuses everyone.
    struct Refuse;

    impl Admission for Refuse {
        fn admit(&self, _peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
            false
        }
    }

    /// The access hook is asked even while the endpoint's core is borrowed (a check made from inside a section of
    /// the endpoint, such as from a hook it is running): the answer is the hook's, never a default that admits.
    #[test]
    fn admit_asks_the_hook_while_the_core_is_borrowed() {
        let ep = Vinc::builder()
            .acp(Refuse)
            .limits(Limits {
                connections: 1,
                ..Limits::default()
            })
            .build(
                async |_buf: &mut [u8]| -> io::Result<(usize, SocketAddr)> { Err(io::ErrorKind::WouldBlock.into()) },
                async |pkt: &[u8], _to: SocketAddr| -> io::Result<usize> { Ok(pkt.len()) },
                async |_at: Instant| {},
            )
            .unwrap();
        let peer = NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [7; 32],
        };
        assert!(!ep.admit(&peer, b"t", Direction::Gossip));
        let held = ep.0.shared.lock();
        assert!(held.is_some(), "the core is free before the test borrows it");
        assert!(
            !ep.admit(&peer, b"t", Direction::Gossip),
            "a borrowed core admitted a refused peer"
        );
        assert!(!ep.admit(&peer, b"t", Direction::Inbound));
        drop(held);
    }
}
