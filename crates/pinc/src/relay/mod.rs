//! The relay host: the relay side of `pinc-connect` running on the host's sockets.
//!
//! A [`Relay`] accepts the byte streams members open ([`CarrierKind`](crate::CarrierKind)), authenticates each by a PINC handshake to the
//! relay's identity, and forwards their packets, serves signed records and lookups, answers address queries, holds
//! packets for sleeping members and notes their sleep notices, all by the state machine of `pinc-connect`. It starts no
//! thread or task and owns no runtime: the host passes its I/O as async closures ([`Udp`], [`Carriers`], [`Clock`])
//! and awaits [`Relay::run`], which polls everything. Handles are not `Send`.
//!
//! ```ignore
//! let relay = Relay::builder().limits(Limits::default()).build(
//!     Udp::new(async |buf| recv(buf).await, async |pkt, to| send(pkt, to).await),
//!     CarrierFns::new(accept, open, read, write, close),
//!     Clock::new(now_ns, sleep_until_ns),
//! )?;
//! relay.run().await?;
//! ```
//!
//! # Embedded or run as a service
//!
//! The relay owns no process, socket, runtime or timer. It runs on the closures the host passes, so a node can take
//! the relay role inside its own process: the host shares one UDP socket and one executor with its other endpoints,
//! awaits [`Relay::run`] next to them, and stops it with [`Relay::stop`] without ending anything else. No deployment
//! needs a relay service: any of its nodes that others can reach can take the role. A dedicated host can also run it
//! as a service of its own, as the relay server in `sourcenetwork/pinc_relay` does. The example binary is a minimal
//! host of the second kind.
//!
//! # What it keeps
//!
//! The identity is the host's key store. Signed records are handed to a [`Store`] as they are stored and restored from
//! it when [`Relay::run`] starts (the default [`MemStore`] keeps them in memory, shared between clones). The mailbox
//! of the state machine is in memory only.
//!
//! # What an operator sees
//!
//! [`Relay::stats`] has the counters (carriers up and down, packets forwarded, records, lookups, mailbox use, and
//! refusals by [`Reason`]) and [`Relay::next_event`] drains a bounded queue of [`Event`]s. Neither holds packet content
//! or keys.
//!
//! # Limits of the shape
//!
//! The tables are fixed at [`CARRIERS`] sessions, [`RECORDS`] records and [`MAILBOX_MEMBERS`] sleeping members of
//! [`MAILBOX_BYTES`] each; [`Limits`] lowers what is allowed within them. TLS in front of a WebSocket is the host's.
//! Dropping the future of [`Relay::run`] drops every stream without calling `close`; call [`Relay::stop`] and await
//! the run to close them one by one.

mod access;
mod carrier_fns;
mod carriers;
mod conn;
mod fx;
mod hub;
mod io;
mod limits;
mod part;
mod peers;
mod run;
mod state;
mod stats;
mod store;

use ::core::cell::{Cell, RefCell};
use ::core::net::SocketAddr;
use alloc::rc::Rc;
use alloc::vec::Vec;

use pinc_crypto::NodeId;
use pinc_keystore::{KeyStore, SoftwareStore};

pub use self::access::{Access, AllowAll};
pub use self::carrier_fns::CarrierFns;
pub use self::carriers::{Carriers, Completion, Done, Tag};
use self::hub::Hub;
pub use self::io::{Clock, Host, Hosted, NoCarriers, Udp, Unbuilt};
pub use self::limits::{CARRIERS, Limits, MAILBOX_BYTES, MAILBOX_MEMBERS, RECORDS};
use self::part::Made;
pub use self::part::{Part, SharedIdentity, StoreWrite};
pub use self::peers::Peer;
use self::run::Inner;
use self::state::Core;
#[cfg(feature = "trace")]
pub use self::state::probe::{KeepJob, KeepProbe};
pub use self::stats::{Closed, Event, Reason, Stats};
pub use self::store::{Kept, KeptRecord, MemStore, Store};
use crate::error::{Error, Result};
use crate::keys::Identity;

/// A relay. Clones are handles to the same relay.
pub struct Relay<H: Hosted, K: KeyStore = SoftwareStore, St: Store = MemStore, A: Access = AllowAll> {
    inner: Rc<Inner<H, K, St, A>>,
}

impl<H: Hosted, K: KeyStore, St: Store, A: Access> Clone for Relay<H, K, St, A> {
    fn clone(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
}

impl<H: Hosted, K: KeyStore, St: Store, A: Access> ::core::fmt::Debug for Relay<H, K, St, A> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        f.write_str("Relay")
    }
}

impl Relay<Unbuilt, SoftwareStore, MemStore, AllowAll> {
    /// Start configuring a relay.
    pub fn builder() -> Builder {
        Builder {
            identity: None,
            limits: Limits::default(),
            store: MemStore::new(),
            access: AllowAll,
            peers: Vec::new(),
            hub: None,
            tunnel: None,
        }
    }
}

/// The relay [`Builder::build`] makes over the host's closures.
pub type Built<R, S, C, N, Z, K, St> = Relay<Host<R, S, C, N, Z>, K, St>;

/// Configures a relay: its identity, limits, store, access policy and trusted peer relays.
pub struct Builder<K: KeyStore = SoftwareStore, St: Store = MemStore, A: Access = AllowAll> {
    identity: Option<SharedIdentity<K>>,
    limits: Limits,
    store: St,
    access: A,
    peers: Vec<Peer>,
    hub: Option<(SocketAddr, Vec<Vec<u8>>)>,
    tunnel: Option<SocketAddr>,
}

impl<K: KeyStore, St: Store, A: Access> ::core::fmt::Debug for Builder<K, St, A> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        f.write_str("Builder")
    }
}

impl<K: KeyStore, St: Store, A: Access> Builder<K, St, A> {
    /// The identity of the relay, in the key store the host chose. Required.
    pub fn identity<K2: KeyStore>(self, identity: Identity<K2>) -> Builder<K2, St, A> {
        self.shared_identity(Rc::new(RefCell::new(identity)))
    }

    /// The identity of the relay when it is shared with the node's endpoint: signing and key requests of both go through
    /// the one key store. The relay borrows it only inside a call. Required (or [`Builder::identity`]).
    pub fn shared_identity<K2: KeyStore>(self, identity: SharedIdentity<K2>) -> Builder<K2, St, A> {
        Builder {
            identity: Some(identity),
            limits: self.limits,
            store: self.store,
            access: self.access,
            peers: self.peers,
            hub: self.hub,
            tunnel: self.tunnel,
        }
    }

    /// The sizes and rates the relay runs with.
    #[must_use]
    pub fn limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// Where signed records are kept across a restart.
    pub fn store<St2: Store>(self, store: St2) -> Builder<K, St2, A> {
        Builder {
            identity: self.identity,
            limits: self.limits,
            store,
            access: self.access,
            peers: self.peers,
            hub: self.hub,
            tunnel: self.tunnel,
        }
    }

    /// Who may hold a carrier: asked once per carrier, after its handshake. The default admits every node.
    pub fn access<A2: Access>(self, access: A2) -> Builder<K, St, A2> {
        Builder {
            identity: self.identity,
            limits: self.limits,
            store: self.store,
            access,
            peers: self.peers,
            hub: self.hub,
            tunnel: self.tunnel,
        }
    }

    /// List `peer` as a peer relay: a carrier it opens with the peer protocol carries relay-to-relay traffic
    /// (forwarded packets and replicated records) instead of a member's, and when its node id is higher than this
    /// relay's, this relay opens a carrier to it with the host's `open` and keeps it up, dialing again after a failure.
    /// A relay never peers with itself, so one list can be given to every relay of a mesh. At most 32 other relays.
    #[must_use]
    pub fn peer(mut self, peer: Peer) -> Self {
        self.peers.push(peer);
        self
    }

    /// Run a hub endpoint on the relay's UDP socket, bound at `local`, that accepts sessions for the given protocols.
    /// Members with a validated UDP session can then send packets through the relay over UDP and receive the packets
    /// the relay holds for them; without a hub the tunnel is off and every packet travels on a carrier. Only for a
    /// relay built with [`Builder::build`]; a [`Part`] uses the node's endpoint ([`Builder::tunnel`]).
    #[must_use]
    pub fn hub(mut self, local: SocketAddr, alpns: &[&[u8]]) -> Self {
        self.hub = Some((local, alpns.iter().map(|a| a.to_vec()).collect()));
        self
    }

    /// Tunnel through the node's endpoint, bound at `local`, for a [`Part`] built with [`Builder::build_part`]: members
    /// with a validated UDP session to that endpoint can send packets through the relay over UDP. The endpoint is lent
    /// at each call ([`Part::hub`], [`Part::hub_event`], [`Part::datagram`], [`Part::after_datagram`]).
    #[must_use]
    pub fn tunnel(mut self, local: SocketAddr) -> Self {
        self.tunnel = Some(local);
        self
    }

    /// The state machine for a relay with a tunnel to `tunnel`, and what is left of the builder.
    fn make<S>(self, tunnel: Option<SocketAddr>, now: u64) -> Result<Made<S, K, St, A>> {
        self.limits.check()?;
        let Some(identity) = self.identity else {
            return Err(Error::config("a relay needs an identity: pass one to the builder"));
        };
        let identity_id = identity.borrow().node_id();
        let others = self.peers.iter().filter(|p| p.id != identity_id).count();
        if others > pinc_connect::relay::rule::MAX_PEERS {
            return Err(Error::config("a relay trusts at most 32 peer relays"));
        }
        let core = Core::new(Rc::clone(&identity), self.access, &self.peers, self.limits, tunnel, now)?;
        Ok((core, self.store, identity, self.limits))
    }

    /// Build the part of a relay that an outer driver runs, over the host's carriers: no socket, no clock, no endpoint of
    /// its own. `now` is the host's clock (nanoseconds since the Unix epoch). Nothing runs until the driver calls it.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) if a limit is out of range, there are more than 32 peers, the key
    /// store fails, or a hub was configured (a part tunnels through the node's endpoint: [`Builder::tunnel`]).
    pub fn build_part<C: Carriers>(self, carriers: C, now: u64) -> Result<Part<C, K, St, A>> {
        if self.hub.is_some() {
            return Err(Error::config(
                "a relay part has no hub of its own: tunnel through the node's endpoint",
            ));
        }
        let tunnel = self.tunnel;
        let (core, store, ..) = self.make(tunnel, now)?;
        Ok(Part::new(core, Rc::new(carriers), store))
    }

    /// Build the relay over the host's closures. Nothing runs until [`Relay::run`] is awaited.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) if a limit is out of range, there are more than 32 peers, or
    /// the key store fails.
    #[allow(clippy::type_complexity, reason = "the host's closures are named once, here")]
    pub fn build<R, S, C, N, Z>(
        mut self,
        udp: Udp<R, S>,
        carriers: C,
        clock: Clock<N, Z>,
    ) -> Result<Relay<Host<R, S, C, N, Z>, K, St, A>>
    where
        Host<R, S, C, N, Z>: Hosted<Streams = C, Stream = C::Stream>,
        C: Carriers,
    {
        if self.tunnel.is_some() {
            return Err(Error::config(
                "tunnel is for a relay part: a relay built with its own sockets uses hub",
            ));
        }
        let host = Host::new(udp, clock);
        let now = host.now();
        let hub = self.hub.take();
        let (core, store, identity, limits) = self.make(hub.as_ref().map(|h| h.0), now)?;
        let hub = match hub {
            Some((local, alpns)) => Some(Hub::new(local, &alpns, &identity, &limits, now)?),
            None => None,
        };
        Ok(Relay {
            inner: Rc::new(Inner {
                host,
                part: RefCell::new(Part::new(core, Rc::new(carriers), store)),
                hub: RefCell::new(hub),
                stop: Cell::new(false),
                waker: RefCell::new(None),
                running: Cell::new(false),
            }),
        })
    }
}

/// Ends a run, however it ends: every stream is dropped and the machine told, so a dropped run leaves no carrier open.
struct RunGuard<'a, H: Hosted, K: KeyStore, St: Store, A: Access>(&'a Inner<H, K, St, A>);

impl<H: Hosted, K: KeyStore, St: Store, A: Access> Drop for RunGuard<'_, H, K, St, A> {
    fn drop(&mut self) {
        self.0.running.set(false);
        if let Ok(mut part) = self.0.part.try_borrow_mut() {
            part.end(self.0.host.now());
        }
    }
}

impl<H: Hosted, K: KeyStore, St: Store, A: Access> Relay<H, K, St, A> {
    /// Serve until [`Relay::stop`]. Restores the stored records first, then accepts streams, reads datagrams and keeps
    /// the timers. Only one run can be awaited at a time.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) if a run is already awaited, or the error of the store if it
    /// cannot load the records (the relay does not start with an unknown set of records).
    pub async fn run(&self) -> Result<()> {
        if self.inner.running.replace(true) {
            return Err(Error::config("this relay is already running"));
        }
        let _guard = RunGuard(&self.inner);
        run::drive(&self.inner).await
    }

    /// Ask [`Relay::run`] to close every carrier and return.
    pub fn stop(&self) {
        self.inner.stop.set(true);
        if let Some(w) = self.inner.waker.borrow_mut().take() {
            w.wake();
        }
    }

    /// The counters.
    pub fn stats(&self) -> Stats {
        self.inner.part.borrow().stats()
    }

    /// The oldest event nobody has read yet.
    pub fn next_event(&self) -> Option<Event> {
        self.inner.part.borrow_mut().next_event()
    }

    /// The relay's node id.
    pub fn node_id(&self) -> NodeId {
        self.inner.part.borrow().node_id()
    }

    /// End the carrier of `node`, if it has one (its right to hold one was withdrawn); whether it had.
    pub fn close_carrier(&self, node: &NodeId) -> bool {
        let closed = self.inner.part.borrow_mut().close_carrier(node);
        if closed && let Some(w) = self.inner.waker.borrow_mut().take() {
            w.wake();
        }
        closed
    }
}
