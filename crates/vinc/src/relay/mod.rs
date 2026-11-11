//! The relay host: the relay side of `vinc-connect` running on the host's sockets.
//!
//! A [`Relay`] accepts the byte streams members open ([`CarrierKind`](crate::CarrierKind)), authenticates each by a VINC handshake to the
//! relay's identity, and forwards their packets, serves signed records and lookups, answers address queries, holds
//! packets for sleeping members and notes their sleep notices, all by the state machine of `vinc-connect`. It starts no
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
//! # Embedded, not a service
//!
//! The relay is a role an ordinary node takes inside its own process, never a separate service: it owns no process,
//! socket, runtime or timer. It runs on the closures the host passes, so the host can share one UDP socket and one
//! executor with its other endpoints, await [`Relay::run`] next to them, and stop it with [`Relay::stop`] without
//! ending anything else. The example binary is only an example of such a host.
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

mod carrier_fns;
mod carriers;
mod conn;
mod fx;
mod hub;
mod io;
mod limits;
mod peers;
mod run;
mod state;
mod stats;
mod store;

use ::core::cell::{Cell, RefCell};
use alloc::rc::Rc;
use alloc::vec::Vec;

use vinc_crypto::NodeId;
use vinc_keystore::{KeyStore, SoftwareStore};

pub use self::carrier_fns::CarrierFns;
pub use self::carriers::{Carriers, Completion, Done, Tag};
pub use self::io::{Clock, Host, Hosted, NoCarriers, Udp, Unbuilt};
pub use self::limits::{CARRIERS, Limits, MAILBOX_BYTES, MAILBOX_MEMBERS, RECORDS};
pub use self::peers::Peer;
use self::run::Inner;
use self::state::Core;
pub use self::stats::{Closed, Event, Reason, Stats};
pub use self::store::{Kept, KeptRecord, MemStore, Store};
use crate::error::{Error, Result};
use crate::keys::Identity;

/// A relay. Clones are handles to the same relay.
pub struct Relay<H: Hosted, K: KeyStore = SoftwareStore, St: Store = MemStore> {
    inner: Rc<Inner<H, K, St>>,
}

impl<H: Hosted, K: KeyStore, St: Store> Clone for Relay<H, K, St> {
    fn clone(&self) -> Self {
        Self {
            inner: Rc::clone(&self.inner),
        }
    }
}

impl<H: Hosted, K: KeyStore, St: Store> ::core::fmt::Debug for Relay<H, K, St> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        f.write_str("Relay")
    }
}

impl Relay<Unbuilt, SoftwareStore, MemStore> {
    /// Start configuring a relay.
    pub fn builder() -> Builder {
        Builder {
            identity: None,
            limits: Limits::default(),
            store: MemStore::new(),
            peers: Vec::new(),
            hub: None,
        }
    }
}

/// The relay [`Builder::build`] makes over the host's closures.
pub type Built<R, S, C, N, Z, K, St> = Relay<Host<R, S, C, N, Z>, K, St>;

/// Configures a relay: its identity, limits, store and trusted peer relays.
pub struct Builder<K: KeyStore = SoftwareStore, St: Store = MemStore> {
    identity: Option<Identity<K>>,
    limits: Limits,
    store: St,
    peers: Vec<Peer>,
    hub: Option<(::core::net::SocketAddr, Vec<Vec<u8>>)>,
}

impl<K: KeyStore, St: Store> ::core::fmt::Debug for Builder<K, St> {
    fn fmt(&self, f: &mut ::core::fmt::Formatter<'_>) -> ::core::fmt::Result {
        f.write_str("Builder")
    }
}

impl<K: KeyStore, St: Store> Builder<K, St> {
    /// The identity of the relay, in the key store the host chose. Required.
    pub fn identity<K2: KeyStore>(self, identity: Identity<K2>) -> Builder<K2, St> {
        Builder {
            identity: Some(identity),
            limits: self.limits,
            store: self.store,
            peers: self.peers,
            hub: self.hub,
        }
    }

    /// The sizes and rates the relay runs with.
    #[must_use]
    pub fn limits(mut self, limits: Limits) -> Self {
        self.limits = limits;
        self
    }

    /// Where signed records are kept across a restart.
    pub fn store<St2: Store>(self, store: St2) -> Builder<K, St2> {
        Builder {
            identity: self.identity,
            limits: self.limits,
            store,
            peers: self.peers,
            hub: self.hub,
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
    /// the relay holds for them; without a hub the tunnel is off and every packet travels on a carrier.
    #[must_use]
    pub fn hub(mut self, local: ::core::net::SocketAddr, alpns: &[&[u8]]) -> Self {
        self.hub = Some((local, alpns.iter().map(|a| a.to_vec()).collect()));
        self
    }

    /// Build the relay over the host's closures. Nothing runs until [`Relay::run`] is awaited.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) if a limit is out of range, there are more than 32 peers, or
    /// the key store fails.
    #[allow(clippy::type_complexity, reason = "the host's closures are named once, here")]
    pub fn build<R, S, C, N, Z>(
        self,
        udp: Udp<R, S>,
        carriers: C,
        clock: Clock<N, Z>,
    ) -> Result<Built<R, S, C, N, Z, K, St>>
    where
        Host<R, S, C, N, Z>: Hosted<Stream = C::Stream>,
        C: Carriers,
    {
        self.limits.check()?;
        let Some(identity) = self.identity else {
            return Err(Error::config("a relay needs an identity: pass one to the builder"));
        };
        let identity_id = identity.node_id();
        let others = self.peers.iter().filter(|p| p.id != identity_id).count();
        if others > vinc_connect::relay::rule::MAX_PEERS {
            return Err(Error::config("a relay trusts at most 32 peer relays"));
        }
        let host = Host::new(udp, carriers, clock);
        let core = Core::new(identity, &self.peers, self.limits, self.hub, host.now())?;
        Ok(Relay {
            inner: Rc::new(Inner {
                host,
                store: self.store,
                core: RefCell::new(core),
                stop: Cell::new(false),
                waker: RefCell::new(None),
                running: Cell::new(false),
            }),
        })
    }
}

/// Ends a run, however it ends: every stream is dropped and the machine told, so a dropped run leaves no carrier open.
struct RunGuard<'a, H: Hosted, K: KeyStore, St>(&'a Inner<H, K, St>);

impl<H: Hosted, K: KeyStore, St> Drop for RunGuard<'_, H, K, St> {
    fn drop(&mut self) {
        self.0.running.set(false);
        if let Ok(mut core) = self.0.core.try_borrow_mut() {
            core.abort_all(self.0.host.now());
        }
    }
}

impl<H: Hosted, K: KeyStore, St: Store> Relay<H, K, St> {
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
        self.inner.core.borrow().stats()
    }

    /// The oldest event nobody has read yet.
    pub fn next_event(&self) -> Option<Event> {
        self.inner.core.borrow_mut().pop_event()
    }

    /// The relay's node id.
    pub fn node_id(&self) -> NodeId {
        self.inner.core.borrow().node_id()
    }
}
