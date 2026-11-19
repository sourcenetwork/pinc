//! The relay role of an endpoint: what the driver asks of a relay that runs inside the endpoint's own process.
//!
//! An endpoint can be a relay for other nodes as well as a node: [`Builder::relay_role`](crate::Builder::relay_role)
//! gives it the relay part (`relay::Part`, the relay state machine without its I/O) and the host's carriers for the
//! streams its members open. The role shares the endpoint's identity, socket and clock, and starts no task, thread or
//! channel: the future of [`Endpoint::run`](crate::Endpoint::run) drives it beside the endpoint. [`Role`] is the
//! seam: the endpoint without the role has the unit role, whose every call is empty and whose [`Role::ON`] is false,
//! so the driver's role branches are not compiled in and the data path of such an endpoint does no work for a role.
//!
//! Invariants: the role is borrowed only inside a call and never across an await or a call of a host closure; the part
//! is given the relay clock (nanoseconds since the Unix epoch) and the endpoint its own, the driver adding the fixed
//! offset between them; the in-flight operations of the host's carriers live in the future of `run`, so a role is
//! driven by one `run` at a time and ends when it ends.

use alloc::vec::Vec;
use core::future::{Ready, pending, ready};
use core::net::SocketAddr;
use core::task::Context;

use pinc_core::Event;
use pinc_crypto::NodeId;
use pinc_keystore::KeyStore;
use pinc_node::Ep;

use crate::error::Result;
use crate::keys::Identity;
use crate::relay::{Access, Builder as RelayBuilder, Carriers, Kept, Part, Stats, Store};

mod sealed {
    pub trait Sealed {}
}

/// What an endpoint's driver does with its relay role. Only the unit type (no role) and [`Part`] implement it.
pub trait Role: sealed::Sealed + Sized {
    /// Whether there is a role at all; the driver's role branches test it, so they vanish for the unit role.
    #[doc(hidden)]
    const ON: bool;

    /// A datagram arrived from `src`: whether the relay took it, else the endpoint takes it.
    #[doc(hidden)]
    fn offer<E: Ep>(&mut self, ep: &E, now: u64, src: SocketAddr, bytes: &mut [u8]) -> bool;

    /// The endpoint read a session packet from `src` that the relay did not take.
    #[doc(hidden)]
    fn after_offer<E: Ep>(&mut self, ep: &E, now: u64, src: SocketAddr);

    /// Apply what the relay queued for the endpoint; whether anything was.
    #[doc(hidden)]
    fn pump<E: Ep>(&mut self, ep: &mut E, now: u64, out: &mut Vec<Event>) -> bool;

    /// The endpoint reported an event of a hub session.
    #[doc(hidden)]
    fn heard<E: Ep>(&mut self, ep: &mut E, now: u64, relay_now: u64, ev: &Event, out: &mut Vec<Event>);

    /// The endpoint wants to send `bytes` to `remote`: whether `remote` names a member, so the relay carries it.
    #[doc(hidden)]
    fn carry(&mut self, relay_now: u64, remote: &SocketAddr, bytes: &[u8]) -> bool;

    /// The next datagram the relay wants to send: its remote and its length in `out`.
    #[doc(hidden)]
    fn outgoing(&mut self, out: &mut [u8]) -> Option<(SocketAddr, usize)>;

    /// When the relay next needs [`Role::tick`], on the relay clock.
    #[doc(hidden)]
    fn due(&self, relay_now: u64) -> Option<u64>;

    /// Time passed: run the relay's timers.
    #[doc(hidden)]
    fn tick(&mut self, relay_now: u64);

    /// Take the carriers' completions and start what became due; whether anything happened.
    #[doc(hidden)]
    fn poll_io(&mut self, cx: &mut Context<'_>, relay_now: u64) -> bool;

    /// The work the host's carriers need polled; it never finishes.
    #[doc(hidden)]
    fn start_io(&self) -> impl Future<Output = ()> + use<Self>;

    /// Everything the store kept, to give to [`Role::restore`].
    #[doc(hidden)]
    fn load(&self) -> impl Future<Output = Result<Kept>> + use<Self>;

    /// Put what the store kept back.
    #[doc(hidden)]
    fn restore(&mut self, relay_now: u64, kept: &Kept);

    /// The next write to the store, if one is due and none is out.
    #[doc(hidden)]
    fn next_write(&mut self) -> Option<impl Future<Output = Result<()>> + use<Self>>;

    /// The write taken last finished.
    #[doc(hidden)]
    fn written(&mut self, ok: bool);

    /// The run is over: drop every carrier.
    #[doc(hidden)]
    fn end(&mut self, relay_now: u64);

    /// The relay's counters.
    #[doc(hidden)]
    fn stats(&self) -> Option<Stats>;

    /// The oldest event of the relay nobody has read.
    #[doc(hidden)]
    fn next_event(&mut self) -> Option<crate::relay::Event>;

    /// End the carrier of `node`; whether it had one.
    #[doc(hidden)]
    fn close_carrier(&mut self, node: &NodeId) -> bool;
}

impl sealed::Sealed for () {}

/// No relay role: nothing to do and nothing compiled in.
impl Role for () {
    const ON: bool = false;

    fn offer<E: Ep>(&mut self, _: &E, _: u64, _: SocketAddr, _: &mut [u8]) -> bool {
        false
    }

    fn after_offer<E: Ep>(&mut self, _: &E, _: u64, _: SocketAddr) {}

    fn pump<E: Ep>(&mut self, _: &mut E, _: u64, _: &mut Vec<Event>) -> bool {
        false
    }

    fn heard<E: Ep>(&mut self, _: &mut E, _: u64, _: u64, _: &Event, _: &mut Vec<Event>) {}

    fn carry(&mut self, _: u64, _: &SocketAddr, _: &[u8]) -> bool {
        false
    }

    fn outgoing(&mut self, _: &mut [u8]) -> Option<(SocketAddr, usize)> {
        None
    }

    fn due(&self, _: u64) -> Option<u64> {
        None
    }

    fn tick(&mut self, _: u64) {}

    fn poll_io(&mut self, _: &mut Context<'_>, _: u64) -> bool {
        false
    }

    fn start_io(&self) -> impl Future<Output = ()> + use<> {
        pending()
    }

    fn load(&self) -> impl Future<Output = Result<Kept>> + use<> {
        ready(Ok(Kept::default()))
    }

    fn restore(&mut self, _: u64, _: &Kept) {}

    fn next_write(&mut self) -> Option<impl Future<Output = Result<()>> + use<>> {
        None::<Ready<Result<()>>>
    }

    fn written(&mut self, _: bool) {}

    fn end(&mut self, _: u64) {}

    fn stats(&self) -> Option<Stats> {
        None
    }

    fn next_event(&mut self) -> Option<crate::relay::Event> {
        None
    }

    fn close_carrier(&mut self, _: &NodeId) -> bool {
        false
    }
}

impl<C: Carriers, K: KeyStore, St: Store, A: Access> sealed::Sealed for Part<C, K, St, A> {}

impl<C: Carriers, K: KeyStore, St: Store, A: Access> Role for Part<C, K, St, A> {
    const ON: bool = true;

    fn offer<E: Ep>(&mut self, ep: &E, now: u64, src: SocketAddr, bytes: &mut [u8]) -> bool {
        self.datagram(ep, now, src, bytes)
    }

    fn after_offer<E: Ep>(&mut self, ep: &E, now: u64, src: SocketAddr) {
        self.after_datagram(ep, now, src);
    }

    fn pump<E: Ep>(&mut self, ep: &mut E, now: u64, out: &mut Vec<Event>) -> bool {
        self.hub(ep, now, out)
    }

    fn heard<E: Ep>(&mut self, ep: &mut E, now: u64, relay_now: u64, ev: &Event, out: &mut Vec<Event>) {
        self.hub_event(ep, now, relay_now, ev, out);
    }

    fn carry(&mut self, relay_now: u64, remote: &SocketAddr, bytes: &[u8]) -> bool {
        self.tunnel(relay_now, remote, bytes)
    }

    fn outgoing(&mut self, out: &mut [u8]) -> Option<(SocketAddr, usize)> {
        self.poll_transmit(out)
    }

    fn due(&self, relay_now: u64) -> Option<u64> {
        self.next_deadline(relay_now)
    }

    fn tick(&mut self, relay_now: u64) {
        self.handle_timeout(relay_now);
    }

    fn poll_io(&mut self, cx: &mut Context<'_>, relay_now: u64) -> bool {
        self.poll(cx, relay_now)
    }

    fn start_io(&self) -> impl Future<Output = ()> + use<C, K, St, A> {
        self.drive()
    }

    fn load(&self) -> impl Future<Output = Result<Kept>> + use<C, K, St, A> {
        Part::load(self)
    }

    fn restore(&mut self, relay_now: u64, kept: &Kept) {
        Part::restore(self, relay_now, kept);
    }

    fn next_write(&mut self) -> Option<impl Future<Output = Result<()>> + use<C, K, St, A>> {
        self.next_store_write().map(crate::relay::StoreWrite::run)
    }

    fn written(&mut self, ok: bool) {
        self.store_written(ok);
    }

    fn end(&mut self, relay_now: u64) {
        Part::end(self, relay_now);
    }

    fn stats(&self) -> Option<Stats> {
        Some(Part::stats(self))
    }

    fn next_event(&mut self) -> Option<crate::relay::Event> {
        Part::next_event(self)
    }

    fn close_carrier(&mut self, node: &NodeId) -> bool {
        Part::close_carrier(self, node)
    }
}

/// What a builder holds for the role until the endpoint's identity is known, and what builds it. Only the unit type
/// (no role) and [`RelayRole`] implement it.
pub trait RoleSpec<K: KeyStore>: sealed::Sealed {
    /// The role it makes.
    type Built: Role;

    /// Build the role over the endpoint's identity, bound at `local`, at relay clock `relay_now`.
    #[doc(hidden)]
    fn build(
        self,
        identity: alloc::rc::Rc<core::cell::RefCell<Identity<K>>>,
        local: SocketAddr,
        relay_now: u64,
    ) -> Result<Self::Built>;
}

impl<K: KeyStore> RoleSpec<K> for () {
    type Built = ();

    fn build(self, _: alloc::rc::Rc<core::cell::RefCell<Identity<K>>>, _: SocketAddr, _: u64) -> Result<()> {
        Ok(())
    }
}

/// The settings of the relay role and the host's carriers for its members: made by
/// [`Builder::relay_role`](crate::Builder::relay_role).
pub struct RelayRole<C, St: Store, A: Access> {
    pub(crate) builder: RelayBuilder<pinc_keystore::SoftwareStore, St, A>,
    pub(crate) carriers: C,
}

impl<C, St: Store, A: Access> core::fmt::Debug for RelayRole<C, St, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("RelayRole")
    }
}

impl<C, St: Store, A: Access> sealed::Sealed for RelayRole<C, St, A> {}

impl<K: KeyStore, C: Carriers, St: Store, A: Access> RoleSpec<K> for RelayRole<C, St, A> {
    type Built = Part<C, K, St, A>;

    fn build(
        self,
        identity: alloc::rc::Rc<core::cell::RefCell<Identity<K>>>,
        local: SocketAddr,
        relay_now: u64,
    ) -> Result<Part<C, K, St, A>> {
        self.builder
            .shared_identity(identity)
            .tunnel(local)
            .build_part(self.carriers, relay_now)
    }
}
