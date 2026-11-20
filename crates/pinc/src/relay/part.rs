//! The embeddable part of a relay: the state machine, the carriers side, the store jobs, the limits, the stats and the
//! events, with no socket, no clock, no sleep and no endpoint of its own.
//!
//! An outer driver (the node's own, or [`Relay::run`](super::Relay::run), which is a thin loop over this) makes plain
//! calls and does the I/O itself:
//!
//! - a datagram arrived: [`Part::datagram`] (it says whether the relay took it: address discovery, a tunnelled or
//!   forwarded packet; otherwise the endpoint's owner takes it);
//! - the next datagram to send: [`Part::poll_transmit`];
//! - the next deadline and a timeout: [`Part::next_deadline`], [`Part::handle_timeout`];
//! - one poll that takes the carriers' completions and starts the operations that became due: [`Part::poll`], next to
//!   the future [`Part::drive`] the host's carriers need polled;
//! - the store write that is pending: [`Part::next_store_write`] and [`Part::store_written`], after [`Part::load`]
//!   and [`Part::restore`] at the start;
//! - the node's endpoint, lent at each call through [`pinc_node::Ep`]: [`Part::hub`] applies what the machine queued
//!   for it, [`Part::hub_event`] hears the events of the endpoint that concern the relay's members, and
//!   [`Part::tunnel`] takes the datagrams the endpoint addresses to a member.
//!
//! The identity is shared with the endpoint (`Rc<RefCell<Identity>>`): signing and key requests go through the one key
//! store. The part holds the borrow of the identity only inside a call, never across one, so the embedder must not hold
//! its own borrow while it calls the part.
//!
//! Invariants: no call waits; no borrow of the embedder's state outlives a call; every queue the part keeps is bounded;
//! the host's carriers are told when the part ends ([`Carriers::ended`]), once per run and once on drop.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;
use core::net::SocketAddr;
use core::task::{Context, Poll};

use pinc_crypto::NodeId;
use pinc_keystore::{KeyStore, SoftwareStore};
use pinc_node::Ep;

use super::access::{Access, AllowAll};
use super::carriers::{Carriers, Tag};
use super::limits::Limits;
use super::state::{Core, Job, Mark};
use super::stats::{Event, Stats};
use super::store::{Kept, MemStore, Store};
use crate::keys::Identity;

/// The most completions handled in one call of [`Part::poll`] before it returns.
const BUDGET: usize = 512;

/// One write to the store, taken by [`Part::next_store_write`] and run by the driver.
#[derive(Debug)]
pub struct StoreWrite<St> {
    store: Rc<St>,
    job: Job,
}

impl<St: Store> StoreWrite<St> {
    /// Do the write. Report the outcome with [`Part::store_written`].
    ///
    /// # Errors
    /// The store's error.
    pub async fn run(self) -> crate::Result<()> {
        match self.job {
            Job::Put(node, rec, received) => self.store.put(&node, &rec, received).await,
            Job::Remove(node) => self.store.remove(&node).await,
            Job::Mail(node, packets) => self.store.put_mailbox(&node, &packets).await,
        }
    }
}

/// The relay without its I/O. See the module docs.
pub struct Part<C: Carriers, K: KeyStore = SoftwareStore, St: Store = MemStore, A: Access = AllowAll> {
    pub(super) core: Core<C::Stream, K, A>,
    pub(super) carriers: Rc<C>,
    pub(super) store: Rc<St>,
    /// What the write out now is about; a failure or the end of the run marks it again.
    writing: Option<Mark>,
    /// [`Part::restore`] ran: the machine holds what the store kept.
    restored: bool,
}

impl<C: Carriers, K: KeyStore, St: Store, A: Access> core::fmt::Debug for Part<C, K, St, A> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Part")
    }
}

impl<C: Carriers, K: KeyStore, St: Store, A: Access> Part<C, K, St, A> {
    pub(super) fn new(core: Core<C::Stream, K, A>, carriers: Rc<C>, store: St) -> Self {
        Self {
            core,
            carriers,
            store: Rc::new(store),
            writing: None,
            restored: false,
        }
    }

    pub(super) fn identity(&self) -> SharedIdentity<K> {
        self.core.identity()
    }

    pub(super) fn queue_udp(&mut self, to: SocketAddr, bytes: &[u8]) {
        self.core.queue_udp(to, bytes);
    }

    /// The relay's node id.
    pub fn node_id(&self) -> NodeId {
        self.core.node_id()
    }

    /// The counters.
    pub fn stats(&self) -> Stats {
        self.core.stats()
    }

    /// The oldest event nobody has read yet.
    pub fn next_event(&mut self) -> Option<Event> {
        self.core.pop_event()
    }

    /// Everything the store kept; give it to [`Part::restore`] before the first poll. The future owns what it needs.
    ///
    /// # Errors
    /// The store's own error.
    pub fn load(&self) -> impl Future<Output = crate::Result<Kept>> + use<C, K, St, A> {
        let store = Rc::clone(&self.store);
        async move { store.load().await }
    }

    /// Whether [`Part::restore`] ran already. The machine then holds what the store kept: a second run of the part must
    /// not load and restore again (the held packets would be held twice), and the writes still owed stay queued.
    pub const fn restored(&self) -> bool {
        self.restored
    }

    /// Put what the store kept back: the records and the packets held for sleeping members.
    pub fn restore(&mut self, now: u64, kept: &Kept) {
        self.restored = true;
        self.core.restore(now, kept);
    }

    /// The work the host's carriers need polled; it never finishes. Poll it with the same waker as [`Part::poll`], first
    /// in each pass, and pass again while [`Part::poll`] reports progress. The future owns what it needs.
    pub fn drive(&self) -> impl Future<Output = ()> + use<C, K, St, A> {
        let carriers = Rc::clone(&self.carriers);
        async move { carriers.drive().await }
    }

    /// Take the completions of the carriers (at most a bounded batch), handle them, and start the operations that became
    /// due: an accept, reads and writes, the dials of peer relays, the closing of finished streams. Whether anything
    /// happened; if so, call it again after polling [`Part::drive`], and call it again at the next wake. `cx` is
    /// the waker of the task that runs the part.
    pub fn poll(&mut self, cx: &mut Context<'_>, now: u64) -> bool {
        let core = &mut self.core;
        let carriers = &*self.carriers;
        let mut progressed = false;
        if core.want_accept(now) {
            carriers.submit_accept(Tag::new(0));
        }
        let mut handled = 0;
        while handled < BUDGET
            && let Poll::Ready(done) = carriers.poll_completed(cx)
        {
            handled += 1;
            progressed = true;
            if let Some((tag, stream)) = core.complete(done, now) {
                carriers.close(tag, stream);
            }
        }
        while let Some(slot) = core.pop_submit() {
            if let Some((stream, buf)) = core.take_read(slot) {
                carriers.submit_read(&stream, core.tag(slot), buf);
                core.counters.stream_ops += 1;
            }
            if let Some((stream, buf, from)) = core.take_write(slot) {
                carriers.submit_write(&stream, core.tag(slot), buf, from);
                core.counters.stream_ops += 1;
            }
            progressed = true;
        }
        while let Some((i, peer, kind)) = core.next_dial(now) {
            carriers.submit_open(Tag::new(i as u64), &peer, kind);
            progressed = true;
        }
        while let Some(slot) = core.pop_reap() {
            let tag = core.tag(slot);
            if let Some(stream) = core.finish(slot, now) {
                carriers.close(tag, stream);
            }
            progressed = true;
        }
        progressed
    }

    /// A datagram arrived from `src`. Whether it was the relay's own (address discovery, a tunnelled or a forwarded
    /// packet): the part took it. If not, the caller gives it to the endpoint, then calls [`Part::after_datagram`].
    /// `ep` is only read, to tell which member the datagram came from.
    pub fn datagram<E: Ep>(&mut self, ep: &E, now: u64, src: SocketAddr, bytes: &mut [u8]) -> bool {
        let member = self.core.member_at(ep, &src);
        self.core.on_datagram(now, src, member, bytes)
    }

    /// The endpoint read a datagram from `src` that [`Part::datagram`] left to it. A packet from a member's validated
    /// direct address keeps the member's UDP session usable for the tunnel; asked after the read, the packet that
    /// validated the address counts too. `ep` is only read.
    pub fn after_datagram<E: Ep>(&mut self, ep: &E, now: u64, src: SocketAddr) {
        let member = self.core.member_at(ep, &src);
        self.core.on_heard(now, member);
    }

    /// The next datagram the relay wants to send: its remote, and its length in `out`. A datagram longer than `out` is
    /// dropped and counted.
    pub fn poll_transmit(&mut self, out: &mut [u8]) -> Option<(SocketAddr, usize)> {
        while let Some((to, buf)) = self.core.take_udp() {
            let n = buf.len();
            let fits = n <= out.len();
            if let Some(dst) = out.get_mut(..n) {
                dst.copy_from_slice(&buf);
            }
            self.core.udp_sent(fits, buf);
            if fits {
                return Some((to, n));
            }
        }
        None
    }

    /// When the part next needs [`Part::handle_timeout`], in nanoseconds of the host's clock, if it needs one.
    pub fn next_deadline(&self, now: u64) -> Option<u64> {
        let mut at = self.core.next_wake();
        if self.core.accept_paused(now) {
            at = at.min(self.core.accept_resume());
        }
        (at != u64::MAX).then_some(at)
    }

    /// Time passed: run the machine's timers and the checks of stream deadlines.
    pub fn handle_timeout(&mut self, now: u64) {
        self.core.on_timeout(now);
    }

    /// The next write to the store, if one is due and none is out. The driver runs it ([`StoreWrite::run`]) and reports
    /// with [`Part::store_written`].
    pub fn next_store_write(&mut self) -> Option<StoreWrite<St>> {
        if self.writing.is_some() {
            return None;
        }
        let job = self.core.next_job()?;
        self.writing = Some(job.mark());
        Some(StoreWrite {
            store: Rc::clone(&self.store),
            job,
        })
    }

    /// The write taken last finished, `ok` if the store kept it. A failure is counted and reported as an event, and the
    /// write is tried again, by the part's clock as of the last [`Part::poll`] or [`Part::handle_timeout`]: within one
    /// second of the failure, and never more often than once a second while the store fails.
    pub fn store_written(&mut self, ok: bool) {
        let mark = self.writing.take();
        if !ok {
            self.core.store_failed();
            if let Some(mark) = mark {
                self.core.requeue(mark);
                self.core.retry_after(self.core.now_hint());
            }
        }
    }

    /// Apply what the machine queued for the node's endpoint (packets from members' carriers, pulses for their sessions,
    /// datagrams for their addresses); whether anything was. The events the endpoint produced at once go to `out`, for
    /// the endpoint's owner to handle like the ones it polls. Call it after [`Part::poll`], [`Part::datagram`] and
    /// [`Part::handle_timeout`]. `now` is the endpoint's clock.
    pub fn hub<E: Ep>(&mut self, ep: &mut E, now: u64, out: &mut Vec<pinc_core::Event>) -> bool {
        self.core.hub_pump(ep, now, out)
    }

    /// The endpoint reported `ev`. Pass the events of sessions that are the relay's members ([`pinc_core::Event::Incoming`],
    /// [`pinc_core::Event::Closed`] and [`pinc_core::Event::PeerAwake`] matter); the others are ignored. A new member's
    /// session takes the member role. The events the endpoint produced at once go to `out`. `now` is the endpoint's
    /// clock, used for its commands, and `relay_now` the relay's own (the same one when the host keeps a single clock).
    pub fn hub_event<E: Ep>(
        &mut self,
        ep: &mut E,
        now: u64,
        relay_now: u64,
        ev: &pinc_core::Event,
        out: &mut Vec<pinc_core::Event>,
    ) {
        self.core.hub_event(ep, now, relay_now, ev, out);
    }

    /// The endpoint wants to send `bytes` to `remote`. Whether `remote` is a relay path address, which names a member:
    /// the packet then goes to the member's carrier and the caller sends nothing; if not, the caller sends it itself.
    pub fn tunnel(&mut self, now: u64, remote: &SocketAddr, bytes: &[u8]) -> bool {
        self.core.tunnel(now, remote, bytes)
    }

    /// A packet for a member was dropped before the part could take it: it is counted like one the hub had no room for.
    pub(crate) fn lost(&mut self) {
        self.core.hub_lost();
    }

    /// End the carrier of `node` (its right to hold one was withdrawn); whether it had one. The close shows in the next
    /// [`Part::poll`].
    pub fn close_carrier(&mut self, node: &NodeId) -> bool {
        self.core.revoke(node)
    }

    /// Close every carrier and accept no more; [`Part::poll`] works through the closing, and [`Part::is_stopped`] says
    /// when it is done.
    pub fn stop(&mut self) {
        self.core.begin_shutdown();
    }

    /// Whether [`Part::stop`] was called and every carrier is closed.
    pub fn is_stopped(&self) -> bool {
        self.core.stopping && self.core.idle()
    }

    /// The run is over: drop every stream and tell the host's carriers ([`Carriers::ended`]). Call it when the driver
    /// stops without having waited for [`Part::is_stopped`]; the part also does it when dropped.
    pub fn end(&mut self, now: u64) {
        // a write that was out is given back: the run that held it is gone
        if let Some(mark) = self.writing.take() {
            self.core.requeue(mark);
        }
        self.core.abort_all(now);
        self.carriers.ended();
    }
}

impl<C: Carriers, K: KeyStore, St: Store, A: Access> Drop for Part<C, K, St, A> {
    fn drop(&mut self) {
        let now = self.core.now_hint();
        self.end(now);
    }
}

/// The identity a part shares with its endpoint.
pub type SharedIdentity<K> = Rc<RefCell<Identity<K>>>;

/// What a builder makes: the state machine, the store, the identity and the limits.
pub(super) type Made<S, K, St, A> = (Core<S, K, A>, St, SharedIdentity<K>, Limits);

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, reason = "tests assert")]
mod tests {
    use alloc::vec;
    use core::cell::Cell;
    use core::future::pending;
    use core::pin::pin;
    use core::task::Waker;

    use pinc_crypto::{IdentityAlg, NodeId};

    use super::*;
    use crate::error::Error;
    use crate::relay::Relay;
    use crate::relay::carriers::{Completion, Tag};
    use crate::relay::peers::Peer;

    const T0: u64 = 1_000_000_000_000;
    const SEC: u64 = 1_000_000_000;

    /// Carriers that count the accepts asked of them and never complete anything.
    struct Mock(Rc<Cell<u32>>);

    impl Carriers for Mock {
        type Stream = ();

        fn submit_accept(&self, _: Tag) {
            self.0.set(self.0.get() + 1);
        }

        fn submit_open(&self, _: Tag, _: &Peer, _: crate::carrier::CarrierKind) {}

        fn submit_read(&self, _: &Rc<()>, _: Tag, _: Vec<u8>) {}

        fn submit_write(&self, _: &Rc<()>, _: Tag, _: Vec<u8>, _: usize) {}

        fn close(&self, _: Tag, _: Rc<()>) {}

        fn poll_completed(&self, _: &mut Context<'_>) -> Poll<Completion<()>> {
            Poll::Pending
        }

        fn drive(&self) -> impl Future<Output = ()> {
            pending()
        }
    }

    /// A store whose first mailbox write fails; it counts every mailbox write.
    #[derive(Clone, Default)]
    struct Flaky {
        writes: Rc<Cell<u32>>,
        fail_first: Rc<Cell<bool>>,
    }

    #[allow(clippy::unused_async_trait_impl, reason = "the test store never waits")]
    impl Store for Flaky {
        async fn load(&self) -> crate::Result<Kept> {
            Ok(Kept::default())
        }

        async fn put(&self, _: &NodeId, _: &[u8], _: u64) -> crate::Result<()> {
            Ok(())
        }

        async fn remove(&self, _: &NodeId) -> crate::Result<()> {
            Ok(())
        }

        async fn put_mailbox(&self, _: &NodeId, _: &[u8]) -> crate::Result<()> {
            self.writes.set(self.writes.get() + 1);
            if self.fail_first.replace(false) {
                Err(Error::config("the store failed"))
            } else {
                Ok(())
            }
        }
    }

    fn part(store: Flaky) -> (Part<Mock, SoftwareStore, Flaky>, Rc<Cell<u32>>) {
        let accepts = Rc::new(Cell::new(0));
        let p = Relay::builder()
            .identity(Identity::from_seed_with(&[7; 32], &[0; 32]).unwrap())
            .store(store)
            .build_part(Mock(Rc::clone(&accepts)), T0)
            .unwrap();
        (p, accepts)
    }

    fn done<T>(f: impl Future<Output = T>) -> T {
        let mut f = pin!(f);
        match f.as_mut().poll(&mut Context::from_waker(Waker::noop())) {
            Poll::Ready(v) => v,
            Poll::Pending => panic!("the store waited"),
        }
    }

    /// A member whose held packets the store has, in a form that does not parse: restoring it queues one mailbox write.
    fn owed_write() -> Kept {
        Kept {
            records: Vec::new(),
            mailboxes: vec![(
                NodeId {
                    alg: IdentityAlg::Ed25519,
                    bytes: [9; 32],
                },
                Vec::new(),
            )],
        }
    }

    #[test]
    fn a_run_that_ended_asks_for_an_accept_again() {
        let (mut p, accepts) = part(Flaky::default());
        let mut cx = Context::from_waker(Waker::noop());
        p.poll(&mut cx, T0);
        assert_eq!(accepts.get(), 1);
        p.end(T0);
        p.poll(&mut cx, T0 + SEC);
        assert_eq!(accepts.get(), 2, "the second run never asked for an accept");
    }

    #[test]
    fn a_write_in_flight_when_the_run_ends_is_given_back() {
        let (mut p, _) = part(Flaky::default());
        p.restore(T0, &owed_write());
        let w = p.next_store_write().expect("one write is owed");
        drop(w);
        p.end(T0);
        assert!(p.next_store_write().is_some(), "the write that was in flight is lost");
    }

    #[test]
    fn a_failed_write_is_tried_again_after_a_second() {
        let store = Flaky::default();
        store.fail_first.set(true);
        let (mut p, _) = part(store.clone());
        p.restore(T0, &owed_write());
        let w = p.next_store_write().expect("one write is owed");
        assert!(done(w.run()).is_err());
        p.store_written(false);
        assert_eq!(p.stats().store_errors, 1);
        assert!(p.next_store_write().is_none(), "the retry came at once");
        p.handle_timeout(T0 + SEC);
        let w = p.next_store_write().expect("the failed write was forgotten");
        assert!(done(w.run()).is_ok());
        p.store_written(true);
        assert_eq!(store.writes.get(), 2);
        assert!(p.next_store_write().is_none());
    }

    /// An idle part is woken for the retry of a failed write, though its own check comes later than the retry.
    #[test]
    fn a_failed_write_wakes_an_idle_part_for_its_retry() {
        let store = Flaky::default();
        store.fail_first.set(true);
        let (mut p, _) = part(store);
        p.restore(T0, &owed_write());
        p.handle_timeout(T0 + SEC / 2);
        let w = p.next_store_write().expect("one write is owed");
        assert!(done(w.run()).is_err());
        p.store_written(false);
        p.handle_timeout(T0 + SEC);
        assert_eq!(
            p.next_deadline(T0 + SEC),
            Some(T0 + SEC + SEC / 2),
            "the part sleeps past the retry"
        );
        p.handle_timeout(T0 + SEC + SEC / 2);
        assert!(p.next_store_write().is_some(), "the retry did not come");
    }

    #[test]
    fn a_part_knows_it_was_restored() {
        let (mut p, _) = part(Flaky::default());
        assert!(!p.restored());
        p.restore(T0, &Kept::default());
        assert!(
            p.restored(),
            "a second run would restore into a machine that holds it all"
        );
    }
}
