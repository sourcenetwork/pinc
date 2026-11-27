//! The driving: how the futures of the facade run the endpoint with the host's three closures, with no task, no channel
//! and no thread of the library's own.
//!
//! Every facade future is one call of [`Shared::run`]. It locks the core, serves what is due, and tries its operation;
//! if the operation must wait it registers a ticket under the thing it waits for and then looks for the driving role:
//! a flag that exactly one waiting future holds. The holder keeps the host's pending receive and sleep
//! futures inside its own state, so a datagram or a deadline wakes the holder's task; it feeds the datagram to the
//! core, which wakes the futures the datagram is for. The role is sticky: the holder keeps it while it waits. When it
//! finishes or is dropped it clears the flag and wakes the oldest waiting future, which takes the role if it still
//! waits. A future that does not hold the role only waits on its ticket. A future whose call took its value out of the
//! endpoint (a read, an accept, an open, a dial) returns it at once, and what the endpoint wants to send goes with the
//! next poll of any future (pinc#636, pinc#702: a result is never kept back for a send, so a dropped future loses
//! nothing); a call whose payload is the send (a write, a datagram, a close) sends first and returns after, so the
//! endpoint's last packets never wait for a poll that never comes.
//!
//! Everything runs on the thread that built the endpoint, so the flag is a `Cell` and the core a `RefCell`.
//!
//! Invariants: at most one future holds the role; the flag, the baton and a ticket's registration change in one
//! borrow of the core, so a wake is never lost between a failed attempt and the wait; no borrow is held across an await
//! or a call of a host closure; the receive and transmit buffers come from two small pools (the endpoints of the
//! thread share them with `std`; each endpoint holds its own without, reserved when it is built) and go back when
//! dropped, so steady traffic allocates none, however many futures send at once; with no future polled the endpoint
//! makes no progress, which is the SANS-IO contract.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell, RefMut};
use core::future::poll_fn;
use core::net::{IpAddr, SocketAddr};
use core::pin::pin;
use core::task::Poll;
use core::time::Duration;

mod carrier_io;
mod http_io;
mod role_io;
#[cfg(feature = "trace")]
mod turn_probe;

pub(crate) use role_io::RoleEnd;

use crate::carriers::{Carriers, Relay};
use crate::engine::{Core, Try, Wait};
use crate::error::Error;
use crate::host::Hosted;
use crate::platform::{HostError, HostInstant, Platform};
use crate::role::Role;
use crate::standby::Ticket;

/// The first time the endpoint sees, so no time is zero.
pub(crate) const T0: u64 = 10_000_000_000;
/// The relay role's clock at endpoint time `now`: the wall clock at the first instant plus the time elapsed since.
pub(crate) const fn role_clock(origin: u64, now: u64) -> u64 {
    origin.saturating_add(now.saturating_sub(T0))
}

/// The endpoint time at which the role's clock reads `at`.
pub(crate) const fn endpoint_clock(origin: u64, at: u64) -> u64 {
    T0.saturating_add(at.saturating_sub(origin))
}

/// The largest UDP payload: the most a coalesced receive or a batched transmit holds.
const UDP_MAX: usize = 65_536;
/// The most datagrams read in one burst before the endpoint runs.
const DRAIN: usize = 256;
/// The most buffers each pool keeps.
const POOLED: usize = 8;

/// A pool of buffers.
type Pool = Rc<RefCell<Vec<Vec<u8>>>>;

#[cfg(feature = "std")]
std::thread_local! {
    /// The receive buffers the endpoints of this thread share.
    static RX_BUFS: Pool = Pool::default();
    /// The transmit buffers the endpoints of this thread share.
    static TX_BUFS: Pool = Pool::default();
}

/// The receive and transmit pools of an endpoint being built: those of its thread.
#[cfg(feature = "std")]
fn pools(_rx_len: usize, _tx_len: usize) -> (Pool, Pool) {
    (RX_BUFS.with(Rc::clone), TX_BUFS.with(Rc::clone))
}

/// The receive and transmit pools of an endpoint being built: its own, each with one buffer of its size and room for
/// `POOLED`, so a buffer that goes back never allocates.
#[cfg(not(feature = "std"))]
fn pools(rx_len: usize, tx_len: usize) -> (Pool, Pool) {
    let one = |len: usize| {
        let mut pool = Vec::with_capacity(POOLED);
        pool.push(vec![0; len]);
        Rc::new(RefCell::new(pool))
    };
    (one(rx_len), one(tx_len))
}

/// The state every handle of an endpoint shares.
pub(crate) struct Shared<H: Hosted> {
    pub(crate) host: H,
    start: <H::Platform as Platform>::Instant,
    local: SocketAddr,
    driving: Cell<bool>,
    /// The access hook, the same one the core asks; it holds no endpoint state, so it is asked without the core.
    pub(crate) admit: Rc<crate::engine::Gate<H::Access>>,
    core: RefCell<Core<H::Keys, H::Access>>,
    /// The relays, in the order the node numbers them.
    relays: Vec<Relay>,
    /// The state of the carriers to the relays; see [`carrier_io`].
    carriers: RefCell<carrier_io::Slots<<H::Carriers as Carriers<H::Platform>>::Stream>>,
    /// A carrier moved bytes or changed state during the last poll: the endpoint has more to do.
    cdirty: Cell<bool>,
    /// The host turned port mapping on: only then is there an HTTP exchange to advance.
    port_mapping: bool,
    /// The HTTP exchange of the port-mapping client while one runs; see [`http_io`].
    http: RefCell<http_io::Held<H>>,
    /// The receive and transmit buffers: shared by every endpoint on this thread with `std`, the endpoint's own
    /// without. A receive buffer is held while a future drives the endpoint and a transmit buffer while a transmit is
    /// built and sent, so with `std` endpoints that are mostly idle share a few instead of keeping two each.
    rx_bufs: Pool,
    tx_bufs: Pool,
    /// The size of a transmit buffer: the endpoint's batch of datagrams of the largest size.
    tx_len: usize,
    /// The wall clock at the endpoint's first instant, which the relay role's clock counts from; see [`role_io`].
    role_wall0: u64,
    /// The role's records are restored: its datagrams are read and its work done only from then on.
    role_ready: Cell<bool>,
    /// The role's carriers moved during the last poll: the endpoint has more to do.
    rdirty: Cell<bool>,
}

/// A buffer that goes back to its pool when dropped.
struct Buf<'a> {
    v: Vec<u8>,
    home: &'a RefCell<Vec<Vec<u8>>>,
}

impl Drop for Buf<'_> {
    fn drop(&mut self) {
        let v = core::mem::take(&mut self.v);
        // A pool borrowed at this moment is never: the borrows are short and nothing calls out while holding one.
        if let Ok(mut pool) = self.home.try_borrow_mut()
            && pool.len() < POOLED
        {
            pool.push(v);
        }
    }
}

/// What one poll of an operation decided.
enum Step<T> {
    /// The attempt is done and its call's payload is the send: the poll sends what the attempt queued before the value
    /// returns.
    Sent(T),
    /// The value was taken out of the endpoint (a read, an accept, an open, a dial): it returns in this poll, before
    /// anything is sent.
    Taken(T),
    Io,
}

/// The I/O error of a host's platform.
type HostErr<H> = <<H as Hosted>::Platform as Platform>::Error;

/// The address as the socket takes it.
pub(crate) fn wire(a: SocketAddr, socket_v6: bool) -> SocketAddr {
    match (a.ip(), socket_v6) {
        (IpAddr::V4(v4), true) => SocketAddr::new(v4.to_ipv6_mapped().into(), a.port()),
        _ => a,
    }
}

/// A buffer of `len` bytes from `home`, or a new one. A pooled buffer of another length (the endpoints of a thread may
/// batch differently) is cut or zero-extended to `len`.
fn pooled(home: &RefCell<Vec<Vec<u8>>>, len: usize) -> Buf<'_> {
    let v = home.try_borrow_mut().ok().and_then(|mut b| b.pop());
    let mut v = v.unwrap_or_else(|| vec![0; len]);
    v.resize(len, 0);
    Buf { v, home }
}

async fn recv_owned<'a, H: Hosted>(
    host: &H,
    mut buf: Buf<'a>,
) -> (Result<(usize, SocketAddr, usize), HostErr<H>>, Buf<'a>) {
    let r = host.recv(buf.v.as_mut_slice()).await;
    (r, buf)
}

async fn sleep_owned<H: Hosted>(host: &H, at: <H::Platform as Platform>::Instant) {
    host.sleep(at).await;
}

/// The guard of one operation: what it registered and whether it holds the driving role, undone when it ends.
struct Turn<'a, H: Hosted> {
    sh: &'a Shared<H>,
    ticket: Option<Ticket>,
    wait: Option<Wait>,
    driving: bool,
    /// Whether the call returned (else the host dropped it), for the mark that follows the release.
    #[cfg(feature = "trace")]
    returned: bool,
    /// Whether the call returned a value it took out of the endpoint, in the poll that took it.
    #[cfg(feature = "trace")]
    taken: bool,
}

impl<H: Hosted> Drop for Turn<'_, H> {
    fn drop(&mut self) {
        self.release();
        #[cfg(feature = "trace")]
        turn_probe::end(self.sh, self.returned, self.taken);
    }
}

impl<H: Hosted> Turn<'_, H> {
    /// Undo what the call registered, and offer the role on.
    fn release(&mut self) {
        let Some(t) = self.ticket else { return };
        if self.driving {
            self.sh.driving.set(false);
        }
        let Some(mut core) = self.sh.lock() else { return };
        if let Some(w) = self.wait {
            core.forget(w, t);
        }
        core.standby.release(t);
        if self.driving {
            core.driver = None;
            core.armed = u64::MAX;
            #[cfg(feature = "trace")]
            core.standby.mark(crate::trace_waits::Mark::Pass);
            core.standby.baton();
        } else if !self.sh.driving.get() {
            // This future may have been the one the baton was offered to: offer it on.
            #[cfg(feature = "trace")]
            core.standby.mark(crate::trace_waits::Mark::Pass);
            core.standby.baton();
        }
    }
}

impl<H: Hosted> Shared<H> {
    /// The shared state of an endpoint whose transmits batch up to `gso` datagrams.
    pub(crate) fn new(
        host: H,
        core: Core<H::Keys, H::Access>,
        local: SocketAddr,
        gso: usize,
        relays: Vec<Relay>,
        role_wall0: u64,
    ) -> Self {
        let port_mapping = core.node.has_port_mapping();
        let start = host.platform().now();
        let tx_len = gso.clamp(1, UDP_MAX / pinc_core::MAX_DATAGRAM) * pinc_core::MAX_DATAGRAM;
        let (rx_bufs, tx_bufs) = pools(H::RECV_MAX, tx_len);
        Self {
            host,
            start,
            local,
            driving: Cell::new(false),
            admit: core.hook(),
            core: RefCell::new(core),
            relays,
            carriers: RefCell::new(carrier_io::slots()),
            cdirty: Cell::new(false),
            port_mapping,
            http: RefCell::new(None),
            rx_bufs,
            tx_bufs,
            tx_len,
            role_wall0,
            role_ready: Cell::new(false),
            rdirty: Cell::new(false),
        }
    }

    pub(crate) const fn local(&self) -> SocketAddr {
        self.local
    }

    /// The core, borrowed for a short section. `None` only if a borrow is already open, which nothing that runs on this
    /// thread can arrange: no borrow is held across an await or a call of a host closure.
    pub(crate) fn lock(&self) -> Option<RefMut<'_, Core<H::Keys, H::Access>>> {
        self.core.try_borrow_mut().ok()
    }

    /// Serve `core` at `now`; a prekey rotation offers the identity's store 32 fresh bytes of the platform's randomness.
    pub(crate) fn service(&self, core: &mut Core<H::Keys, H::Access>, now: u64) -> usize {
        core.service(now, &mut |out| self.host.platform().random(out).is_ok())
    }

    /// The endpoint's clock: nanoseconds since the endpoint was made, after a fixed offset.
    pub(crate) fn now(&self) -> u64 {
        let since = self.host.platform().now().since(self.start);
        T0.saturating_add(u64::try_from(since.as_nanos()).unwrap_or(u64::MAX))
    }

    pub(crate) fn instant(&self, at: u64) -> <H::Platform as Platform>::Instant {
        self.start.add(Duration::from_nanos(at.saturating_sub(T0)))
    }

    fn rx_buf(&self) -> Buf<'_> {
        pooled(&self.rx_bufs, H::RECV_MAX)
    }

    fn tx_buf(&self) -> Buf<'_> {
        pooled(&self.tx_bufs, self.tx_len)
    }

    /// Run `attempt` until it is done. Each time it cannot finish it names what it waits for; the future is woken when
    /// that changes, and meanwhile drives the endpoint if it holds the role. The attempt must be safe to repeat.
    pub(crate) fn run<T>(
        &self,
        attempt: impl FnMut(&mut Core<H::Keys, H::Access>, u64) -> Try<T>,
    ) -> impl Future<Output = T> {
        self.run_as(false, attempt)
    }

    /// As [`run`](Self::run); `owner` says this future may drive an endpoint that has a relay role. Such an endpoint is
    /// driven by its owner (the future of `Endpoint::run`) only, because the carriers' operations in flight live in the
    /// driving future; an endpoint without a role is driven by whichever future waits.
    #[allow(
        clippy::too_many_lines,
        reason = "one poll function: the registration, the role and the host's I/O share its state"
    )]
    pub(crate) async fn run_as<T>(
        &self,
        owner: bool,
        mut attempt: impl FnMut(&mut Core<H::Keys, H::Access>, u64) -> Try<T>,
    ) -> T {
        #[cfg(feature = "trace")]
        turn_probe::mark_free(self, crate::trace_turn::Kind::Start);
        let mut turn = Turn {
            sh: self,
            ticket: None,
            wait: None,
            driving: false,
            #[cfg(feature = "trace")]
            returned: false,
            #[cfg(feature = "trace")]
            taken: false,
        };
        let mut rx = pin!(None);
        let mut sl = pin!(None);
        let mut slept: Option<u64> = None;
        let mut spare: Option<Buf<'_>> = None;
        let mut carriers = pin!(None);
        let mut role_io = pin!(None);
        loop {
            let step = poll_fn(|cx| {
                let now = self.now();
                let Some(mut core) = self.lock() else {
                    cx.waker().wake_by_ref();
                    return Poll::Pending;
                };
                // What was served, and what a previous call queued (its value returned before the send, pinc#636,
                // pinc#702), is sent before the attempt runs. Not once the endpoint is stopping: an attempt that
                // ends with the endpoint must not wait for the timers to have nothing due (pinc#551, pinc#569).
                let served = self.service(&mut core, now) > 0;
                if !core.stopping() && (served || core.take_dirty()) {
                    #[cfg(feature = "trace")]
                    turn_probe::mark(self, &core, crate::trace_turn::Kind::Io);
                    return Poll::Ready(Step::Io);
                }
                if H::Role::ON && owner && self.role_serve(&mut core, now) {
                    #[cfg(feature = "trace")]
                    turn_probe::mark(self, &core, crate::trace_turn::Kind::Io);
                    return Poll::Ready(Step::Io);
                }
                core.caller = turn.ticket;
                let w = match attempt(&mut core, now) {
                    // A call that took its value out of the endpoint (a read, an accept, an open, a dial) returns it
                    // in this poll, before anything is sent (pinc#636, pinc#702); what the attempt queued leaves with
                    // the next poll of any future, which the kick asks for. Its mark is written by the guard's Drop,
                    // which ends the call in the same step.
                    Try::Taken(v) => {
                        #[cfg(feature = "trace")]
                        core.standby.mark(crate::trace_waits::Mark::Try { key: 0, s: 0 });
                        core.kick();
                        return Poll::Ready(Step::Taken(v));
                    }
                    // A call whose payload is the send (a write, a datagram, a close) sends what the attempt queued
                    // before its value returns, so a host whose last act is the call loses nothing when it drops the
                    // endpoint after.
                    Try::Done(v) => {
                        #[cfg(feature = "trace")]
                        core.standby.mark(crate::trace_waits::Mark::Try { key: 0, s: 0 });
                        core.kick();
                        #[cfg(feature = "trace")]
                        turn_probe::mark(self, &core, crate::trace_turn::Kind::Done);
                        return Poll::Ready(Step::Sent(v));
                    }
                    Try::Wait(w) => w,
                };
                if core.take_dirty() || served {
                    #[cfg(feature = "trace")]
                    turn_probe::mark(self, &core, crate::trace_turn::Kind::Io);
                    return Poll::Ready(Step::Io);
                }
                let t = *turn.ticket.get_or_insert_with(|| core.standby.alloc());
                if let Some(old) = turn.wait.replace(w)
                    && old != w
                {
                    core.forget(old, t);
                }
                core.add_wait(w, t);
                core.standby.arm(t, cx.waker());
                #[cfg(feature = "trace")]
                {
                    let (key, s) = crate::engine::waits_probe::wait_code(&w);
                    core.standby.mark(crate::trace_waits::Mark::Try { key, s });
                }
                if !turn.driving && (owner || !H::Role::ON) && !self.driving.replace(true) {
                    turn.driving = true;
                    core.driver = Some(t);
                }
                if !turn.driving {
                    // The attempt may have added a deadline the driver does not sleep until.
                    #[cfg(feature = "trace")]
                    turn_probe::wait(self, Some(&core), turn.ticket, false, false);
                    core.kick();
                    return Poll::Pending;
                }
                let want = core.deadline();
                core.armed = want.unwrap_or(u64::MAX);
                drop(core);

                let mut progressed = false;
                if want != slept {
                    slept = want;
                    match want {
                        Some(d) => sl.set(Some(sleep_owned(&self.host, self.instant(d)))),
                        None => sl.set(None),
                    }
                }
                if let Some(f) = sl.as_mut().as_pin_mut()
                    && f.poll(cx).is_ready()
                {
                    sl.set(None);
                    slept = None;
                    progressed = true;
                }
                if H::Role::ON {
                    if role_io.is_none() {
                        // Boxed, so the future of an endpoint without a role carries no room for the role's state.
                        role_io.set(Some(Box::pin(self.role_task())));
                    }
                    if let Some(f) = role_io.as_mut().as_pin_mut() {
                        // It never completes: it holds the role's carrier operations in flight and polls them.
                        let _ = f.poll(cx);
                    }
                    progressed |= self.rdirty.take();
                }
                // Read what the host already has before anything is sent: a burst that finds no reader overflows the
                // socket's buffer and the datagrams are lost. A relay role reads once its records are restored.
                let burst = if H::Role::ON && !self.role_ready.get() {
                    0
                } else {
                    DRAIN
                };
                for _ in 0..burst {
                    if rx.is_none() {
                        let b = spare.take().unwrap_or_else(|| self.rx_buf());
                        rx.set(Some(recv_owned(&self.host, b)));
                    }
                    let Some(Poll::Ready((res, mut buf))) = rx.as_mut().as_pin_mut().map(|f| f.poll(cx)) else {
                        break;
                    };
                    rx.set(None);
                    progressed = true;
                    match res {
                        Ok((n, from, segment)) => {
                            #[cfg(feature = "trace")]
                            crate::trace_turn::took();
                            let now = self.now();
                            let from = pinc_connect::client::netcheck::canonical(from);
                            if let Some(mut core) = self.lock() {
                                let batch = buf.v.get_mut(..n).unwrap_or_default();
                                if H::Role::ON {
                                    self.role_datagrams(&mut core, now, from, batch, segment);
                                } else {
                                    core.node.handle_batch(now, self.local, from, batch, segment);
                                }
                            }
                        }
                        Err(e) if e.is_transient() => {}
                        Err(_) => {
                            if let Some(mut core) = self.lock() {
                                core.fail(Error::new(crate::ErrorKind::Unreachable, "the socket failed"));
                            }
                        }
                    }
                    spare = Some(buf);
                }
                // The carriers' task also advances the HTTP exchange of the port-mapping client.
                if !self.relays.is_empty() || self.port_mapping {
                    if carriers.is_none() {
                        carriers.set(Some(self.carriers_task()));
                    }
                    if let Some(f) = carriers.as_mut().as_pin_mut() {
                        // It never completes: it holds the operations in flight and polls them.
                        let _ = f.poll(cx);
                    }
                    progressed |= self.cdirty.take();
                }
                #[cfg(feature = "trace")]
                turn_probe::wait(self, None, turn.ticket, true, progressed);
                if progressed {
                    Poll::Ready(Step::Io)
                } else {
                    Poll::Pending
                }
            })
            .await;
            match step {
                // The value a call took out of the endpoint leaves in the poll that took it, before anything is sent:
                // a future dropped after its attempt finished keeps the result, and what the attempt queued goes with
                // the next poll of any future on the endpoint, which the kick asks for (pinc#636, pinc#702). A call
                // whose payload is the send flushes first, so what it queued leaves with the call that queued it,
                // however quiet the endpoint is after.
                Step::Taken(v) => {
                    #[cfg(feature = "trace")]
                    {
                        turn.taken = true;
                    }
                    return v;
                }
                Step::Sent(v) => {
                    self.flush().await;
                    #[cfg(feature = "trace")]
                    {
                        turn.returned = true;
                    }
                    return v;
                }
                Step::Io => {
                    self.flush().await;
                    #[cfg(feature = "trace")]
                    turn_probe::mark_free(self, crate::trace_turn::Kind::Flush);
                }
            }
        }
    }

    /// Serve the endpoint and send everything it wants to send, until it wants nothing more.
    pub(crate) async fn flush(&self) {
        let mut buf: Option<Buf<'_>> = None;
        loop {
            let (to, len, segment, b) = {
                let now = self.now();
                let Some(mut core) = self.lock() else { return };
                let moved = self.service(&mut core, now);
                let mut b = buf.take().unwrap_or_else(|| self.tx_buf());
                let mut next = core
                    .node
                    .poll_transmit(now, &mut b.v)
                    .map(|t| (t.remote, t.len, t.segment_size))
                    .or_else(|| core.poll_udp(&mut b.v).map(|(to, n)| (to, n, n)));
                if H::Role::ON {
                    if let Some((to, len, segment)) = next
                        && self.role_carries(&mut core, now, &to, b.v.get(..len).unwrap_or_default(), segment)
                    {
                        buf = Some(b);
                        continue;
                    }
                    next = next.or_else(|| self.role_outgoing(&mut core, now, &mut b.v));
                }
                if let Some((to, len, segment)) = next {
                    (to, len, segment, b)
                } else {
                    self.pump_carriers(&mut core, true);
                    core.kick();
                    if moved == 0 {
                        return;
                    }
                    buf = Some(b);
                    continue;
                }
            };
            let to = wire(to, self.local.is_ipv6());
            // A datagram the socket refuses is a lost datagram: the transport sends it again.
            let _ = self.host.send(b.v.get(..len).unwrap_or_default(), to, segment).await;
            buf = Some(b);
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod role_tests;

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]
mod tests {
    use core::convert::Infallible;

    use super::*;
    use crate::endpoint::{Endpoint, Pinc};
    use crate::platform::TestPlatform;

    #[cfg(not(feature = "std"))]
    fn recv_max<H: Hosted>(_: &Endpoint<H>) -> usize {
        H::RECV_MAX
    }

    fn built() -> Endpoint<impl Hosted> {
        Pinc::builder_on(TestPlatform)
            .limits(crate::Limits {
                connections: 4,
                ..crate::Limits::default()
            })
            .build(
                async |_buf: &mut [u8]| -> Result<(usize, SocketAddr), Infallible> { core::future::pending().await },
                async |pkt: &[u8], _to: SocketAddr| -> Result<usize, Infallible> { Ok(pkt.len()) },
                async |_at: u64| {},
            )
            .unwrap()
    }

    /// The endpoints of a thread share the pools with `std`, and each holds its own without.
    #[test]
    fn two_endpoints_of_a_thread_share_their_pools_only_with_std() {
        let (a, b) = (built(), built());
        let (a, b) = (&a.0.shared, &b.0.shared);
        assert_eq!(Rc::ptr_eq(&a.rx_bufs, &b.rx_bufs), cfg!(feature = "std"));
        assert_eq!(Rc::ptr_eq(&a.tx_bufs, &b.tx_bufs), cfg!(feature = "std"));
    }

    /// Without `std` the pools hold their buffers from the build, and a buffer that goes back lands in the same place.
    #[cfg(not(feature = "std"))]
    #[test]
    fn the_pools_of_an_endpoint_hold_their_buffers_from_the_build_and_get_them_back() {
        let ep = built();
        let sh = &ep.0.shared;
        let held = |p: &Pool| p.borrow().iter().map(|b| (b.as_ptr(), b.len())).collect::<Vec<_>>();
        let room = |p: &Pool| p.borrow().capacity();
        let (rx, tx) = (held(&sh.rx_bufs), held(&sh.tx_bufs));
        assert_eq!(rx.len(), 1);
        assert_eq!(tx.len(), 1);
        assert_eq!(rx[0].1, recv_max(&ep));
        assert_eq!(tx[0].1, sh.tx_len);
        let (rx_room, tx_room) = (room(&sh.rx_bufs), room(&sh.tx_bufs));
        assert!(rx_room >= POOLED && tx_room >= POOLED);
        {
            let (r, t) = (sh.rx_buf(), sh.tx_buf());
            assert!(sh.rx_bufs.borrow().is_empty() && sh.tx_bufs.borrow().is_empty());
            drop((r, t));
        }
        assert_eq!((held(&sh.rx_bufs), held(&sh.tx_bufs)), (rx, tx));
        assert_eq!((room(&sh.rx_bufs), room(&sh.tx_bufs)), (rx_room, tx_room));
    }

    use alloc::format;
    use alloc::string::String;
    use core::fmt::Write as _;

    use crate::trace_util::{below, mix, write_trace};

    /// One run of the buffer pools.
    struct BufRun {
        run: usize,
        seed: u64,
        holders: (usize, usize),
        lens: (usize, usize),
        calls: usize,
    }

    /// What the runs together showed.
    #[derive(Default)]
    struct Seen {
        alloc_after_first: bool,
        full_give: bool,
        mixed_len: bool,
    }

    /// The two endpoints' pools, their holders and the lines written so far.
    struct Bufs<'a> {
        p1: &'a Pool,
        p2: &'a Pool,
        held: Vec<Option<Buf<'a>>>,
        h1: usize,
        lens: (usize, usize),
        room: (usize, usize),
        next_tag: u32,
        first: bool,
        head: String,
        out: String,
        seen: Seen,
    }

    fn tag(v: &[u8]) -> u32 {
        u32::from_le_bytes(v[..4].try_into().unwrap())
    }

    fn entries(p: &Pool) -> String {
        let rows: Vec<String> = p.borrow().iter().map(|v| format!("[{},{}]", tag(v), v.len())).collect();
        rows.join(",")
    }

    impl<'a> Bufs<'a> {
        fn endpoint(&self, h: usize) -> (usize, &'a Pool, usize) {
            if h < self.h1 {
                (1, self.p1, self.lens.0)
            } else {
                (2, self.p2, self.lens.1)
            }
        }

        /// The state after a call, with the invariants checked.
        fn state(&self) -> String {
            let std = cfg!(feature = "std");
            let mut tags = Vec::new();
            let mut held = Vec::new();
            for b in &self.held {
                match b {
                    Some(b) => {
                        tags.push(tag(&b.v));
                        held.push(format!("[{},{}]", tag(&b.v), b.v.len()));
                    }
                    None => held.push("[0,0]".into()),
                }
            }
            for (h, b) in self.held.iter().enumerate() {
                if let Some(b) = b {
                    assert_eq!(b.v.len(), self.endpoint(h).2, "a held buffer has its holder's length");
                }
            }
            let pools: Vec<&Pool> = if std { vec![self.p1] } else { vec![self.p1, self.p2] };
            for p in pools {
                assert!(p.borrow().len() <= POOLED);
                tags.extend(p.borrow().iter().map(|v| tag(v)));
            }
            let n = tags.len();
            tags.sort_unstable();
            tags.dedup();
            assert_eq!(tags.len(), n, "a tag is in two places");
            assert!(tags.iter().all(|t| *t != 0));
            let c1 = self.p1.borrow().capacity();
            let (c2, second) = if std {
                (0, String::new())
            } else {
                let c2 = self.p2.borrow().capacity();
                assert_eq!((c1, c2), self.room, "the capacity reserved at the build is kept");
                assert!(c1 >= POOLED && c2 >= POOLED);
                assert!(self.p1.borrow().iter().all(|v| v.len() == self.lens.0));
                assert!(self.p2.borrow().iter().all(|v| v.len() == self.lens.1));
                (c2, entries(self.p2))
            };
            format!(
                r#"{{"pools":[[{}],[{second}]],"cap":[{c1},{c2}],"held":[{}]}}"#,
                entries(self.p1),
                held.join(",")
            )
        }

        fn take(&mut self, h: usize) {
            let (e, pool, len) = self.endpoint(h);
            if cfg!(feature = "std") && pool.borrow().last().is_some_and(|v| v.len() != len) {
                self.seen.mixed_len = true;
            }
            let mut b = pooled(pool, len);
            let got = tag(&b.v);
            if got == 0 {
                self.seen.alloc_after_first |= !self.first;
                b.v[..4].copy_from_slice(&self.next_tag.to_le_bytes());
                self.next_tag += 1;
            }
            self.first = false;
            self.held[h] = Some(b);
            let (head, v) = (&self.head, self.state());
            let _ = writeln!(
                self.out,
                r#"{head},"op":"take","h":{},"e":{e},"len":{len},"got":{got},"v":{v}}}"#,
                h + 1
            );
        }

        fn give(&mut self, h: usize) {
            let (e, pool, _) = self.endpoint(h);
            self.seen.full_give |= pool.borrow().len() == POOLED;
            self.held[h] = None;
            let (head, v) = (&self.head, self.state());
            let _ = writeln!(self.out, r#"{head},"op":"give","h":{},"e":{e},"v":{v}}}"#, h + 1);
        }
    }

    fn bufs_run(r: &BufRun) -> (String, Seen) {
        let std = cfg!(feature = "std");
        let ((h1, h2), (l1, l2)) = (r.holders, r.lens);
        let (p1, p2) = (pools(l1, l1).0, pools(l2, l2).0);
        assert_eq!(Rc::ptr_eq(&p1, &p2), std);
        let mut next_tag = 1;
        if !std {
            p1.borrow_mut()[0][..4].copy_from_slice(&1u32.to_le_bytes());
            p2.borrow_mut()[0][..4].copy_from_slice(&2u32.to_le_bytes());
            next_tag = 3;
        }
        let hs = h1 + h2;
        let mut b = Bufs {
            p1: &p1,
            p2: &p2,
            held: (0..hs).map(|_| None).collect(),
            h1,
            lens: r.lens,
            room: (p1.borrow().capacity(), p2.borrow().capacity()),
            next_tag,
            first: true,
            head: format!(r#"{{"t":"bufs","std":{std},"run":{}"#, r.run),
            out: String::new(),
            seen: Seen::default(),
        };
        let init = format!(
            r#"{},"op":"init","hs":{hs},"h1":{h1},"lens":[{l1},{l2}],"v":{}}}"#,
            b.head,
            b.state()
        );
        b.out.push_str(&init);
        b.out.push('\n');
        let mut s = r.seed;
        for _ in 0..r.calls {
            let free: Vec<usize> = (0..hs).filter(|&h| b.held[h].is_none()).collect();
            let busy: Vec<usize> = (0..hs).filter(|&h| b.held[h].is_some()).collect();
            let pick = mix(&mut s) % 100;
            if pick < 90 {
                let take = (pick < 45 && !free.is_empty()) || busy.is_empty();
                let from = if take { &free } else { &busy };
                let h = from[below(&mut s, from.len())];
                if take { b.take(h) } else { b.give(h) }
            } else if pick < 95 {
                for h in free {
                    b.take(h);
                }
            } else {
                for h in busy {
                    b.give(h);
                }
            }
        }
        (b.out, b.seen)
    }

    /// Takes and gives of buffers on the pools of two endpoints, each run on a thread of its own.
    #[test]
    fn trace_facade_bufs() {
        let mut out = String::new();
        let mut seen = Seen::default();
        let mut run = 0;
        for holders in [(1, 1), (3, 1), (9, 2), (12, 12)] {
            for lens in [(8, 8), (8, 24), (24, 8)] {
                for base in [0x6275_6673u64, 0x6275_6674] {
                    let mut rng = base.wrapping_add(u64::try_from(run).unwrap());
                    let calls = 200 + usize::try_from(mix(&mut rng) % 801).unwrap();
                    let cfg = BufRun {
                        run,
                        seed: rng,
                        holders,
                        lens,
                        calls,
                    };
                    let (lines, got) = std::thread::spawn(move || bufs_run(&cfg)).join().unwrap();
                    out.push_str(&lines);
                    seen.alloc_after_first |= got.alloc_after_first;
                    seen.full_give |= got.full_give;
                    seen.mixed_len |= got.mixed_len;
                    run += 1;
                }
            }
        }
        assert!(seen.alloc_after_first && seen.full_give);
        assert_eq!(seen.mixed_len, cfg!(feature = "std"));
        let name = if cfg!(feature = "std") {
            "facade_bufs_std.ndjson"
        } else {
            "facade_bufs_nostd.ndjson"
        };
        write_trace(name, &out);
    }
}
