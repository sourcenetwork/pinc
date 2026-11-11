//! The driving: how the futures of the facade run the endpoint with the host's three closures, with no task, no channel
//! and no thread of the library's own.
//!
//! Every facade future is one call of [`Shared::run`]. It locks the core, serves what is due, and tries its operation;
//! if the operation must wait it registers a ticket under the thing it waits for and then looks for the driving role:
//! a flag that exactly one waiting future holds. The holder keeps the host's pending receive and sleep
//! futures inside its own state, so a datagram or a deadline wakes the holder's task; it feeds the datagram to the
//! core, which wakes the futures the datagram is for. The role is sticky: the holder keeps it while it waits. When it
//! finishes or is dropped it clears the flag and wakes the oldest waiting future, which takes the role if it still
//! waits. A future that does not hold the role only waits on its ticket; a future that has its result sends what the
//! endpoint wants to send before it returns.
//!
//! Everything runs on the thread that built the endpoint, so the flag is a `Cell` and the core a `RefCell`.
//!
//! Invariants: at most one future holds the role; the flag, the baton and a ticket's registration change in one
//! borrow of the core, so a wake is never lost between a failed attempt and the wait; no borrow is held across an await
//! or a call of a host closure; the
//! receive and transmit buffers come from two small pools and go back when dropped, so steady traffic allocates none,
//! however many futures send at once; with no future polled the endpoint makes no progress, which is the SANS-IO
//! contract.

use std::cell::{Cell, RefCell, RefMut};
use std::future::poll_fn;
use std::io;
use std::net::{IpAddr, SocketAddr};
use std::pin::pin;
use std::rc::Rc;
use std::task::Poll;
use std::time::{Duration, Instant};

use crate::engine::{Core, Try, Wait};
use crate::error::Error;
use crate::host::Hosted;
use crate::standby::Ticket;

/// The first time the endpoint sees, so no time is zero.
pub(crate) const T0: u64 = 10_000_000_000;
/// The largest UDP payload: the most a coalesced receive or a batched transmit holds.
const UDP_MAX: usize = 65_536;
/// The most datagrams read in one burst before the endpoint runs.
const DRAIN: usize = 256;
/// The most buffers each pool keeps.
const POOLED: usize = 8;

/// The state every handle of an endpoint shares.
pub(crate) struct Shared<H: Hosted> {
    pub(crate) host: H,
    start: Instant,
    local: SocketAddr,
    driving: Cell<bool>,
    /// The access hook, the same one the core asks; it holds no endpoint state, so it is asked without the core.
    pub(crate) admit: Rc<crate::engine::Gate<H::Access>>,
    core: RefCell<Core<H::Keys, H::Access>>,
    rx_bufs: RefCell<Vec<Vec<u8>>>,
    tx_bufs: RefCell<Vec<Vec<u8>>>,
    /// The size of a transmit buffer: the endpoint's batch of datagrams of the largest size.
    tx_len: usize,
}

/// A buffer that goes back to its pool when dropped.
struct Buf<'a> {
    v: Vec<u8>,
    home: &'a RefCell<Vec<Vec<u8>>>,
}

impl Drop for Buf<'_> {
    fn drop(&mut self) {
        let v = std::mem::take(&mut self.v);
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
    Done(T),
    Io,
}

/// The errors of a receive that lose one datagram and nothing else.
fn transient(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::Interrupted | io::ErrorKind::ConnectionReset | io::ErrorKind::ConnectionRefused
    )
}

/// The address as the endpoint sees it: a mapped IPv4 address on a dual-stack socket is IPv4.
fn canon(a: SocketAddr) -> SocketAddr {
    SocketAddr::new(a.ip().to_canonical(), a.port())
}

/// The address as the socket takes it.
fn wire(a: SocketAddr, socket_v6: bool) -> SocketAddr {
    match (a.ip(), socket_v6) {
        (IpAddr::V4(v4), true) => SocketAddr::new(v4.to_ipv6_mapped().into(), a.port()),
        _ => a,
    }
}

/// A buffer of `len` bytes from `home`, or a new one.
fn pooled(home: &RefCell<Vec<Vec<u8>>>, len: usize) -> Buf<'_> {
    let v = home.try_borrow_mut().ok().and_then(|mut b| b.pop());
    Buf {
        v: v.unwrap_or_else(|| vec![0; len]),
        home,
    }
}

async fn recv_owned<'a, H: Hosted>(host: &H, mut buf: Buf<'a>) -> (io::Result<(usize, SocketAddr, usize)>, Buf<'a>) {
    let r = host.recv(buf.v.as_mut_slice()).await;
    (r, buf)
}

async fn sleep_owned<H: Hosted>(host: &H, at: Instant) {
    host.sleep(at).await;
}

/// The guard of one operation: what it registered and whether it holds the driving role, undone when it ends.
struct Turn<'a, H: Hosted> {
    sh: &'a Shared<H>,
    ticket: Option<Ticket>,
    wait: Option<Wait>,
    driving: bool,
}

impl<H: Hosted> Drop for Turn<'_, H> {
    fn drop(&mut self) {
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
            core.standby.baton();
        } else if !self.sh.driving.get() {
            // This future may have been the one the baton was offered to: offer it on.
            core.standby.baton();
        }
    }
}

impl<H: Hosted> Shared<H> {
    /// The shared state of an endpoint whose transmits batch up to `gso` datagrams.
    pub(crate) fn new(host: H, core: Core<H::Keys, H::Access>, local: SocketAddr, gso: usize) -> Self {
        Self {
            host,
            start: Instant::now(),
            local,
            driving: Cell::new(false),
            admit: core.hook(),
            core: RefCell::new(core),
            rx_bufs: RefCell::new(Vec::new()),
            tx_bufs: RefCell::new(Vec::new()),
            tx_len: gso.clamp(1, UDP_MAX / vinc_core::MAX_DATAGRAM) * vinc_core::MAX_DATAGRAM,
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

    /// The endpoint's clock: nanoseconds since the endpoint was made, after a fixed offset.
    pub(crate) fn now(&self) -> u64 {
        T0.saturating_add(u64::try_from(self.start.elapsed().as_nanos()).unwrap_or(u64::MAX))
    }

    fn instant(&self, at: u64) -> Instant {
        self.start + Duration::from_nanos(at.saturating_sub(T0))
    }

    fn rx_buf(&self) -> Buf<'_> {
        pooled(&self.rx_bufs, H::RECV_MAX)
    }

    fn tx_buf(&self) -> Buf<'_> {
        pooled(&self.tx_bufs, self.tx_len)
    }

    /// Run `attempt` until it is done. Each time it cannot finish it names what it waits for; the future is woken when
    /// that changes, and meanwhile drives the endpoint if it holds the role. The attempt must be safe to repeat.
    #[allow(
        clippy::too_many_lines,
        reason = "one poll function: the registration, the role and the host's I/O share its state"
    )]
    pub(crate) async fn run<T>(&self, mut attempt: impl FnMut(&mut Core<H::Keys, H::Access>, u64) -> Try<T>) -> T {
        let mut turn = Turn {
            sh: self,
            ticket: None,
            wait: None,
            driving: false,
        };
        let mut rx = pin!(None);
        let mut sl = pin!(None);
        let mut slept: Option<u64> = None;
        let mut spare: Option<Buf<'_>> = None;
        loop {
            let step = poll_fn(|cx| {
                let now = self.now();
                let Some(mut core) = self.lock() else {
                    cx.waker().wake_by_ref();
                    return Poll::Pending;
                };
                if core.service(now) > 0 {
                    return Poll::Ready(Step::Io);
                }
                let w = match attempt(&mut core, now) {
                    Try::Done(v) => {
                        core.kick();
                        return Poll::Ready(Step::Done(v));
                    }
                    Try::Wait(w) => w,
                };
                if core.take_dirty() {
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
                if !turn.driving && !self.driving.replace(true) {
                    turn.driving = true;
                    core.driver = Some(t);
                }
                if !turn.driving {
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
                // Read what the host already has before anything is sent: a burst that finds no reader overflows the
                // socket's buffer and the datagrams are lost.
                for _ in 0..DRAIN {
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
                            let now = self.now();
                            let from = canon(from);
                            if let Some(mut core) = self.lock() {
                                for d in buf.v.get_mut(..n).unwrap_or_default().chunks_mut(segment.max(1)) {
                                    core.node.handle_datagram(now, self.local, from, d);
                                }
                            }
                        }
                        Err(e) if transient(&e) => {}
                        Err(_) => {
                            if let Some(mut core) = self.lock() {
                                core.fail(Error::new(crate::ErrorKind::Unreachable, "the socket failed"));
                            }
                        }
                    }
                    spare = Some(buf);
                }
                if progressed {
                    Poll::Ready(Step::Io)
                } else {
                    Poll::Pending
                }
            })
            .await;
            match step {
                Step::Done(v) => {
                    self.flush().await;
                    return v;
                }
                Step::Io => self.flush().await,
            }
        }
    }

    /// Serve the endpoint and send everything it wants to send, until it wants nothing more.
    pub(crate) async fn flush(&self) {
        let mut buf: Option<Buf<'_>> = None;
        loop {
            let (t, b) = {
                let now = self.now();
                let Some(mut core) = self.lock() else { return };
                let moved = core.service(now);
                let mut b = buf.take().unwrap_or_else(|| self.tx_buf());
                if let Some(t) = core.node.poll_transmit(now, &mut b.v) {
                    (t, b)
                } else {
                    core.kick();
                    if moved == 0 {
                        return;
                    }
                    buf = Some(b);
                    continue;
                }
            };
            let to = wire(t.remote, self.local.is_ipv6());
            // A datagram the socket refuses is a lost datagram: the transport sends it again.
            let _ = self
                .host
                .send(b.v.get(..t.len).unwrap_or_default(), to, t.segment_size)
                .await;
            buf = Some(b);
        }
    }
}
