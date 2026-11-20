//! The world of the facade trace tests: two real endpoints over an in-memory wire, a virtual clock they share and a
//! manual executor whose wakers can log which future they wake. Used by `trace_facade_waits` and `trace_facade_stream`.
//!
//! Nothing here runs by itself: a test spawns futures into an [`Exec`], and [`settle`] polls them, delivers the packets
//! and, when nothing else can move, advances the clock to the next timer. The executor never sleeps and never takes a
//! thread, so a run is the same on every machine.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::must_use_candidate,
    clippy::missing_panics_doc,
    dead_code,
    unreachable_pub,
    missing_docs
)]

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::future::{Future, poll_fn};
use std::net::SocketAddr;
use std::pin::Pin;
use std::rc::Rc;
use std::sync::{Arc, Mutex};
use std::task::{Context, Poll, Wake, Waker};

use pinc::{Endpoint, Hosted, Limits, Pinc, Platform};
use pinc_tests::SplitMix64;

/// The subject's address.
pub const SUBJECT: &str = "10.0.0.1:1000";
/// The peer's address.
pub const PEER: &str = "10.0.0.2:1000";
/// Futures of the peer have ids from here; the subject's are below 64.
pub const PEER_BASE: u32 = 1000;

/// A platform on the shared virtual clock: instants are nanoseconds in a `u64`, randomness comes from one generator.
#[derive(Clone)]
pub struct Virt {
    pub now: Rc<Cell<u64>>,
    rng: Rc<RefCell<SplitMix64>>,
}

impl Platform for Virt {
    type Instant = u64;
    type Error = pinc::Error;

    fn now(&self) -> u64 {
        self.now.get()
    }

    fn wall_ns(&self) -> u64 {
        1_700_000_000_000_000_000 + self.now.get()
    }

    fn random(&self, out: &mut [u8]) -> Result<(), pinc::Error> {
        self.rng.borrow_mut().fill(out);
        Ok(())
    }
}

/// The wire: packets sent and not yet delivered, the ones delivered and not yet received, and the waker of each receive
/// that waits.
#[derive(Default)]
struct Net {
    outbox: VecDeque<(SocketAddr, SocketAddr, Vec<u8>)>,
    inbox: HashMap<SocketAddr, VecDeque<(Vec<u8>, SocketAddr)>>,
    rx: HashMap<SocketAddr, Waker>,
    known: HashSet<SocketAddr>,
}

/// The wire, the clock and the timers the endpoints sleep on.
pub struct Wire {
    pub virt: Virt,
    net: Rc<RefCell<Net>>,
    timers: Rc<RefCell<Vec<(u64, Waker)>>>,
}

impl Wire {
    /// A wire whose clock starts at 0 and whose randomness is `rng`.
    pub fn new(rng: SplitMix64) -> Self {
        Self {
            virt: Virt {
                now: Rc::default(),
                rng: Rc::new(RefCell::new(rng)),
            },
            net: Rc::default(),
            timers: Rc::default(),
        }
    }

    /// An endpoint at `addr` from the key seed `[seed; 32]`, serving `alpn`.
    pub fn endpoint(&self, addr: SocketAddr, seed: u8, alpn: &[u8], limits: Limits) -> Endpoint<impl Hosted + use<>> {
        self.net.borrow_mut().known.insert(addr);
        let (net_r, net_s) = (Rc::clone(&self.net), Rc::clone(&self.net));
        let (timers, virt) = (Rc::clone(&self.timers), self.virt.clone());
        Pinc::builder_on(self.virt.clone())
            .seed(&[seed; 32])
            .unwrap()
            .alpn(alpn)
            .local_addr(addr)
            .limits(limits)
            .build(
                async move |buf: &mut [u8]| -> pinc::Result<(usize, SocketAddr)> {
                    poll_fn(|cx| {
                        let mut n = net_r.borrow_mut();
                        if let Some((data, from)) = n.inbox.get_mut(&addr).and_then(VecDeque::pop_front) {
                            assert!(data.len() <= buf.len(), "a packet is longer than the receive buffer");
                            buf[..data.len()].copy_from_slice(&data);
                            Poll::Ready(Ok((data.len(), from)))
                        } else {
                            n.rx.insert(addr, cx.waker().clone());
                            Poll::Pending
                        }
                    })
                    .await
                },
                async move |pkt: &[u8], to: SocketAddr| -> pinc::Result<usize> {
                    net_s.borrow_mut().outbox.push_back((addr, to, pkt.to_vec()));
                    Ok(pkt.len())
                },
                async move |at: u64| {
                    poll_fn(|cx| {
                        if virt.now.get() >= at {
                            Poll::Ready(())
                        } else {
                            timers.borrow_mut().push((at, cx.waker().clone()));
                            Poll::Pending
                        }
                    })
                    .await;
                },
            )
            .unwrap()
    }

    /// Move every packet to its receiver's inbox; the packets and the wakers of the receives that waited for them.
    /// A packet to an address no endpoint has is dropped.
    pub fn deliver(&self) -> (usize, Vec<Waker>) {
        let mut n = self.net.borrow_mut();
        let (mut moved, mut wakers) = (0, Vec::new());
        while let Some((from, to, bytes)) = n.outbox.pop_front() {
            if !n.known.contains(&to) {
                continue;
            }
            moved += 1;
            n.inbox.entry(to).or_default().push_back((bytes, from));
            wakers.extend(n.rx.remove(&to));
        }
        (moved, wakers)
    }

    /// As [`Wire::advance`] for a timer due by `end` only; with none, the clock moves to `end` and the answer is `None`.
    pub fn advance_to(&self, end: u64) -> Option<Vec<Waker>> {
        let first = self.timers.borrow().iter().map(|(at, _)| *at).min();
        if first.is_none_or(|at| at > end) {
            self.virt.now.set(self.virt.now.get().max(end));
            return None;
        }
        self.advance()
    }

    /// Move the clock to the earliest timer and take the wakers of every timer due; `None` when no timer is set.
    pub fn advance(&self) -> Option<Vec<Waker>> {
        let mut t = self.timers.borrow_mut();
        let first = t.iter().map(|(at, _)| *at).min()?;
        self.virt.now.set(self.virt.now.get().max(first));
        let now = self.virt.now.get();
        let (due, rest): (Vec<_>, Vec<_>) = t.drain(..).partition(|(at, _)| *at <= now);
        *t = rest;
        Some(due.into_iter().map(|(_, w)| w).collect())
    }
}

/// The waker of a task: it queues the task once, and tells the probe when `log` is set.
struct W {
    id: u32,
    log: bool,
    ready: Arc<Mutex<VecDeque<u32>>>,
}

impl Wake for W {
    fn wake(self: Arc<Self>) {
        self.wake_by_ref();
    }

    fn wake_by_ref(self: &Arc<Self>) {
        let mut q = self.ready.lock().unwrap();
        if !q.contains(&self.id) {
            q.push_back(self.id);
        }
        if self.log {
            pinc::trace_waits::woke(self.id);
        }
    }
}

struct Task<O> {
    fut: Pin<Box<dyn Future<Output = O>>>,
    waker: Waker,
}

/// What the executor tells a test about.
pub enum Ev<'a, O> {
    /// Task `id` is about to be polled.
    Before(u32),
    /// Task `id` was polled; `Some` is its output if it finished.
    After(u32, Option<&'a O>),
    /// The test is about to wake the wakers of a delivered packet or a timer.
    WakeStart,
    /// It woke them.
    WakeEnd,
}

/// The manual executor: tasks by id, the queue of the ones woken, and the outputs of the ones that finished.
pub struct Exec<O> {
    tasks: BTreeMap<u32, Task<O>>,
    ready: Arc<Mutex<VecDeque<u32>>>,
    pub done: BTreeMap<u32, O>,
}

impl<O> Exec<O> {
    pub fn new() -> Self {
        Self {
            tasks: BTreeMap::new(),
            ready: Arc::default(),
            done: BTreeMap::new(),
        }
    }

    /// Add a task, polled first at the next [`spin`](Self::spin). `log` makes its waker report to the probe.
    pub fn spawn(&mut self, id: u32, log: bool, fut: impl Future<Output = O> + 'static) {
        assert!(
            !self.tasks.contains_key(&id) && !self.done.contains_key(&id),
            "task {id} exists"
        );
        let waker = Waker::from(Arc::new(W {
            id,
            log,
            ready: Arc::clone(&self.ready),
        }));
        self.tasks.insert(
            id,
            Task {
                fut: Box::pin(fut),
                waker,
            },
        );
        self.ready.lock().unwrap().push_back(id);
    }

    /// The ids of the tasks that have not finished, in order.
    pub fn pending(&self) -> Vec<u32> {
        self.tasks.keys().copied().collect()
    }

    /// Drop a task that is still pending; whether there was one.
    pub fn drop_task(&mut self, id: u32) -> bool {
        self.tasks.remove(&id).is_some()
    }

    /// Poll task `id` once if it exists; whether it did.
    pub fn poll_one(&mut self, id: u32, hook: &mut dyn FnMut(Ev<'_, O>)) -> bool {
        let Some(task) = self.tasks.get_mut(&id) else {
            return false;
        };
        hook(Ev::Before(id));
        let mut cx = Context::from_waker(&task.waker);
        match task.fut.as_mut().poll(&mut cx) {
            Poll::Ready(o) => {
                self.tasks.remove(&id);
                hook(Ev::After(id, Some(&o)));
                self.done.insert(id, o);
            }
            Poll::Pending => hook(Ev::After(id, None)),
        }
        true
    }

    /// Poll the woken tasks until none is queued; how many polls.
    pub fn spin(&mut self, hook: &mut dyn FnMut(Ev<'_, O>)) -> usize {
        let mut n = 0;
        loop {
            let next = self.ready.lock().unwrap().pop_front();
            let Some(id) = next else { return n };
            if self.poll_one(id, hook) {
                n += 1;
                assert!(n <= 10_000, "the executor never went quiet");
            }
        }
    }
}

impl<O> Default for Exec<O> {
    fn default() -> Self {
        Self::new()
    }
}

fn wake_all<O>(ws: Vec<Waker>, hook: &mut dyn FnMut(Ev<'_, O>)) {
    if ws.is_empty() {
        return;
    }
    hook(Ev::WakeStart);
    for w in ws {
        w.wake();
    }
    hook(Ev::WakeEnd);
}

/// Poll, deliver and wake until nothing moves.
pub fn settle<O>(w: &Wire, x: &mut Exec<O>, hook: &mut dyn FnMut(Ev<'_, O>)) {
    for _ in 0..1000 {
        let polled = x.spin(hook);
        let (moved, wakers) = w.deliver();
        wake_all(wakers, hook);
        if polled == 0 && moved == 0 {
            return;
        }
    }
    panic!("the world never settled");
}

/// Settle; then, until `cond` holds, move the clock to the next timer and settle again, for at most 30 s of virtual time.
pub fn settle_until<O>(
    w: &Wire,
    x: &mut Exec<O>,
    hook: &mut dyn FnMut(Ev<'_, O>),
    cond: &mut dyn FnMut(&Exec<O>) -> bool,
) {
    let start = w.virt.now.get();
    settle(w, x, hook);
    while !cond(x) {
        assert!(
            w.virt.now.get() - start < 30_000_000_000,
            "the condition did not hold within 30 s"
        );
        let Some(wakers) = w.advance() else {
            panic!("the condition does not hold and no timer is set");
        };
        wake_all(wakers, hook);
        settle(w, x, hook);
    }
}
