//! The driver: the engine as a future the host runs on its own executor.
//!
//! [`open`] gives the handles and a [`Driver`]; the host spawns [`Driver::run`] on the core that owns the socket. One
//! iteration is: clear the wake flag, service the engine to quiescence (requests, events, stream bytes, then every
//! datagram it wants to send), run any timer that is due, then await the first of a datagram, a wake from a handle and
//! the engine's next deadline. With nothing queued the future is parked on that await and costs nothing: no thread, no
//! polling, no busy loop.
//!
//! Invariants: the wake flag is cleared before the queues are drained, so a message queued after the drain wakes the
//! driver again; a timer runs only when its deadline has passed, and the endpoint moves a timer's next deadline strictly
//! into the future, so a timer cannot spin; a send error is a lost datagram (counted), never a stop; a receive error that
//! is not an interrupt or a reset ends the driver and is returned from [`Driver::run`]; dropping the future ends every
//! session, so no handle waits on an engine that is gone.
//!
//! Granularity: a deadline is honoured to the host timer's granularity, never early without a recheck.

use std::future::{Future, poll_fn};
use std::io;
use std::net::{IpAddr, Ipv4Addr, SocketAddr};
use std::pin::pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::task::Poll;

use kovan_channel::bounded::Receiver;
use kovan_channel::unbounded;
use vinc_core::Transmit;
use vinc_crypto::NodeId;
use vinc_keystore::KeyStore;

use crate::engine::{Admit, Engine, EngineConfig};
use crate::error::{Error, ErrorKind, Result};
use crate::io::{Datagrams, Timer};
use crate::keys::Identity;
use crate::link::{SessionShared, chan};
use crate::mem::Limits;
use crate::plane::{Plane, Remote, WakeFlag, plane};
use crate::start::run;

/// The first time the engine sees, so no time is zero.
const T0: u64 = 10_000_000_000;
/// The largest datagram the driver receives.
const RX_BUF: usize = 65_535;
/// The buffer one transmit call fills.
const TX_BUF: usize = 65_536;
/// The most datagrams read in one burst before the engine runs.
const DRAIN: usize = 256;
/// The longest a burst is read before the engine runs: a datagram can cost milliseconds (a handshake in an unoptimized
/// build), and sessions that wait for their acknowledgements through hundreds of them give up on a path that is fine.
const DRAIN_TIME: u64 = 2_000_000;

/// What a driver is built from.
pub struct Settings<S, A> {
    /// The node's identity.
    pub identity: Identity<S>,
    /// The protocols served.
    pub alpns: Vec<Vec<u8>>,
    /// The sizes.
    pub limits: Limits,
    /// The access hook.
    pub admit: A,
    /// The most same-size datagrams one transmit batches before the host splits them (1 turns batching off).
    pub batch: usize,
}

/// Counters of the driver, for tests and monitoring.
#[derive(Debug, Default)]
pub struct LoopStats {
    wakeups: AtomicU64,
    datagrams_in: AtomicU64,
    datagrams_out: AtomicU64,
    timeouts: AtomicU64,
    handle_wakes: AtomicU64,
    send_errors: AtomicU64,
    early: AtomicU64,
    max_late_ns: AtomicU64,
}

/// A reading of [`LoopStats`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopCounts {
    /// Times the wait ended, for any reason.
    pub wakeups: u64,
    /// Datagrams received from the network and handed to the endpoint.
    pub datagrams_in: u64,
    /// Datagrams sent.
    pub datagrams_out: u64,
    /// Times a timer was run.
    pub timeouts: u64,
    /// Wakes from a handle.
    pub handle_wakes: u64,
    /// Datagrams the socket refused.
    pub send_errors: u64,
    /// Times the wait ended on the timer before the deadline it was set for, and the driver waited again.
    pub early: u64,
    /// The most the driver was late to run a timer, in nanoseconds.
    pub max_late_ns: u64,
}

impl LoopStats {
    /// Read the counters.
    pub fn counts(&self) -> LoopCounts {
        let g = |a: &AtomicU64| a.load(Ordering::Relaxed);
        LoopCounts {
            wakeups: g(&self.wakeups),
            datagrams_in: g(&self.datagrams_in),
            datagrams_out: g(&self.datagrams_out),
            timeouts: g(&self.timeouts),
            handle_wakes: g(&self.handle_wakes),
            send_errors: g(&self.send_errors),
            early: g(&self.early),
            max_late_ns: g(&self.max_late_ns),
        }
    }
}

fn bump(a: &AtomicU64, n: u64) {
    a.fetch_add(n, Ordering::Relaxed);
}

/// What the application side of a driver holds.
pub struct Handles {
    /// The handle to the engine.
    pub remote: Remote,
    /// The queue of sessions the peers opened.
    pub incoming: Receiver<Arc<SessionShared>>,
    /// The address the socket is bound to.
    pub local: SocketAddr,
    /// This node's id.
    pub node: NodeId,
    /// The counters of the driver.
    pub stats: Arc<LoopStats>,
}

/// The engine and the host's I/O, ready to run. Spawn [`run`](Self::run) on the executor and core that own the socket.
pub struct Driver<U, T, S, A> {
    udp: U,
    timer: T,
    cfg: EngineConfig<S, A>,
    plane: Plane,
    queue: kovan_channel::bounded::Sender<Arc<SessionShared>>,
    stats: Arc<LoopStats>,
    local: SocketAddr,
}

/// Make the handles and the driver for `settings` over the host's `udp` and `timer`. Nothing runs until the host
/// polls [`Driver::run`].
///
/// # Errors
/// [`ErrorKind::Config`] for a limit or key that is not usable; [`ErrorKind::Unreachable`] if the socket has no address.
pub fn open<U: Datagrams, T: Timer, S: KeyStore, A: Admit>(
    settings: Settings<S, A>,
    udp: U,
    timer: T,
) -> Result<(Handles, Driver<U, T, S, A>)> {
    settings.limits.check()?;
    let local = udp
        .local_addr()
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the bound address is unknown"))?;
    let (remote, plane) = plane(settings.limits.requests);
    let (queue, incoming) = chan::<Arc<SessionShared>>(settings.limits.accept_sessions);
    let node = settings.identity.node_id();
    let stats = Arc::new(LoopStats::default());
    let cfg = EngineConfig {
        identity: settings.identity,
        alpns: settings.alpns,
        limits: settings.limits,
        admit: settings.admit,
        max_gso: settings.batch,
        locals: interfaces(local),
    };
    let handles = Handles {
        remote,
        incoming,
        local,
        node,
        stats: Arc::clone(&stats),
    };
    let driver = Driver {
        udp,
        timer,
        cfg,
        plane,
        queue,
        stats,
        local,
    };
    Ok((handles, driver))
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

/// The errors of a receive that lose one datagram and nothing else.
fn transient(e: &io::Error) -> bool {
    matches!(
        e.kind(),
        io::ErrorKind::Interrupted | io::ErrorKind::ConnectionReset | io::ErrorKind::ConnectionRefused
    )
}

fn socket_error() -> Error {
    Error::new(ErrorKind::Unreachable, "the socket failed")
}

/// The host's I/O and the counters, as the loop uses them.
struct Io<'a, U, T> {
    udp: &'a U,
    timer: &'a T,
    local: SocketAddr,
    stats: &'a LoopStats,
}

impl<U: Datagrams, T: Timer> Io<'_, U, T> {
    fn now(&self) -> u64 {
        T0.saturating_add(self.timer.now())
    }

    async fn send(&self, t: &Transmit, buf: &[u8]) {
        let to = wire(t.remote, self.local.is_ipv6());
        let data = buf.get(..t.len).unwrap_or_default();
        let seg = t.segment_size.max(1);
        match self.udp.send(to, data, seg).await {
            Ok(n) => bump(&self.stats.datagrams_out, n as u64),
            Err(_) => bump(&self.stats.send_errors, data.len().div_ceil(seg) as u64),
        }
    }

    fn ingest<S: KeyStore, A: Admit>(
        &self,
        engine: &mut Engine<'_, '_, S, A>,
        rx: &mut [u8],
        n: usize,
        from: SocketAddr,
    ) {
        bump(&self.stats.datagrams_in, 1);
        let now = self.now();
        if let Some(data) = rx.get_mut(..n) {
            engine.handle_datagram(now, self.local, canon(from), data);
        }
    }

    /// Read what else is already waiting in the socket before the engine sends anything, so a burst does not overflow
    /// the kernel's receive buffer while the driver is busy answering the first datagram.
    fn drain<S: KeyStore, A: Admit>(&self, engine: &mut Engine<'_, '_, S, A>, rx: &mut [u8]) -> Result<()> {
        let start = self.timer.now();
        for _ in 0..DRAIN {
            if self.timer.now().saturating_sub(start) >= DRAIN_TIME {
                break;
            }
            match self.udp.try_recv(rx) {
                Ok(Some((n, from))) => self.ingest(engine, rx, n, from),
                Ok(None) => break,
                Err(e) if transient(&e) => {}
                Err(_) => return Err(socket_error()),
            }
        }
        Ok(())
    }

    /// Send what the endpoint wants to send, handle what that caused, until neither does anything.
    async fn quiesce<S: KeyStore, A: Admit>(&self, engine: &mut Engine<'_, '_, S, A>, tx: &mut [u8]) {
        loop {
            let mut sent = false;
            while let Some(t) = engine.poll_transmit(self.now(), tx) {
                self.send(&t, tx).await;
                sent = true;
            }
            if engine.service(self.now()) == 0 && !sent {
                break;
            }
        }
    }
}

/// What ended one wait.
enum Wait {
    Handle(bool),
    Datagram(io::Result<(usize, SocketAddr)>),
    Timer,
}

impl<U: Datagrams, T: Timer, S: KeyStore, A: Admit> Driver<U, T, S, A> {
    /// Run the endpoint until every handle is dropped and the sessions are closed, a shutdown finished, or the socket
    /// failed. Dropping the future stops the endpoint and ends every session.
    ///
    /// # Errors
    /// [`ErrorKind::Config`] if the limits or keys are not usable; [`ErrorKind::Unreachable`] if the socket failed.
    pub async fn run(self) -> Result<()> {
        let Self {
            udp,
            timer,
            cfg,
            plane,
            queue,
            stats,
            local,
        } = self;
        let (wake, armed) = (plane.wake.clone(), Arc::clone(&plane.armed));
        let io = Io {
            udp: &udp,
            timer: &timer,
            local,
            stats: &stats,
        };
        let now = io.now();
        run(cfg, plane, queue, now, async |engine| {
            event_loop(engine, &io, &wake, &armed).await
        })
        .await?
    }
}

async fn event_loop<U: Datagrams, T: Timer, S: KeyStore, A: Admit>(
    engine: &mut Engine<'_, '_, S, A>,
    io: &Io<'_, U, T>,
    wake: &unbounded::Receiver<()>,
    armed: &WakeFlag,
) -> Result<()> {
    let mut rx = vec![0u8; RX_BUF];
    let mut tx = vec![0u8; TX_BUF];
    let mut signal = pin!(wake.recv_async());
    let mut signal_open = true;
    loop {
        // One receive stays pending across timers and wakes, so no datagram is lost to a dropped receive.
        let (n, from) = {
            let mut recv = pin!(io.udp.recv(&mut rx));
            loop {
                armed.clear();
                io.quiesce(engine, &mut tx).await;
                let now = io.now();
                if engine.finished(now) {
                    return Ok(());
                }
                let deadline = engine.poll_timeout();
                if let Some(d) = deadline.filter(|d| *d <= now) {
                    io.stats.max_late_ns.fetch_max(now - d, Ordering::Relaxed);
                    engine.handle_timeout(now);
                    bump(&io.stats.timeouts, 1);
                    continue;
                }
                let mut sleep = pin!(deadline.map(|d| io.timer.sleep_until(d - T0)));
                let ev = poll_fn(|cx| {
                    if signal_open && let Poll::Ready(m) = signal.as_mut().poll(cx) {
                        return Poll::Ready(Wait::Handle(m.is_some()));
                    }
                    if let Poll::Ready(r) = recv.as_mut().poll(cx) {
                        return Poll::Ready(Wait::Datagram(r));
                    }
                    if let Some(s) = sleep.as_mut().as_pin_mut()
                        && s.poll(cx).is_ready()
                    {
                        return Poll::Ready(Wait::Timer);
                    }
                    Poll::Pending
                })
                .await;
                bump(&io.stats.wakeups, 1);
                match ev {
                    Wait::Handle(open) => {
                        bump(&io.stats.handle_wakes, 1);
                        signal_open = open;
                        if open {
                            signal.set(wake.recv_async());
                        }
                    }
                    Wait::Timer => {
                        if deadline.is_some_and(|d| io.now() < d) {
                            bump(&io.stats.early, 1);
                        }
                    }
                    Wait::Datagram(Ok(got)) => break got,
                    Wait::Datagram(Err(e)) if transient(&e) => break (0, io.local),
                    Wait::Datagram(Err(_)) => return Err(socket_error()),
                }
            }
        };
        if n > 0 {
            io.ingest(engine, &mut rx, n, from);
            io.drain(engine, &mut rx)?;
        }
    }
}
