//! The reference loop: the engine on one thread over one `std::net::UdpSocket`.
//!
//! One iteration is: clear the wake flag, service the engine to quiescence (requests, events, stream bytes, then every
//! datagram it wants to send, each segment of a batch as its own datagram because std has no segmentation offload),
//! run any timer that is due, then wait on the socket with a read timeout set to the engine's next deadline. The wait
//! ends for a datagram, for a wake (a one-byte datagram from a private socket, sent when a handle queued a message) or
//! for the deadline. There is no polling and no busy loop: with nothing queued the thread sleeps in the kernel until one
//! of the three happens.
//!
//! Invariants: the wake flag is cleared before the queues are drained, so a message queued after the drain wakes the
//! loop again; a timer is run only when its deadline has passed, and the endpoint moves a timer's next deadline strictly
//! into the future, so a timer cannot spin; a send error is a lost datagram (counted), never a stop; a receive error that
//! is not a timeout, an interrupt or a reset ends the loop and is returned from [`Running::join`].
//!
//! Granularity: a read timeout is rounded up by the operating system to its timer tick, so a deadline can be honoured
//! up to a few milliseconds late, never early.

use std::io;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr, UdpSocket};
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use kovan_channel::bounded::Receiver;
use vinc_core::Transmit;
use vinc_crypto::NodeId;

use crate::engine::{Admit, Engine, EngineConfig};
use crate::error::{Error, ErrorKind, Result};
use crate::keys::Identity;
use crate::link::{SessionShared, chan};
use crate::mem::Limits;
use crate::plane::{Remote, Wake, WakeFlag, plane};
use crate::start::run;

/// The first time the engine sees, so no time is zero.
const T0: u64 = 10_000_000_000;
/// The largest datagram the loop receives.
const RX_BUF: usize = 65_535;
/// The buffer one transmit call fills.
const TX_BUF: usize = 65_536;
/// The most datagrams read in one burst before the engine runs.
const DRAIN: usize = 256;

/// The stack of the driver thread. `run` itself needs only a default stack; this is for the loop that follows: in an
/// unoptimized build, creating a connection builds a value of over a megabyte on the stack several times over, which
/// does not fit the 2 MiB default. An optimized build uses a small part of it; the pages are committed only when used.
const STACK: usize = 8 * 1024 * 1024;

/// What the reference loop is built from.
pub struct Settings {
    /// The address to bind: port 0 picks one.
    pub bind: SocketAddr,
    /// The node's identity.
    pub identity: Identity,
    /// The protocols served.
    pub alpns: Vec<Vec<u8>>,
    /// The sizes.
    pub limits: Limits,
    /// The access hook, if any.
    pub admit: Option<Arc<dyn Admit>>,
    /// The most same-size datagrams one transmit batches before the loop splits them (1 turns batching off).
    pub batch: usize,
}

/// Counters of the loop, for tests and monitoring.
#[derive(Debug, Default)]
pub struct LoopStats {
    wakeups: AtomicU64,
    datagrams_in: AtomicU64,
    datagrams_out: AtomicU64,
    timeouts: AtomicU64,
    wake_datagrams: AtomicU64,
    send_errors: AtomicU64,
    early: AtomicU64,
    max_late_ns: AtomicU64,
}

/// A reading of [`LoopStats`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LoopCounts {
    /// Times the wait on the socket ended, for any reason.
    pub wakeups: u64,
    /// Datagrams received from the network and handed to the endpoint.
    pub datagrams_in: u64,
    /// Datagrams sent.
    pub datagrams_out: u64,
    /// Times a timer was run.
    pub timeouts: u64,
    /// Wakes from a handle.
    pub wake_datagrams: u64,
    /// Datagrams the socket refused.
    pub send_errors: u64,
    /// Times the wait ended on its timeout before the deadline it was set for, and the loop waited again.
    pub early: u64,
    /// The most the loop was late to run a timer, in nanoseconds.
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
            wake_datagrams: g(&self.wake_datagrams),
            send_errors: g(&self.send_errors),
            early: g(&self.early),
            max_late_ns: g(&self.max_late_ns),
        }
    }
}

fn bump(a: &AtomicU64) {
    a.fetch_add(1, Ordering::Relaxed);
}

struct UdpWake {
    flag: Arc<WakeFlag>,
    socket: UdpSocket,
    target: SocketAddr,
}

impl Wake for UdpWake {
    fn wake(&self) {
        if !self.flag.arm() {
            return;
        }
        for _ in 0..8 {
            match self.socket.send_to(&[0], self.target) {
                Ok(_) => return,
                Err(_) => std::thread::yield_now(),
            }
        }
        self.flag.disarm();
    }
}

/// A running reference loop.
pub struct Running {
    remote: Remote,
    incoming: Receiver<Arc<SessionShared>>,
    local: SocketAddr,
    node: NodeId,
    stats: Arc<LoopStats>,
    thread: Option<JoinHandle<io::Result<()>>>,
}

impl Running {
    /// The handle to the engine.
    pub const fn remote(&self) -> &Remote {
        &self.remote
    }

    /// The queue of sessions the peers opened.
    pub const fn incoming(&self) -> &Receiver<Arc<SessionShared>> {
        &self.incoming
    }

    /// The address the socket is bound to.
    pub const fn local_addr(&self) -> SocketAddr {
        self.local
    }

    /// This node's id.
    pub const fn node_id(&self) -> NodeId {
        self.node
    }

    /// The counters of the loop.
    pub fn stats(&self) -> Arc<LoopStats> {
        Arc::clone(&self.stats)
    }

    /// Wait for the loop to stop (after every handle is dropped or a shutdown finished) and return why.
    ///
    /// # Errors
    /// The socket error that ended the loop, if one did.
    pub fn join(mut self) -> io::Result<()> {
        let Some(t) = self.thread.take() else { return Ok(()) };
        // The loop stops when every handle is gone, and this one is the last the driver itself holds.
        drop(self);
        t.join()
            .unwrap_or_else(|_| Err(io::Error::other("the driver thread panicked")))
    }
}

/// Bind the socket, start the loop on its own thread and return the handle once the engine is up.
///
/// # Errors
/// [`ErrorKind::Config`] for a limit or key that is not usable; [`ErrorKind::Unreachable`] if the socket cannot be bound
/// or the thread cannot start.
pub fn start(settings: Settings) -> Result<Running> {
    let socket = UdpSocket::bind(settings.bind)
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the address cannot be bound"))?;
    let local = socket
        .local_addr()
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the bound address is unknown"))?;
    let wake_sock = UdpSocket::bind((loopback(local), 0))
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the wake socket cannot be bound"))?;
    let wake_from = wake_sock
        .local_addr()
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the wake socket is unknown"))?;
    let target = SocketAddr::new(
        if local.ip().is_unspecified() {
            loopback(local)
        } else {
            local.ip()
        },
        local.port(),
    );
    let flag = Arc::new(WakeFlag::default());
    let (remote, plane) = plane(
        settings.limits.requests,
        Arc::new(UdpWake {
            flag: Arc::clone(&flag),
            socket: wake_sock,
            target,
        }),
    );
    let (queue_tx, incoming) = chan::<Arc<SessionShared>>(settings.limits.accept_sessions);
    let node = settings.identity.node_id();
    let stats = Arc::new(LoopStats::default());
    let (ready_tx, ready_rx) = chan::<Result<()>>(1);
    let cfg = EngineConfig {
        identity: settings.identity,
        alpns: settings.alpns,
        limits: settings.limits,
        admit: settings.admit,
        max_gso: settings.batch,
        locals: interfaces(local),
    };
    let ctx = Ctx {
        socket,
        local,
        wake_from,
        flag,
        stats: Arc::clone(&stats),
        clock: Instant::now(),
    };
    let thread = std::thread::Builder::new()
        .name("vinc-driver".into())
        .stack_size(STACK)
        .spawn(move || {
            let up = ready_tx.clone();
            let now = ctx.now();
            match run(cfg, plane, queue_tx, now, |engine| {
                up.send(Ok(()));
                event_loop(engine, &ctx)
            }) {
                Ok(r) => r,
                Err(e) => {
                    ready_tx.send(Err(e));
                    Ok(())
                }
            }
        })
        .map_err(|_| Error::new(ErrorKind::Unreachable, "the driver thread cannot start"))?;
    match ready_rx.recv() {
        Some(Ok(())) => Ok(Running {
            remote,
            incoming,
            local,
            node,
            stats,
            thread: Some(thread),
        }),
        Some(Err(e)) => Err(e),
        None => Err(Error::shutdown()),
    }
}

struct Ctx {
    socket: UdpSocket,
    local: SocketAddr,
    wake_from: SocketAddr,
    flag: Arc<WakeFlag>,
    stats: Arc<LoopStats>,
    clock: Instant,
}

impl Ctx {
    fn now(&self) -> u64 {
        T0.saturating_add(u64::try_from(self.clock.elapsed().as_nanos()).unwrap_or(u64::MAX))
    }
}

const fn loopback(like: SocketAddr) -> IpAddr {
    if like.is_ipv4() {
        IpAddr::V4(Ipv4Addr::LOCALHOST)
    } else {
        IpAddr::V6(Ipv6Addr::LOCALHOST)
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

fn send(ctx: &Ctx, t: &Transmit, buf: &[u8]) {
    let to = wire(t.remote, ctx.local.is_ipv6());
    for seg in buf.get(..t.len).unwrap_or_default().chunks(t.segment_size.max(1)) {
        match ctx.socket.send_to(seg, to) {
            Ok(_) => bump(&ctx.stats.datagrams_out),
            Err(_) => bump(&ctx.stats.send_errors),
        }
    }
}

/// Hand one received datagram to the engine; `false` if it was a wake and not a datagram.
fn ingest(engine: &mut Engine<'_, '_>, ctx: &Ctx, rx: &mut [u8], n: usize, from: SocketAddr) -> bool {
    if from == ctx.wake_from && n == 1 {
        bump(&ctx.stats.wake_datagrams);
        return false;
    }
    bump(&ctx.stats.datagrams_in);
    let now = ctx.now();
    if let Some(data) = rx.get_mut(..n) {
        engine.handle_datagram(now, ctx.local, canon(from), data);
    }
    true
}

/// Read what else is already waiting in the socket before the engine sends anything, so a burst does not overflow the
/// kernel's receive buffer (std cannot enlarge it) while the loop is busy answering the first datagram.
fn drain(engine: &mut Engine<'_, '_>, ctx: &Ctx, rx: &mut [u8]) -> io::Result<()> {
    ctx.socket.set_nonblocking(true)?;
    let mut result = Ok(());
    for _ in 0..DRAIN {
        match ctx.socket.recv_from(rx) {
            Ok((n, from)) => {
                ingest(engine, ctx, rx, n, from);
            }
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => break,
            Err(e)
                if matches!(
                    e.kind(),
                    io::ErrorKind::Interrupted | io::ErrorKind::ConnectionReset | io::ErrorKind::ConnectionRefused
                ) => {}
            Err(e) => {
                result = Err(e);
                break;
            }
        }
    }
    ctx.socket.set_nonblocking(false)?;
    result
}

fn event_loop(engine: &mut Engine<'_, '_>, ctx: &Ctx) -> io::Result<()> {
    let mut rx = vec![0u8; RX_BUF];
    let mut tx = vec![0u8; TX_BUF];
    loop {
        ctx.flag.clear();
        // Quiesce: send what the endpoint wants to send, handle what that caused, until neither does anything.
        loop {
            let mut sent = false;
            while let Some(t) = engine.poll_transmit(ctx.now(), &mut tx) {
                send(ctx, &t, &tx);
                sent = true;
            }
            if engine.service(ctx.now()) == 0 && !sent {
                break;
            }
        }
        let now = ctx.now();
        if engine.finished(now) {
            return Ok(());
        }
        let deadline = engine.poll_timeout();
        if let Some(d) = deadline.filter(|d| *d <= now) {
            ctx.stats.max_late_ns.fetch_max(now - d, Ordering::Relaxed);
            engine.handle_timeout(now);
            bump(&ctx.stats.timeouts);
            continue;
        }
        let wait = deadline.map(|d| Duration::from_nanos(d - now));
        ctx.socket.set_read_timeout(wait)?;
        match ctx.socket.recv_from(&mut rx) {
            Ok((n, from)) => {
                bump(&ctx.stats.wakeups);
                if !ingest(engine, ctx, &mut rx, n, from) {
                    continue;
                }
                drain(engine, ctx, &mut rx)?;
            }
            Err(e) => match e.kind() {
                io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => {
                    bump(&ctx.stats.wakeups);
                    if deadline.is_some_and(|d| ctx.now() < d) {
                        bump(&ctx.stats.early);
                    }
                }
                io::ErrorKind::Interrupted | io::ErrorKind::ConnectionReset | io::ErrorKind::ConnectionRefused => {}
                _ => return Err(e),
            },
        }
    }
}
