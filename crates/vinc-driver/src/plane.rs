//! How handles talk to the engine thread: a bounded request queue with replies, an unbounded control queue for
//! fire-and-forget messages, and a wake.
//!
//! A [`Request`] has a reply channel and goes through a bounded queue, so a flood of callers waits instead of growing
//! memory. A [`Ctl`] message never waits and is bounded by what it names (a stream is nudged once until the engine
//! handles it; a session closes once). After either, the engine's loop is woken through [`Wake`], which a driver
//! implements for its own loop (a datagram to its own socket for the reference driver).
//!
//! Invariants: the engine clears the wake flag before it drains the queues, so a message sent after the drain wakes it
//! again; when the last [`Remote`] is dropped the engine is told, and it closes its sessions and stops.

use std::net::SocketAddr;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use kovan_channel::{bounded, unbounded};
use vinc_core::{NodeStats, SessionId, SessionStats};
use vinc_crypto::NodeId;
use vinc_transport::stream::StreamId;

use crate::error::{Error, Result};
use crate::link::{NewStream, SessionShared, StreamShared, chan};

/// How a driver rouses its loop when a message is waiting.
pub trait Wake: Send + Sync + 'static {
    /// Make the loop run once soon. It may be called from any thread and any number of times.
    fn wake(&self);
}

/// A call that has an answer.
pub enum Request {
    /// Dial `node` for `alpn`.
    Connect {
        /// The peer.
        node: NodeId,
        /// The protocol.
        alpn: Vec<u8>,
        /// The addresses to try.
        addrs: Vec<SocketAddr>,
        /// The answer.
        reply: bounded::Sender<Result<Arc<SessionShared>>>,
    },
    /// Open a stream.
    Open {
        /// The session.
        session: SessionId,
        /// Bidirectional or not.
        bidi: bool,
        /// The answer.
        reply: bounded::Sender<Result<NewStream>>,
    },
    /// Send a datagram.
    Datagram {
        /// The session.
        session: SessionId,
        /// The bytes.
        data: Vec<u8>,
        /// The answer.
        reply: bounded::Sender<Result<()>>,
    },
    /// Read the counters of a session.
    Stats {
        /// The session.
        session: SessionId,
        /// The answer.
        reply: bounded::Sender<Result<SessionStats>>,
    },
    /// List the peers with a session.
    Peers {
        /// The answer.
        reply: bounded::Sender<Vec<NodeId>>,
    },
    /// Read the node-wide counters.
    Node {
        /// The answer.
        reply: bounded::Sender<NodeStats>,
    },
    /// Send sessions for `alpn` to their own queue instead of the shared one.
    Listen {
        /// The protocol.
        alpn: Vec<u8>,
        /// The queue, or why not.
        reply: bounded::Sender<Result<bounded::Receiver<Arc<SessionShared>>>>,
    },
    /// Close every session and stop; the reply comes when they are gone.
    Shutdown {
        /// The answer.
        reply: bounded::Sender<()>,
    },
}

/// A message that needs no answer and never waits.
#[derive(Debug)]
pub enum Ctl {
    /// A stream has bytes to send or room to read into.
    Nudge(SessionId, StreamId),
    /// Abandon the send side of a stream.
    Reset(SessionId, StreamId, u64),
    /// Close a session.
    Close(SessionId, u64),
    /// Close every session of a peer.
    ClosePeer(NodeId),
    /// Remember an address for a peer.
    AddAddr(NodeId, SocketAddr),
    /// The network changed: probe the paths again.
    NetworkChange,
    /// The node suspends.
    Suspend,
    /// The node resumes; `true` if its address changed meanwhile.
    Resume(bool),
    /// The last handle is gone.
    Dropped,
}

struct RemoteInner {
    stopped: Arc<AtomicBool>,
    req: bounded::Sender<Request>,
    ctl: unbounded::Sender<Ctl>,
    wake: Arc<dyn Wake>,
}

impl Drop for RemoteInner {
    fn drop(&mut self) {
        self.ctl.send(Ctl::Dropped);
        self.wake.wake();
    }
}

/// A handle to the engine: cheap to clone, usable from any thread. The engine runs while a handle lives.
#[derive(Clone)]
pub struct Remote {
    inner: Arc<RemoteInner>,
}

impl core::fmt::Debug for Remote {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("Remote(..)")
    }
}

/// The engine's side of a [`Remote`].
pub struct Plane {
    pub(crate) stopped: Arc<AtomicBool>,
    pub(crate) req: bounded::Receiver<Request>,
    pub(crate) ctl: unbounded::Receiver<Ctl>,
}

/// A queue pair: the handle side and the engine side. `depth` is the most requests waiting at once.
pub fn plane(depth: usize, wake: Arc<dyn Wake>) -> (Remote, Plane) {
    let (req, req_rx) = chan::<Request>(depth);
    let (ctl, ctl_rx) = unbounded::<Ctl>();
    let stopped = Arc::new(AtomicBool::new(false));
    let inner = Arc::new(RemoteInner {
        stopped: Arc::clone(&stopped),
        req,
        ctl,
        wake,
    });
    (
        Remote { inner },
        Plane {
            stopped,
            req: req_rx,
            ctl: ctl_rx,
        },
    )
}

/// The flag a loop clears before it drains, and a [`Wake`] sets before it rouses the loop: it makes many wakes one.
#[derive(Debug, Default)]
pub struct WakeFlag(AtomicBool);

impl WakeFlag {
    /// Whether a wake is needed now: `true` for the first caller since the last [`clear`](Self::clear).
    pub fn arm(&self) -> bool {
        !self.0.swap(true, Ordering::AcqRel)
    }

    /// Call before draining the queues.
    pub fn clear(&self) {
        self.0.store(false, Ordering::Release);
    }

    /// Forget a wake that could not be delivered, so the next message tries again.
    pub fn disarm(&self) {
        self.clear();
    }
}

/// A handle that does not keep the engine alive.
#[derive(Clone)]
pub struct WeakRemote(std::sync::Weak<RemoteInner>);

impl WeakRemote {
    /// The strong handle, if the engine still has one.
    pub fn upgrade(&self) -> Option<Remote> {
        self.0.upgrade().map(|inner| Remote { inner })
    }
}

impl Remote {
    /// A handle that does not keep the engine alive: a background task that must not hold the endpoint open holds this.
    pub fn downgrade(&self) -> WeakRemote {
        WeakRemote(Arc::downgrade(&self.inner))
    }

    /// Send `make(reply)` and wait for the answer. Dropping the future before the answer arrives leaves the engine
    /// consistent: a request already queued is still handled, and its answer is discarded.
    ///
    /// # Errors
    /// [`Error::shutdown`] if the engine has stopped.
    pub async fn call<T: Send + 'static>(&self, make: impl FnOnce(bounded::Sender<T>) -> Request) -> Result<T> {
        let (tx, rx) = chan::<T>(1);
        if self.inner.stopped.load(Ordering::SeqCst) {
            return Err(Error::shutdown());
        }
        self.inner.req.send_async(make(tx)).await;
        self.inner.wake.wake();
        // The engine sets `stopped` and then answers every request still queued, so a request sent before that is
        // answered and one sent after it is caught here.
        if self.inner.stopped.load(Ordering::SeqCst) {
            return Err(Error::shutdown());
        }
        rx.recv_async().await.ok_or_else(Error::shutdown)
    }

    /// Send a message that needs no answer.
    pub fn ctl(&self, c: Ctl) {
        self.inner.ctl.send(c);
        self.inner.wake.wake();
    }

    /// Tell the engine a stream has bytes to send or room to read into, once until it handles it.
    pub fn nudge(&self, s: &StreamShared) {
        if !s.pump.swap(true, Ordering::AcqRel) {
            self.ctl(Ctl::Nudge(s.session, s.id));
        }
    }
}
