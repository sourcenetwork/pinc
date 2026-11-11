//! The loop that runs a relay: one future that polls every pending operation of the host's closures.
//!
//! There is no task, thread or channel: [`drive`] keeps the in-flight accept, UDP receive, UDP send, stream reads and
//! writes, closes, store write and sleep in its own locals and polls them all with the waker of the future that is
//! running it. A completed operation is handled at once by the synchronous state in `core`.
//!
//! Invariants: no borrow of the state is held across an await; each pass handles at most `BUDGET` completions and then
//! yields, so a busy socket cannot starve the others; dropping the future drops every operation and stream, which is
//! safe at any await because each operation owns its buffers.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::future::poll_fn;
use core::net::SocketAddr;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use vinc_crypto::NodeId;
use vinc_keystore::KeyStore;

use super::io::Hosted;
use super::state::Core;
use super::store::Store;
use crate::error::Result;

/// The most completions handled in one pass before the loop yields.
const BUDGET: usize = 512;
/// The size of the buffer a datagram is received into.
const DATAGRAM_BUF: usize = 4096;
/// How long accepting pauses after a failed accept, in nanoseconds.
const ACCEPT_PAUSE_NS: u64 = 100_000_000;

/// Everything a relay shares between its handles.
pub(crate) struct Inner<H: Hosted, K: KeyStore, St> {
    pub(crate) host: H,
    pub(crate) store: St,
    pub(crate) core: RefCell<Core<H::Stream, K>>,
    pub(crate) stop: Cell<bool>,
    pub(crate) waker: RefCell<Option<Waker>>,
    pub(crate) running: Cell<bool>,
}

struct Done {
    r: Result<usize>,
    buf: Vec<u8>,
}

struct Ops<R, W> {
    read: Option<Pin<Box<R>>>,
    write: Option<Pin<Box<W>>>,
}

impl<R, W> Default for Ops<R, W> {
    fn default() -> Self {
        Self {
            read: None,
            write: None,
        }
    }
}

async fn read_owned<H: Hosted>(h: &H, s: Rc<H::Stream>, buf: Vec<u8>) -> Done {
    let (r, buf) = h.read(&s, buf).await;
    Done { r, buf }
}

async fn write_owned<H: Hosted>(h: &H, s: Rc<H::Stream>, buf: Vec<u8>, from: usize) -> Done {
    let (r, buf) = h.write(&s, buf, from).await;
    Done { r, buf }
}

async fn recv_owned<H: Hosted>(h: &H, mut buf: Vec<u8>) -> (Result<(usize, SocketAddr)>, Vec<u8>) {
    let r = h.recv(&mut buf).await;
    (r, buf)
}

async fn send_owned<H: Hosted>(h: &H, buf: Vec<u8>, to: SocketAddr) -> (Result<usize>, Vec<u8>) {
    let r = h.send(&buf, to).await;
    (r, buf)
}

async fn close_owned<H: Hosted>(h: &H, s: H::Stream) {
    h.close(s).await;
}

async fn put_owned<St: Store>(st: &St, node: NodeId, rec: Vec<u8>) -> Result<()> {
    st.put(&node, &rec).await
}

fn poll_opt<F: Future>(slot: &mut Option<Pin<Box<F>>>, cx: &mut Context<'_>) -> Option<F::Output> {
    let f = slot.as_mut()?;
    match f.as_mut().poll(cx) {
        Poll::Ready(v) => {
            *slot = None;
            Some(v)
        }
        Poll::Pending => None,
    }
}

/// Poll the read and the write of one stream; whether either finished.
fn poll_conn<S, K, R, W>(
    core: &mut Core<S, K>,
    ops: &mut Ops<R, W>,
    slot: usize,
    cx: &mut Context<'_>,
    now: u64,
    mk_r: &impl Fn(Rc<S>, Vec<u8>) -> R,
    mk_w: &impl Fn(Rc<S>, Vec<u8>, usize) -> W,
) -> bool
where
    K: KeyStore,
    R: Future<Output = Done>,
    W: Future<Output = Done>,
{
    let mut progressed = false;
    if ops.read.is_none()
        && let Some((s, buf)) = core.take_read(slot)
    {
        ops.read = Some(Box::pin(mk_r(s, buf)));
    }
    if let Some(d) = poll_opt(&mut ops.read, cx) {
        core.on_read(slot, now, d.r, d.buf);
        progressed = true;
    }
    if ops.write.is_none()
        && let Some((s, buf, from)) = core.take_write(slot)
    {
        ops.write = Some(Box::pin(mk_w(s, buf, from)));
    }
    if let Some(d) = poll_opt(&mut ops.write, cx) {
        core.on_write(slot, d.r, d.buf);
        progressed = true;
    }
    progressed
}

// vertexia: every pending operation is polled on every wake, O(streams) per wake; per-operation wakers would need `Arc`
// or `unsafe`, so the upgrade is a readiness source the host passes (one wake per ready stream)
/// Run the relay until it is stopped.
#[allow(
    clippy::too_many_lines,
    reason = "one poll function: the pending operations share its locals"
)]
pub(crate) async fn drive<H, K, St>(inner: &Inner<H, K, St>) -> Result<()>
where
    H: Hosted,
    K: KeyStore,
    St: Store,
{
    let h = &inner.host;
    let records = inner.store.load().await?;
    inner.core.borrow_mut().restore(h.now(), &records);
    drop(records);

    let mk_r = |s: Rc<H::Stream>, b: Vec<u8>| read_owned(h, s, b);
    let mk_w = |s: Rc<H::Stream>, b: Vec<u8>, from: usize| write_owned(h, s, b, from);
    let mut ops: Vec<Ops<_, _>> = Vec::new();
    let mut accept = None;
    let mut accept_pause = 0u64;
    let mut recv = None;
    let mut rbuf = Some(alloc::vec![0u8; DATAGRAM_BUF]);
    let mut send = None;
    let mut closes = Vec::new();
    let mut persist = None;
    let mut sleep: Option<(u64, Pin<Box<_>>)> = None;

    poll_fn(|cx| {
        *inner.waker.borrow_mut() = Some(cx.waker().clone());
        let mut core = inner.core.borrow_mut();
        if inner.stop.get() && !core.stopping {
            core.begin_shutdown();
        }
        for _ in 0..BUDGET {
            let now = h.now();
            let mut progressed = false;

            if accept.is_none() && !core.stopping && now >= accept_pause {
                accept = Some(Box::pin(h.accept()));
            }
            if let Some(r) = poll_opt(&mut accept, cx) {
                progressed = true;
                if let Ok((s, kind)) = r {
                    if let Err(s) = core.add_conn(s, kind, now) {
                        closes.push(Box::pin(close_owned(h, s)));
                    }
                } else {
                    core.accept_failed();
                    accept_pause = now.saturating_add(ACCEPT_PAUSE_NS);
                }
            }

            if recv.is_none()
                && let Some(b) = rbuf.take()
            {
                recv = Some(Box::pin(recv_owned(h, b)));
            }
            if let Some((r, b)) = poll_opt(&mut recv, cx) {
                progressed = true;
                let mut b = b;
                if let Ok((n, from)) = r {
                    core.on_datagram(now, from, b.get_mut(..n).unwrap_or_default());
                }
                rbuf = Some(b);
            }

            if send.is_none()
                && let Some((to, buf)) = core.take_udp()
            {
                send = Some(Box::pin(send_owned(h, buf, to)));
            }
            if let Some((r, buf)) = poll_opt(&mut send, cx) {
                progressed = true;
                core.udp_sent(r.is_ok(), buf);
            }

            ops.resize_with(core.conns.len(), Ops::default);
            for slot in 0..ops.len() {
                if let Some(o) = ops.get_mut(slot) {
                    progressed |= poll_conn(&mut *core, o, slot, cx, now, &mk_r, &mk_w);
                }
            }

            let dead: Vec<usize> = core.dying_slots().collect();
            for slot in dead {
                if let Some(o) = ops.get_mut(slot) {
                    *o = Ops::default();
                }
                if let Some(rc) = core.finish(slot, now)
                    && let Ok(s) = Rc::try_unwrap(rc)
                {
                    closes.push(Box::pin(close_owned(h, s)));
                }
                progressed = true;
            }
            let before = closes.len();
            closes.retain_mut(|f| f.as_mut().poll(cx).is_pending());
            progressed |= closes.len() != before;

            if persist.is_none()
                && let Some(node) = core.persist.pop()
                && let Some(rec) = core.record(now, &node)
            {
                persist = Some(Box::pin(put_owned(&inner.store, node, rec)));
            }
            if let Some(r) = poll_opt(&mut persist, cx) {
                progressed = true;
                if r.is_err() {
                    core.store_failed();
                }
            }

            let mut want = core.next_wake();
            if accept.is_none() && !core.stopping && accept_pause > now {
                want = want.min(accept_pause);
            }
            if want <= now {
                core.on_timeout(now);
                sleep = None;
                progressed = true;
            } else {
                if sleep.as_ref().map(|s| s.0) != Some(want) {
                    sleep = Some((want, Box::pin(h.sleep(want))));
                }
                if let Some((_, f)) = sleep.as_mut()
                    && f.as_mut().poll(cx).is_ready()
                {
                    sleep = None;
                    core.on_timeout(now);
                    progressed = true;
                }
            }

            if !progressed {
                if core.stopping && core.idle() && closes.is_empty() {
                    return Poll::Ready(Ok(()));
                }
                return Poll::Pending;
            }
        }
        cx.waker().wake_by_ref();
        Poll::Pending
    })
    .await
}
