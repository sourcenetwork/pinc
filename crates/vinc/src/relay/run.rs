//! The loop that runs a relay: one future that works through the completions of the host's carriers and polls its few
//! single operations.
//!
//! There is no task, thread or channel: [`drive`] keeps the host's driving future, the UDP receive and send, the store
//! write and the sleep in its own locals and polls them with the waker of the future that is running it. The streams are
//! not polled: the relay submits an operation and the host reports its completion ([`Carriers`]), so a wake costs
//! O(completions), not O(streams). A completion is handled at once by the synchronous state in `state`.
//!
//! Invariants: no borrow of the state is held across an await; each pass handles at most `BUDGET` completions and then
//! yields, so a busy socket cannot starve the others; the loop touches only the streams on its work lists (an
//! operation to start, a stream to close), never all of them.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::future::poll_fn;
use core::net::SocketAddr;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use vinc_keystore::KeyStore;

use super::carriers::{Carriers, Tag};
use super::io::Hosted;
use super::state::{Core, Job};
use super::store::Store;
use crate::error::Result;

/// The most completions handled in one pass before the loop yields.
const BUDGET: usize = 512;
/// The size of the buffer a datagram is received into.
const DATAGRAM_BUF: usize = 4096;

/// Everything a relay shares between its handles.
pub(crate) struct Inner<H: Hosted, K: KeyStore, St> {
    pub(crate) host: H,
    pub(crate) store: St,
    pub(crate) core: RefCell<Core<H::Stream, K>>,
    pub(crate) stop: Cell<bool>,
    pub(crate) waker: RefCell<Option<Waker>>,
    pub(crate) running: Cell<bool>,
}

async fn recv_owned<H: Hosted>(h: &H, mut buf: Vec<u8>) -> (Result<(usize, SocketAddr)>, Vec<u8>) {
    let r = h.recv(&mut buf).await;
    (r, buf)
}

async fn send_owned<H: Hosted>(h: &H, buf: Vec<u8>, to: SocketAddr) -> (Result<usize>, Vec<u8>) {
    let r = h.send(&buf, to).await;
    (r, buf)
}

async fn keep_owned<St: Store>(st: &St, job: Job) -> Result<()> {
    match job {
        Job::Put(node, rec, received) => st.put(&node, &rec, received).await,
        Job::Remove(node) => st.remove(&node).await,
        Job::Mail(node, packets) => st.put_mailbox(&node, &packets).await,
    }
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
    let streams = h.carriers();
    let kept = inner.store.load().await?;
    inner.core.borrow_mut().restore(h.now(), &kept);
    drop(kept);

    let mut driver = Box::pin(streams.drive());
    let mut recv = None;
    let mut rbuf = Some(alloc::vec![0u8; DATAGRAM_BUF]);
    let mut send = None;
    let mut persist = None;
    let mut sleep: Option<(u64, Pin<Box<_>>)> = None;

    poll_fn(|cx| {
        *inner.waker.borrow_mut() = Some(cx.waker().clone());
        let mut core = inner.core.borrow_mut();
        core.counters.wakes += 1;
        if inner.stop.get() && !core.stopping {
            core.begin_shutdown();
        }
        for _ in 0..BUDGET {
            let now = h.now();
            let mut progressed = false;

            // the host's own work comes first: the operations it finishes show up as completions below
            let _ = driver.as_mut().poll(cx);

            if core.want_accept(now) {
                streams.submit_accept(Tag::new(0));
            }
            let mut handled = 0;
            while handled < BUDGET
                && let Poll::Ready(done) = streams.poll_completed(cx)
            {
                handled += 1;
                progressed = true;
                if let Some((tag, stream)) = core.complete(done, now) {
                    streams.close(tag, stream);
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

            while let Some(slot) = core.pop_submit() {
                if let Some((stream, buf)) = core.take_read(slot) {
                    streams.submit_read(&stream, core.tag(slot), buf);
                    core.counters.stream_ops += 1;
                }
                if let Some((stream, buf, from)) = core.take_write(slot) {
                    streams.submit_write(&stream, core.tag(slot), buf, from);
                    core.counters.stream_ops += 1;
                }
                progressed = true;
            }

            while let Some((i, peer, kind)) = core.next_dial(now) {
                streams.submit_open(Tag::new(i as u64), &peer, kind);
                progressed = true;
            }

            while let Some(slot) = core.pop_reap() {
                let tag = core.tag(slot);
                if let Some(stream) = core.finish(slot, now) {
                    streams.close(tag, stream);
                }
                progressed = true;
            }

            if persist.is_none()
                && let Some(job) = core.next_job()
            {
                persist = Some(Box::pin(keep_owned(&inner.store, job)));
            }
            if let Some(r) = poll_opt(&mut persist, cx) {
                progressed = true;
                if r.is_err() {
                    core.store_failed();
                }
            }

            let mut want = core.next_wake();
            if core.accept_paused(now) {
                want = want.min(core.accept_resume());
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
                if core.stopping && core.idle() {
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
