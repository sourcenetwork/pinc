//! The baton of the driving role, against the promise of `crates/vinc/src/standby.rs`: "when the future that drives the
//! endpoint ends, [`Standby::baton`] wakes the oldest waiting ticket". A future that reuses the slot of one that ended
//! while still queued inherits that slot's place in the queue, so it is offered the role before a future that has been
//! waiting longer.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::future::Future;
use std::net::SocketAddr;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::task::{Context, Wake, Waker};
use std::time::Instant;

use vinc::Vinc;

/// A waker that counts its wakes.
struct Count(AtomicUsize);

impl Wake for Count {
    fn wake(self: Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
    fn wake_by_ref(self: &Arc<Self>) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }
}

fn counter() -> (Arc<Count>, Waker) {
    let c = Arc::new(Count(AtomicUsize::new(0)));
    (Arc::clone(&c), Waker::from(c))
}

fn wakes(c: &Arc<Count>) -> usize {
    c.0.load(Ordering::SeqCst)
}

/// Poll `f` with `w` until it returns `Pending` (a poll that ends in `Io` loops inside the future).
fn poll_pending<F: Future + ?Sized>(f: Pin<&mut F>, w: &Waker) {
    let mut cx = Context::from_waker(w);
    assert!(f.poll(&mut cx).is_pending(), "an accept with no peer never finishes");
}

/// An endpoint over a host whose socket never delivers and whose clock never fires: only the facade's own wakes happen.
fn quiet() -> vinc::Endpoint<impl vinc::Hosted> {
    Vinc::builder()
        .alpn(b"standby/order".as_slice())
        .local_addr("127.0.0.1:9".parse().unwrap())
        .build(
            async |_buf: &mut [u8]| -> std::io::Result<(usize, SocketAddr)> { std::future::pending().await },
            async |pkt: &[u8], _to: SocketAddr| -> std::io::Result<usize> { Ok(pkt.len()) },
            async |_at: Instant| std::future::pending::<()>().await,
        )
        .unwrap()
}

/// The control: with no slot reused, the baton wakes the future that waited first.
#[test]
fn without_reuse_the_baton_goes_to_the_oldest_waiting_future() {
    let ep = quiet();
    let (_cd, wd) = counter();
    let (cb, wb) = counter();
    let (cc, wc) = counter();
    let mut d = Box::pin(ep.accept());
    poll_pending(d.as_mut(), &wd);
    let mut b = Box::pin(ep.accept());
    poll_pending(b.as_mut(), &wb);
    let mut c = Box::pin(ep.accept());
    poll_pending(c.as_mut(), &wc);
    drop(d);
    assert_eq!((wakes(&cb), wakes(&cc)), (1, 0));
    drop((b, c));
}

#[test]
fn the_baton_goes_to_the_oldest_waiting_future() {
    let ep = quiet();
    let (_cd, wd) = counter();
    let (_cx, wx) = counter();
    let (cb, wb) = counter();
    let (cc, wc) = counter();

    // D waits first and takes the role (slot 0); X waits (slot 1), then B (slot 2). The queue is 0, 1, 2.
    let mut d = Box::pin(ep.accept());
    poll_pending(d.as_mut(), &wd);
    let mut x = Box::pin(ep.accept());
    poll_pending(x.as_mut(), &wx);
    let mut b = Box::pin(ep.accept());
    poll_pending(b.as_mut(), &wb);

    // X ends while D drives: its slot is released but stays queued at position 1.
    drop(x);
    // C starts waiting after B: it reuses slot 1 and its arm does not queue it again.
    let mut c = Box::pin(ep.accept());
    poll_pending(c.as_mut(), &wc);
    assert_eq!((wakes(&cb), wakes(&cc)), (0, 0), "nothing has woken B or C yet");

    // D ends: the baton must offer the role to the oldest waiting future, B, which waited before C.
    drop(d);
    assert_eq!(
        (wakes(&cb), wakes(&cc)),
        (1, 0),
        "the baton woke C (armed after B, in the reused slot of X) instead of B, the oldest waiting ticket"
    );
    drop((b, c));
}
