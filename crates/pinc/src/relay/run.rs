//! The loop that runs a relay alone: a thin loop over the [`Part`] with the host's UDP socket and clock and the relay's
//! own hub endpoint.
//!
//! There is no task, thread or channel: [`drive`] keeps the host's driving future, the UDP receive and send, the store
//! write and the sleep in its own locals and polls them with the waker of the future that is running it. The streams are
//! not polled: the part submits an operation and the host reports its completion ([`Carriers`](super::Carriers)), so a
//! wake costs O(completions), not O(streams). An embedder with its own endpoint, socket and timer does not use this
//! loop; it makes the same calls itself on the part.
//!
//! Invariants: no borrow of the part is held across an await; each pass handles at most `BUDGET` completions and then
//! yields, so a busy socket cannot starve the others.

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::future::poll_fn;
use core::net::SocketAddr;
use core::pin::Pin;
use core::task::{Context, Poll, Waker};

use pinc_core::Ledger;
use pinc_keystore::KeyStore;

use super::access::Access;
use super::hub::Hub;
use super::io::Hosted;
use super::part::Part;
use super::store::Store;
use crate::drive::wire;
use crate::error::Result;

/// The most passes one wake makes before the loop yields.
const BUDGET: usize = 512;
/// The size of the buffer a datagram is received into.
const DATAGRAM_BUF: usize = 4096;

/// Everything a relay shares between its handles.
pub(crate) struct Inner<H: Hosted, K: KeyStore, St: Store, A: Access> {
    pub(crate) host: H,
    pub(crate) part: RefCell<Part<H::Streams, K, St, A>>,
    pub(crate) hub: RefCell<Option<Hub>>,
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

/// The ledger every uncharged datagram of the relay passes: the hub endpoint's (fixed at build), or one the loop keeps
/// when the relay has no hub. A datagram the hub endpoint built is charged by its own gate and is never charged here.
enum Gate {
    Hub,
    Own(Box<Ledger>),
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

/// Whether the socket is IPv6: a dual-stack one hands IPv4 senders over in mapped form and takes that form back.
// vertexia: the family is learned from the first datagram received, so a send before any receive on a dual-stack
// socket outside Linux goes out unmapped; pass the family at `relay::Udp::new` to know it from the start
#[derive(Default)]
struct Family(bool);

impl Family {
    fn heard(&mut self, from: SocketAddr) {
        self.0 |= from.is_ipv6();
    }

    fn wire(&self, to: SocketAddr) -> SocketAddr {
        wire(to, self.0)
    }
}

/// Run the relay until it is stopped.
#[allow(
    clippy::too_many_lines,
    reason = "one poll function: the pending operations share its locals"
)]
pub(crate) async fn drive<H, K, St, A>(inner: &Inner<H, K, St, A>) -> Result<()>
where
    H: Hosted,
    K: KeyStore,
    St: Store,
    A: Access,
{
    let h = &inner.host;
    // a run after a run: the machine holds what the store kept, and the writes still owed are queued
    if !inner.part.borrow().restored() {
        let load = inner.part.borrow().load();
        let kept = load.await?;
        inner.part.borrow_mut().restore(h.now(), &kept);
    }

    // vertexia: the table is about 60 KB, built only on a relay without a hub, and empty after a restart (every address
    // is held afresh); a hub endpoint's ledger replaces it when the relay has one.
    let mut gate = if inner.hub.borrow().is_none() {
        let seed = inner.part.borrow_mut().core.ledger_seed()?;
        Gate::Own(Box::new(Ledger::new(seed)))
    } else {
        Gate::Hub
    };
    let mut driver = Box::pin(inner.part.borrow().drive());
    let mut recv = None;
    let mut rbuf = Some(alloc::vec![0u8; DATAGRAM_BUF]);
    let mut send = None;
    let mut persist: Option<Pin<Box<_>>> = None;
    let mut sleep: Option<(u64, Pin<Box<_>>)> = None;
    let mut family = Family::default();

    poll_fn(|cx| {
        *inner.waker.borrow_mut() = Some(cx.waker().clone());
        let mut part = inner.part.borrow_mut();
        let mut hub = inner.hub.borrow_mut();
        part.core.counters.wakes += 1;
        if inner.stop.get() && !part.core.stopping {
            part.stop();
        }
        for _ in 0..BUDGET {
            let now = h.now();
            let mut progressed = false;

            // the host's own work comes first: the operations it finishes show up as completions below
            let _ = driver.as_mut().poll(cx);
            progressed |= part.poll(cx, now);

            if recv.is_none()
                && let Some(b) = rbuf.take()
            {
                recv = Some(Box::pin(recv_owned(h, b)));
            }
            if let Some((r, b)) = poll_opt(&mut recv, cx) {
                progressed = true;
                let mut b = b;
                if let Ok((n, from)) = r {
                    family.heard(from);
                    let from = pinc_connect::client::netcheck::canonical(from);
                    let dgram = b.get_mut(..n).unwrap_or_default();
                    if let Some(hub) = hub.as_mut() {
                        if part.datagram(hub.ep(), now, from, dgram) {
                            // The relay's own datagram counts as received from its source in the hub endpoint's
                            // ledger, so the answer to it is held to three times what it sent.
                            hub.ep_mut().host_received(now, from, n);
                        } else {
                            hub.handle_datagram(now, from, dgram);
                            part.after_datagram(hub.ep(), now, from);
                        }
                    } else {
                        if let Gate::Own(own) = &mut gate {
                            own.on_receive(from, n as u64);
                        }
                        part.core.on_datagram(now, from, None, dgram);
                    }
                }
                rbuf = Some(b);
            }

            if let Some(hub) = hub.as_mut() {
                hub.cycle(&mut part, now);
            }

            // Every datagram the relay sends passes the ledger of the endpoint that owns the address: the hub
            // endpoint's, or the loop's own when the relay has no hub.
            let next = match (send.is_some(), &mut gate) {
                (true, _) => None,
                (false, Gate::Own(own)) => part.core.take_udp(|to, n| own.allow_send(to, n as u64)),
                (false, Gate::Hub) => hub
                    .as_mut()
                    .and_then(|hub| part.core.take_udp(|to, n| hub.ep_mut().host_send(now, to, n))),
            };
            if let Some((to, buf)) = next {
                send = Some(Box::pin(send_owned(h, buf, family.wire(to))));
            }
            if let Some((r, buf)) = poll_opt(&mut send, cx) {
                progressed = true;
                part.core.udp_sent(r.is_ok(), buf);
            }

            if persist.is_none()
                && let Some(w) = part.next_store_write()
            {
                persist = Some(Box::pin(w.run()));
            }
            if let Some(r) = poll_opt(&mut persist, cx) {
                progressed = true;
                part.store_written(r.is_ok());
            }

            let mut want = part.next_deadline(now).unwrap_or(u64::MAX);
            if let Some(t) = hub.as_ref().and_then(Hub::next_timeout) {
                want = want.min(t);
            }
            if want <= now {
                part.handle_timeout(now);
                if let Some(hub) = hub.as_mut() {
                    hub.handle_timeout(now);
                    hub.cycle(&mut part, now);
                }
                sleep = None;
                progressed = true;
            } else if want != u64::MAX {
                if sleep.as_ref().map(|s| s.0) != Some(want) {
                    sleep = Some((want, Box::pin(h.sleep(want))));
                }
                if let Some((_, f)) = sleep.as_mut()
                    && f.as_mut().poll(cx).is_ready()
                {
                    sleep = None;
                    part.handle_timeout(now);
                    if let Some(hub) = hub.as_mut() {
                        hub.handle_timeout(now);
                        hub.cycle(&mut part, now);
                    }
                    progressed = true;
                }
            }

            if !progressed {
                if part.is_stopped() {
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

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// After a mapped IPv4 source was received an IPv4 destination goes out mapped; before any receive it goes as given.
    #[test]
    fn an_ipv4_destination_is_mapped_once_an_ipv6_source_was_heard() {
        let v4: SocketAddr = "192.0.2.7:9".parse().unwrap();
        let mut f = Family::default();
        assert_eq!(f.wire(v4), v4);
        f.heard("[::ffff:192.0.2.1]:5".parse().unwrap());
        assert_eq!(f.wire(v4), "[::ffff:192.0.2.7]:9".parse::<SocketAddr>().unwrap());
    }
}
