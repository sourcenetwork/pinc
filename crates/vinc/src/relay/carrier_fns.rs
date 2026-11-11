//! The closure form of the host's carriers: async closures for accept, open, read, write and close.
//!
//! It is the completion contract ([`Carriers`]) built on the closures: the operations the relay submits wait in a queue,
//! and one future ([`Carriers::drive`]) that lives as long as the run holds every operation in flight and polls all of
//! them. That makes it cost a poll per operation in flight at every wake, which is a poll of every idle stream; it suits a
//! host with few carriers, and the tests. A host with many carriers implements [`Carriers`] itself (see its example).
//!
//! Invariants: an operation is polled only after it was submitted; closing a stream drops its operations first, so the
//! stream is the only holder when the close closure gets it.

use alloc::boxed::Box;
use alloc::collections::VecDeque;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;
use core::future::poll_fn;
use core::marker::PhantomData;
use core::pin::Pin;
use core::task::{Context, Poll};

use super::carriers::{Carriers, Completion, Done, Tag};
use super::peers::Peer;
use crate::carrier::CarrierKind;
use crate::error::Result;

enum Req<T> {
    Accept(Tag),
    Open(Tag, Peer, CarrierKind),
    Read(Tag, Rc<T>, Vec<u8>),
    Write(Tag, Rc<T>, Vec<u8>, usize),
    Close(Tag, Rc<T>),
}

/// The host's carriers as async closures, for a stream type `T` of the host's.
pub struct CarrierFns<A, O, Rd, Wr, Cl, T> {
    accept: A,
    open: O,
    read: Rd,
    write: Wr,
    close: Cl,
    reqs: RefCell<VecDeque<Req<T>>>,
    done: RefCell<VecDeque<Completion<T>>>,
    _stream: PhantomData<fn() -> T>,
}

impl<A, O, Rd, Wr, Cl, T> core::fmt::Debug for CarrierFns<A, O, Rd, Wr, Cl, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str("CarrierFns")
    }
}

impl<A, O, Rd, Wr, Cl, T> CarrierFns<A, O, Rd, Wr, Cl, T>
where
    A: AsyncFn() -> Result<(T, CarrierKind)>,
    O: AsyncFn(&Peer, CarrierKind) -> Result<T>,
    Rd: AsyncFn(&T, Vec<u8>) -> (Result<usize>, Vec<u8>),
    Wr: AsyncFn(&T, Vec<u8>, usize) -> (Result<usize>, Vec<u8>),
    Cl: AsyncFn(T),
{
    /// `accept` waits for the next stream; `open(&peer, kind)` opens a stream of `kind` to a peer relay (the TCP
    /// connect, or the HTTP upgrade of a WebSocket, are the host's work; a host that dials no peers passes a closure
    /// that fails); `read(&s, buf)` fills at most `buf.len()` bytes from the start of `buf` and returns the count (zero
    /// when the peer closed; the length of `buf` does not change); `write(&s, buf, from)` writes `buf` from `from` to
    /// its end and returns the count it wrote; `close(s)` ends the stream. Read and write return the buffer.
    ///
    /// The closures are polled together, so every wake costs a poll of each operation in flight; see the module docs.
    pub const fn new(accept: A, open: O, read: Rd, write: Wr, close: Cl) -> Self {
        Self {
            accept,
            open,
            read,
            write,
            close,
            reqs: RefCell::new(VecDeque::new()),
            done: RefCell::new(VecDeque::new()),
            _stream: PhantomData,
        }
    }

    async fn accept_op(&self) -> Result<(T, CarrierKind)> {
        (self.accept)().await
    }

    async fn open_op(&self, peer: Peer, kind: CarrierKind) -> Result<T> {
        (self.open)(&peer, kind).await
    }

    async fn read_op(&self, s: Rc<T>, buf: Vec<u8>) -> (Result<usize>, Vec<u8>) {
        (self.read)(&s, buf).await
    }

    async fn write_op(&self, s: Rc<T>, buf: Vec<u8>, from: usize) -> (Result<usize>, Vec<u8>) {
        (self.write)(&s, buf, from).await
    }

    async fn close_op(&self, s: T) {
        (self.close)(s).await;
    }

    fn finish(&self, tag: Tag, done: Done<T>) {
        self.done.borrow_mut().push_back(Completion { tag, done });
    }

    async fn run(&self) {
        let mut accept = None;
        let mut opens = Vec::new();
        let mut reads = Vec::new();
        let mut writes = Vec::new();
        let mut closes = Vec::new();
        poll_fn(|cx: &mut Context<'_>| -> Poll<()> {
            loop {
                let Some(req) = self.reqs.borrow_mut().pop_front() else {
                    break;
                };
                match req {
                    Req::Accept(tag) => accept = Some((tag, Box::pin(self.accept_op()))),
                    Req::Open(tag, peer, kind) => opens.push((tag, Box::pin(self.open_op(peer, kind)))),
                    Req::Read(tag, s, buf) => reads.push((tag, Box::pin(self.read_op(s, buf)))),
                    Req::Write(tag, s, buf, from) => writes.push((tag, Box::pin(self.write_op(s, buf, from)))),
                    Req::Close(tag, s) => {
                        reads.retain(|(t, _): &(Tag, Pin<Box<_>>)| t.conn() != tag.conn());
                        writes.retain(|(t, _): &(Tag, Pin<Box<_>>)| t.conn() != tag.conn());
                        if let Ok(s) = Rc::try_unwrap(s) {
                            closes.push(Box::pin(self.close_op(s)));
                        }
                    }
                }
            }
            if let Some((tag, f)) = accept.as_mut()
                && let Poll::Ready(r) = f.as_mut().poll(cx)
            {
                let tag = *tag;
                accept = None;
                self.finish(tag, Done::Accepted(r));
            }
            opens.retain_mut(|(tag, f)| match f.as_mut().poll(cx) {
                Poll::Ready(r) => {
                    self.finish(*tag, Done::Opened(r));
                    false
                }
                Poll::Pending => true,
            });
            reads.retain_mut(|(tag, f)| match f.as_mut().poll(cx) {
                Poll::Ready((r, buf)) => {
                    self.finish(*tag, Done::Read(r, buf));
                    false
                }
                Poll::Pending => true,
            });
            writes.retain_mut(|(tag, f)| match f.as_mut().poll(cx) {
                Poll::Ready((r, buf)) => {
                    self.finish(*tag, Done::Written(r, buf));
                    false
                }
                Poll::Pending => true,
            });
            closes.retain_mut(|f| f.as_mut().poll(cx).is_pending());
            Poll::Pending
        })
        .await;
    }
}

impl<A, O, Rd, Wr, Cl, T> Carriers for CarrierFns<A, O, Rd, Wr, Cl, T>
where
    A: AsyncFn() -> Result<(T, CarrierKind)>,
    O: AsyncFn(&Peer, CarrierKind) -> Result<T>,
    Rd: AsyncFn(&T, Vec<u8>) -> (Result<usize>, Vec<u8>),
    Wr: AsyncFn(&T, Vec<u8>, usize) -> (Result<usize>, Vec<u8>),
    Cl: AsyncFn(T),
{
    type Stream = T;

    fn submit_accept(&self, tag: Tag) {
        self.reqs.borrow_mut().push_back(Req::Accept(tag));
    }

    fn submit_open(&self, tag: Tag, peer: &Peer, kind: CarrierKind) {
        self.reqs.borrow_mut().push_back(Req::Open(tag, *peer, kind));
    }

    fn submit_read(&self, stream: &Rc<T>, tag: Tag, buf: Vec<u8>) {
        self.reqs.borrow_mut().push_back(Req::Read(tag, Rc::clone(stream), buf));
    }

    fn submit_write(&self, stream: &Rc<T>, tag: Tag, buf: Vec<u8>, from: usize) {
        self.reqs
            .borrow_mut()
            .push_back(Req::Write(tag, Rc::clone(stream), buf, from));
    }

    fn close(&self, tag: Tag, stream: Rc<T>) {
        self.reqs.borrow_mut().push_back(Req::Close(tag, stream));
    }

    fn poll_completed(&self, _cx: &mut Context<'_>) -> Poll<Completion<T>> {
        // The operations finish inside `drive`, which the relay polls in the same pass, so no waker is kept.
        match self.done.borrow_mut().pop_front() {
            Some(c) => Poll::Ready(c),
            None => Poll::Pending,
        }
    }

    fn drive(&self) -> impl Future<Output = ()> {
        self.run()
    }
}
