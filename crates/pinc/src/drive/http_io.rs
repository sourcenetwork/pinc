//! The HTTP exchange of the port-mapping client (`UPnP`), carried over the host's carriers: open a TCP stream to the
//! host that answered the search, write the request, read until it closes, hand the answer back.
//!
//! The exchange is state, not a future: the stream, the request and how much of it is written, the answer read so far,
//! and the phase live in [`Shared`], and whichever call drives the endpoint advances it through the same host
//! operations the carriers use (`open`, `write`, `read`, `close`), recording progress after each completed operation.
//! An operation in flight when the driver changes is started again by the new driver, which is the carriers' contract
//! (a dropped read loses nothing, a write reports how much it took): a host whose operation loses data when dropped
//! breaks it, and the endpoint does not cope with that. A write dropped by a change of driver may have put part of the
//! request out, so, as a carrier's is, that stream is closed and the exchange ends with no answer: the port-mapping
//! client's own retry decides when to ask again.
//!
//! Every stream an exchange opens is given to the host's `close` exactly once, whichever way the exchange ends (its
//! answer, the client giving it up, a dropped write), and a running close finishes before the next exchange opens.
//!
//! Invariants: at most one exchange runs at a time; an answer is read up to [`pinc_portmap::MAX_RESPONSE`] bytes and no
//! further; a stream that fails ends the exchange with no answer.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec;
use alloc::vec::Vec;
use core::future::Future;
use core::task::Context;

use super::carrier_io::Op;
use crate::carrier::CarrierKind;
use crate::carriers::{Carriers, Relay};
use crate::drive::Shared;
use crate::host::Hosted;
use crate::platform::Platform;

/// The answer an exchange ends with: the bytes read, or none when it failed.
type Answer = Option<Vec<u8>>;

/// The longest request the port-mapping client builds.
const MAX_REQUEST: usize = pinc_portmap::upnp::MAX_REQUEST;
/// The bytes one read may take.
const READ_CHUNK: usize = 4096;

// The versions of the host operations of an exchange: a result is taken only by the step that started it.
const OPEN: u64 = 1;
const WRITE: u64 = 2;
const READ: u64 = 3;
const CLOSE: u64 = 4;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    Open,
    Write,
    Read,
    /// The exchange ended; its stream is being closed.
    Close,
}

/// The exchange of an endpoint of host type `H`, boxed in the shared state while one runs.
pub(super) type Held<H> = Option<Box<Exchange<<<H as Hosted>::Carriers as Carriers<<H as Hosted>::Platform>>::Stream>>>;

/// One exchange in progress.
pub(crate) struct Exchange<S> {
    relay: Relay,
    req: Vec<u8>,
    sent: usize,
    answer: Vec<u8>,
    stream: Option<Rc<S>>,
    phase: Phase,
    /// A host operation was started and its result is not recorded yet.
    busy: bool,
    /// The stream to give to the host's `close`, once the exchange ended.
    closing: Option<S>,
    /// How the exchange ended, handed to the client after the stream is closed (none when the client gave up).
    result: Option<Answer>,
}

impl<S> Exchange<S> {
    /// The exchange ends: its stream is to be closed.
    fn start_close(&mut self) {
        self.phase = Phase::Close;
        self.busy = false;
        self.closing = self.stream.take().and_then(|s| Rc::try_unwrap(s).ok());
    }
}

/// What the driver asks of the host.
pub(super) enum Step<S> {
    Open(Relay),
    Write(Rc<S>, Vec<u8>, usize),
    Read(Rc<S>, Vec<u8>),
    Close(S),
}

/// What the host answered.
pub(super) enum Done<S, E> {
    Opened(Result<S, E>),
    Wrote(Result<usize, E>),
    Read(Result<usize, E>, Vec<u8>),
    Closed,
}

/// One host operation.
pub(super) async fn host_step<C: Carriers<Pf>, Pf: Platform>(
    c: &C,
    step: Step<C::Stream>,
) -> Done<C::Stream, Pf::Error> {
    match step {
        Step::Open(r) => Done::Opened(c.open(&r, CarrierKind::Tcp).await),
        Step::Write(s, buf, from) => Done::Wrote(c.write(&s, buf, from).await.0),
        Step::Read(s, buf) => {
            let (r, b) = c.read(&s, buf).await;
            Done::Read(r, b)
        }
        Step::Close(s) => {
            c.close(s).await;
            Done::Closed
        }
    }
}

impl<H: Hosted> Shared<H> {
    /// Advance the HTTP exchange of the port-mapping client: start one when the client has a request, drop one it gave
    /// up on, take the result of the host operation that finished, start the next. Whether anything moved.
    #[allow(
        clippy::too_many_lines,
        reason = "one step of one state machine, a phase after the other"
    )]
    pub(super) fn http_drive<F>(
        &self,
        cx: &mut Context<'_>,
        hop: &mut Op<F>,
        mut make: impl FnMut(Step<<H::Carriers as Carriers<H::Platform>>::Stream>) -> F,
    ) -> bool
    where
        F: Future<Output = Done<<H::Carriers as Carriers<H::Platform>>::Stream, <H::Platform as Platform>::Error>>,
    {
        if !self.port_mapping {
            return false;
        }
        let mut moved = false;
        let awaited = self.lock().is_some_and(|core| core.node.http_awaited());
        let mut slot = self.http.borrow_mut();
        if let Some(ex) = slot.as_mut()
            && ex.phase != Phase::Close
            && !awaited
        {
            // The client gave the exchange up: its stream is closed, and the next request waits for that.
            hop.cancel();
            ex.start_close();
            moved = true;
        }
        if slot.is_none() {
            let mut req = [0u8; MAX_REQUEST];
            let job = self.lock().and_then(|mut core| {
                let me = *core.node.id();
                core.node.poll_http(&mut req).map(|(to, n)| (me, to, n))
            });
            if let Some((me, to, n)) = job {
                hop.cancel();
                *slot = Some(Box::new(Exchange {
                    relay: Relay::new(me).with_tcp(to),
                    req: req.get(..n).unwrap_or_default().to_vec(),
                    sent: 0,
                    answer: Vec::new(),
                    stream: None,
                    phase: Phase::Open,
                    busy: false,
                    closing: None,
                    result: None,
                }));
                moved = true;
            }
        }
        let Some(ex) = slot.as_mut() else {
            return moved;
        };
        let mut finished: Option<Answer> = None;
        let mut done = false;
        match ex.phase {
            Phase::Open if <H::Carriers as Carriers<H::Platform>>::NONE => {
                // No carriers: the exchange fails in this pass, as an open that answers at once would.
                moved = true;
                finished = Some(None);
            }
            Phase::Open => {
                if !hop.running(OPEN) {
                    hop.start(OPEN, make(Step::Open(ex.relay)));
                    ex.busy = true;
                }
                if let Some(Done::Opened(r)) = hop.poll(cx, OPEN) {
                    ex.busy = false;
                    moved = true;
                    match r {
                        Ok(s) => {
                            ex.stream = Some(Rc::new(s));
                            ex.phase = Phase::Write;
                        }
                        Err(_) => finished = Some(None),
                    }
                }
            }
            Phase::Write => {
                if ex.busy && !hop.running(WRITE) {
                    // A write that was in flight was dropped: part of the request may be out. As a carrier's, the stream
                    // is closed and the exchange ends; the client's own retry decides when to ask again.
                    finished = Some(None);
                } else if let Some(s) = ex.stream.clone() {
                    if !hop.running(WRITE) {
                        hop.start(WRITE, make(Step::Write(s, ex.req.clone(), ex.sent)));
                        ex.busy = true;
                    }
                    if let Some(Done::Wrote(r)) = hop.poll(cx, WRITE) {
                        ex.busy = false;
                        moved = true;
                        match r {
                            Ok(n) if n > 0 => {
                                ex.sent = ex.sent.saturating_add(n);
                                if ex.sent >= ex.req.len() {
                                    ex.phase = Phase::Read;
                                }
                            }
                            _ => finished = Some(None),
                        }
                    }
                }
            }
            Phase::Read => {
                if let Some(s) = ex.stream.clone() {
                    if !hop.running(READ) {
                        hop.start(READ, make(Step::Read(s, vec![0u8; READ_CHUNK])));
                        ex.busy = true;
                    }
                    if let Some(Done::Read(r, buf)) = hop.poll(cx, READ) {
                        ex.busy = false;
                        moved = true;
                        match r {
                            Ok(0) => finished = Some(Some(core::mem::take(&mut ex.answer))),
                            Ok(n) => {
                                let room = pinc_portmap::MAX_RESPONSE.saturating_sub(ex.answer.len());
                                ex.answer.extend_from_slice(buf.get(..n.min(room)).unwrap_or_default());
                                if ex.answer.len() >= pinc_portmap::MAX_RESPONSE {
                                    finished = Some(Some(core::mem::take(&mut ex.answer)));
                                }
                            }
                            Err(_) => finished = Some(None),
                        }
                    }
                }
            }
            Phase::Close => {
                if !hop.running(CLOSE) {
                    match ex.closing.take() {
                        Some(s) => hop.start(CLOSE, make(Step::Close(s))),
                        None => done = true,
                    }
                }
                if hop.poll(cx, CLOSE).is_some() {
                    done = true;
                }
            }
        }
        if let Some(answer) = finished {
            hop.cancel();
            ex.result = Some(answer);
            ex.start_close();
            moved = true;
        }
        if done {
            // The stream is closed: now the client hears how the exchange ended, so a client that stops with this
            // exchange is not done before its stream is.
            let result = ex.result.take();
            *slot = None;
            if let Some(answer) = result {
                let now = self.now();
                if let Some(mut core) = self.lock() {
                    core.node.handle_http(now, answer.as_deref());
                }
            }
            moved = true;
        }
        moved
    }
}
