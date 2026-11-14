//! The HTTP exchange of the port-mapping client (`UPnP`), carried over the host's carriers: open a TCP stream to the
//! host that answered the search, write the request, read until it closes, hand the answer back.
//!
//! The exchange is state, not a future: the stream, the request and how much of it is written, the answer read so
//! far, and the phase live in [`Shared`], and whichever call drives the endpoint advances it through the same host
//! operations the carriers use (`open`, `write`, `read`), recording progress after each completed operation. An
//! operation in flight when the driver changes is started again by the new driver, which is the carriers' contract
//! (a dropped read loses nothing, a write reports how much it took): a host whose operation loses data when dropped
//! breaks it, and the endpoint does not cope with that. A dropped write may have put part of the request out, so the
//! exchange then starts over on a new stream.
//!
//! Invariants: at most one exchange runs at a time; an answer is read up to [`vinc_portmap::MAX_RESPONSE`] bytes and no
//! further; a stream that fails ends the exchange with no answer; an exchange is dropped, stream and all, when the
//! port-mapping client no longer awaits it (its deadline passed).

use std::future::Future;
use std::io;
use std::rc::Rc;
use std::task::Context;

use super::carrier_io::Op;
use crate::carrier::CarrierKind;
use crate::carriers::{Carriers, Relay};
use crate::drive::Shared;
use crate::host::Hosted;

/// The longest request the port-mapping client builds.
const MAX_REQUEST: usize = vinc_portmap::upnp::MAX_REQUEST;
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
}

/// The exchange of an endpoint of host type `H`, boxed in the shared state while one runs.
pub(super) type Held<H> = Option<Box<Exchange<<<H as Hosted>::Carriers as Carriers>::Stream>>>;

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
}

/// What the driver asks of the host.
pub(super) enum Step<S> {
    Open(Relay),
    Write(Rc<S>, Vec<u8>, usize),
    Read(Rc<S>, Vec<u8>),
    Close(S),
}

/// What the host answered.
pub(super) enum Done<S> {
    Opened(io::Result<S>),
    Wrote(io::Result<usize>),
    Read(io::Result<usize>, Vec<u8>),
    Closed,
}

/// One host operation.
pub(super) async fn host_step<C: Carriers>(c: &C, step: Step<C::Stream>) -> Done<C::Stream> {
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
        mut make: impl FnMut(Step<<H::Carriers as Carriers>::Stream>) -> F,
    ) -> bool
    where
        F: Future<Output = Done<<H::Carriers as Carriers>::Stream>>,
    {
        if !self.port_mapping {
            return false;
        }
        let mut moved = false;
        let mut slot = self.http.borrow_mut();
        if slot.is_some() && !self.lock().is_some_and(|core| core.node.http_awaited()) {
            // The client gave the exchange up: drop it and its stream, so the next request is polled.
            *slot = None;
            hop.cancel();
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
                }));
                moved = true;
            }
        }
        let Some(ex) = slot.as_mut() else {
            // the stream of an exchange that ended is closed by the same operation slot
            if hop.poll(cx, CLOSE).is_some() {
                moved = true;
            }
            return moved;
        };
        let mut finished: Option<Option<Vec<u8>>> = None;
        match ex.phase {
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
                    // A write that was in flight was dropped: part of the request may be out, so start over.
                    ex.stream = None;
                    ex.sent = 0;
                    ex.phase = Phase::Open;
                    ex.busy = false;
                    moved = true;
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
                            Ok(0) => finished = Some(Some(std::mem::take(&mut ex.answer))),
                            Ok(n) => {
                                let room = vinc_portmap::MAX_RESPONSE.saturating_sub(ex.answer.len());
                                ex.answer.extend_from_slice(buf.get(..n.min(room)).unwrap_or_default());
                                if ex.answer.len() >= vinc_portmap::MAX_RESPONSE {
                                    finished = Some(Some(std::mem::take(&mut ex.answer)));
                                }
                            }
                            Err(_) => finished = Some(None),
                        }
                    }
                }
            }
        }
        if let Some(answer) = finished {
            let stream = ex.stream.take().and_then(|s| Rc::try_unwrap(s).ok());
            *slot = None;
            let now = self.now();
            if let Some(mut core) = self.lock() {
                core.node.handle_http(now, answer.as_deref());
            }
            if let Some(s) = stream {
                hop.start(CLOSE, make(Step::Close(s)));
            }
            moved = true;
        }
        moved
    }
}
