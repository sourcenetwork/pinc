//! The relay carriers on the driving future: one slot per relay, and the future that opens, reads, writes and closes
//! them with the host's closures.
//!
//! The state of a carrier (its stream, the bytes read and not yet taken by the node, the bytes the node wants written)
//! lives in the shared state, so it survives a change of the driving future. The operations in flight (an open, a read,
//! a write, a close) live in [`Shared::carriers_task`], which the driving future polls: a new driver starts them again
//! from the state. A read that is dropped loses no byte (the host's contract); a write that is dropped may have sent
//! part of its buffer, so the new driver closes that carrier and the connectivity layer opens it again.
//!
//! Invariants: no borrow is held across a call of a host closure; every buffer is allocated when a carrier opens and
//! reused after; the bytes waiting to be written are bounded by [`OUT_CAP`].

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::future::{Future, poll_fn};
use core::pin::Pin;
use core::task::{Context, Poll};

use pinc_connect::carrier::ws::{self, Decoder, Opcode, Role as WsRole, WsFrame};
use pinc_connect::client::Io as CarrierIo;
use pinc_connect::client::Kind;

use super::{Shared, http_io};
use crate::carrier::CarrierKind;
use crate::carriers::{Carriers, Relay};
use crate::engine::Core;
use crate::host::Hosted;
use crate::node::RELAYS;
use crate::platform::Platform;

/// The most bytes the node may have queued for one carrier that the host has not yet taken.
pub(crate) const OUT_CAP: usize = 256 * 1024;

/// Take the bytes the node has for one carrier into `out`, until `out` holds [`OUT_CAP`] or the node has none. `next`
/// fills a buffer and returns how many bytes it gave and, for a WebSocket carrier (`framed`), the mask of their
/// frame. A framed take is at most one frame's payload, so everything the node gives is framed; false if a frame
/// could not be encoded all the same, with `out` left as it was before that take.
fn take_out(
    out: &mut Vec<u8>,
    scratch: &mut [u8],
    framed: bool,
    mut next: impl FnMut(&mut [u8]) -> (usize, [u8; 4]),
) -> bool {
    let room = if framed {
        scratch.len().min(ws::MAX_PAYLOAD)
    } else {
        scratch.len()
    };
    let Some(buf) = scratch.get_mut(..room) else {
        return true;
    };
    while out.len() < OUT_CAP {
        let (n, mask) = next(buf);
        let Some(chunk) = buf.get(..n).filter(|c| !c.is_empty()) else {
            return true;
        };
        if framed {
            let at = out.len();
            out.resize(at + n + ws::MAX_HEADER, 0);
            let used = out
                .get_mut(at..)
                .and_then(|o| ws::encode(Opcode::Binary, chunk, Some(mask), o).ok());
            out.truncate(at + used.unwrap_or(0));
            if used.is_none() {
                return false;
            }
        } else {
            out.extend_from_slice(chunk);
        }
    }
    true
}
/// The size of a read.
const READ_BUF: usize = 16 * 1024;
/// The most bytes of the stream read ahead of the node, and of undecoded WebSocket frames. A ping of two bytes is
/// answered with six, so the answers waiting to be written stay under `OUT_CAP + 3 * IN_CAP` (plus the answers in the
/// one write in flight, under the same bound): reading stops once the answers waiting pass `OUT_CAP`, and one read of
/// pings adds at most three times what it read. The node's own outgoing bytes do not count: they never stop a read.
const IN_CAP: usize = 64 * 1024;

/// Where a carrier is.
pub(crate) enum State<S> {
    /// No carrier, none wanted.
    Idle,
    /// The node asked for one and the host is opening it.
    Opening(CarrierKind),
    /// Open.
    Open(Rc<S>, CarrierKind),
    /// Being closed; the stream is taken by whoever closes it.
    Closing(Option<Rc<S>>),
}

/// One relay's carrier.
pub(crate) struct Slot<S> {
    pub(crate) state: State<S>,
    /// Counts the changes of `state`, so an operation started under an older state is dropped.
    pub(crate) ver: u64,
    /// The bytes the node wants on the carrier, framed for it, not yet handed to a write.
    out: Vec<u8>,
    /// The bytes of `out` that are answers to the peer's pings, not yet handed to a write.
    pongs: usize,
    /// A buffer a write gave back, kept for the next `out`.
    spare: Vec<u8>,
    /// How much of the buffer of the write in flight is already out.
    wfrom: usize,
    /// A write is in flight: if no driver holds it any more, the carrier is closed.
    writing: bool,
    /// Stream bytes read and not yet taken by the node, from `inoff`.
    inbuf: Vec<u8>,
    inoff: usize,
    /// WebSocket bytes read and not yet decoded.
    raw: Vec<u8>,
    decoder: Decoder,
    /// A read buffer, kept between reads.
    rbuf: Vec<u8>,
}

impl<S> Slot<S> {
    pub(crate) const fn new() -> Self {
        Self {
            state: State::Idle,
            ver: 0,
            out: Vec::new(),
            pongs: 0,
            spare: Vec::new(),
            wfrom: 0,
            writing: false,
            inbuf: Vec::new(),
            inoff: 0,
            raw: Vec::new(),
            decoder: Decoder::new(WsRole::Server),
            rbuf: Vec::new(),
        }
    }

    fn set(&mut self, state: State<S>) {
        self.state = state;
        self.ver += 1;
        self.out.clear();
        self.pongs = 0;
        self.wfrom = 0;
        self.writing = false;
        self.inbuf.clear();
        self.inoff = 0;
        self.raw.clear();
        self.decoder = Decoder::new(WsRole::Server);
    }

    /// Whether the next read may start: the node has taken what was read, a whole read fits in the bytes waiting to be
    /// decoded, and the answers to pings are not behind. A peer that pings faster than the host writes waits in its own
    /// socket; the node's own upload does not hold a read back.
    const fn want_read(&self) -> bool {
        self.inoff >= self.inbuf.len() && self.raw.len() + READ_BUF <= IN_CAP && self.pongs <= OUT_CAP
    }

    const fn is_ws(&self) -> bool {
        matches!(self.state, State::Open(_, CarrierKind::Ws))
    }
}

/// The slots of the relays.
pub(crate) type Slots<S> = [Slot<S>; RELAYS];

pub(crate) fn slots<S>() -> Slots<S> {
    core::array::from_fn(|_| Slot::new())
}

/// The bit of [`Op`]'s state that says an operation runs; the rest is the version of the state it belongs to.
const LIVE: u64 = 1 << 63;

/// An operation in flight: its future lives in one box for the life of the driver, set again for each operation. The
/// version and the flag that it runs share one word, so a slot costs two words.
pub(super) struct Op<F> {
    fut: Option<Pin<Box<F>>>,
    state: u64,
}

impl<F: Future> Op<F> {
    pub(super) const fn new() -> Self {
        Self { fut: None, state: 0 }
    }

    pub(super) const fn running(&self, ver: u64) -> bool {
        self.state == (ver | LIVE)
    }

    pub(super) fn start(&mut self, ver: u64, f: F) {
        match self.fut.as_mut() {
            Some(b) => b.as_mut().set(f),
            None => self.fut = Some(Box::pin(f)),
        }
        self.state = ver | LIVE;
    }

    /// The result, if the operation finished and still belongs to state `ver`.
    pub(super) fn poll(&mut self, cx: &mut Context<'_>, ver: u64) -> Option<F::Output> {
        if self.state & LIVE == 0 {
            return None;
        }
        let out = match self.fut.as_mut()?.as_mut().poll(cx) {
            Poll::Ready(v) => v,
            Poll::Pending => return None,
        };
        self.state &= !LIVE;
        (self.state == ver).then_some(out)
    }

    /// Drop the operation and what it holds.
    pub(super) fn cancel(&mut self) {
        if self.fut.is_some() {
            self.state = 0;
            self.fut = None;
        }
    }
}

async fn open_owned<C: Carriers<Pf>, Pf: Platform>(
    c: &C,
    relay: Relay,
    kind: CarrierKind,
) -> Result<C::Stream, Pf::Error> {
    c.open(&relay, kind).await
}

async fn read_owned<C: Carriers<Pf>, Pf: Platform>(
    c: &C,
    s: Rc<C::Stream>,
    buf: Vec<u8>,
) -> (Result<usize, Pf::Error>, Vec<u8>) {
    c.read(&s, buf).await
}

async fn write_owned<C: Carriers<Pf>, Pf: Platform>(
    c: &C,
    s: Rc<C::Stream>,
    buf: Vec<u8>,
    from: usize,
) -> (Result<usize, Pf::Error>, Vec<u8>) {
    c.write(&s, buf, from).await
}

async fn close_owned<C: Carriers<Pf>, Pf: Platform>(c: &C, s: C::Stream) {
    c.close(s).await;
}

/// What a relay's slot asks of the driver now.
enum View<S> {
    Idle,
    Opening(CarrierKind),
    Open(Rc<S>),
    Closing,
}

type Stream<H> = <<H as Hosted>::Carriers as Carriers<<H as Hosted>::Platform>>::Stream;

impl<H: Hosted> Shared<H> {
    fn view(&self, r: usize) -> Option<(u64, View<Stream<H>>)> {
        let t = self.carriers.try_borrow().ok()?;
        let s = t.get(r)?;
        let v = match &s.state {
            State::Idle => View::Idle,
            State::Opening(k) => View::Opening(*k),
            State::Open(st, _) => View::Open(Rc::clone(st)),
            State::Closing(_) => View::Closing,
        };
        Some((s.ver, v))
    }

    /// Run `f` on the slot of relay `r` if it is still in state `ver`.
    fn with_slot<T>(&self, r: usize, ver: u64, f: impl FnOnce(&mut Slot<Stream<H>>) -> T) -> Option<T> {
        let mut t = self.carriers.try_borrow_mut().ok()?;
        let s = t.get_mut(r).filter(|s| s.ver == ver)?;
        Some(f(s))
    }

    /// The node asked for carriers or has bytes for them: take both into the slots. Wakes the driver if there is
    /// something for it to do and `wake` is set.
    pub(crate) fn pump_carriers(&self, core: &mut Core<H::Keys, H::Access>, wake: bool) {
        if self.relays.is_empty() {
            return;
        }
        let Ok(mut t) = self.carriers.try_borrow_mut() else {
            return;
        };
        let mut work = false;
        while let Some(io) = core.carrier_io() {
            work = true;
            match io {
                CarrierIo::Open { relay, kind, .. } => {
                    let ws = matches!(kind, Kind::Ws);
                    if let (Some(s), Some(rel)) = (t.get_mut(relay), self.relays.get(relay)) {
                        s.set(State::Opening(rel.kind(ws)));
                    }
                }
                CarrierIo::Close { relay } => {
                    if let Some(s) = t.get_mut(relay) {
                        let held = match core::mem::replace(&mut s.state, State::Idle) {
                            State::Open(st, _) => Some(st),
                            _ => None,
                        };
                        s.set(State::Closing(held));
                    }
                }
            }
        }
        let mut scratch = self.tx_buf();
        for (r, s) in t.iter_mut().enumerate() {
            let State::Open(_, kind) = s.state else { continue };
            let framed = kind == CarrierKind::Ws;
            let before = s.out.len();
            let whole = take_out(&mut s.out, &mut scratch.v, framed, |buf| {
                let n = core.carrier_out(r, buf);
                let mut mask = [0u8; 4];
                if framed && n > 0 {
                    core.random(&mut mask);
                }
                (n, mask)
            });
            work |= s.out.len() != before || !whole;
            if !whole {
                // Bytes the node gave could not be framed: the stream would have a hole, so the carrier ends here.
                if let State::Open(st, _) = core::mem::replace(&mut s.state, State::Idle) {
                    s.set(State::Closing(Some(st)));
                }
                core.carrier_closed(self.now(), r);
                self.cdirty.set(true);
            }
        }
        drop(t);
        if work && wake {
            core.wake_driver();
        }
    }

    /// A driver that died mid-write left a carrier whose stream may hold half a buffer: close it.
    fn adopt_carriers(&self) {
        let now = self.now();
        let Some(mut core) = self.lock() else { return };
        let Ok(mut t) = self.carriers.try_borrow_mut() else {
            return;
        };
        for (r, s) in t.iter_mut().enumerate() {
            if s.writing {
                let st = match core::mem::replace(&mut s.state, State::Idle) {
                    State::Open(st, _) => Some(st),
                    _ => None,
                };
                s.set(State::Closing(st));
                core.carrier_closed(now, r);
            }
        }
    }

    /// Close relay `r`'s carrier because it failed, and tell the node (once).
    fn fail_carrier(&self, r: usize, ver: u64) {
        let now = self.now();
        let Some(mut core) = self.lock() else { return };
        let was = self
            .with_slot(r, ver, |s| match core::mem::replace(&mut s.state, State::Idle) {
                State::Open(st, _) => {
                    s.set(State::Closing(Some(st)));
                    true
                }
                State::Opening(_) => {
                    s.set(State::Idle);
                    true
                }
                other => {
                    s.state = other;
                    false
                }
            })
            .unwrap_or(false);
        if was {
            core.carrier_closed(now, r);
            self.cdirty.set(true);
        }
    }

    fn carrier_opened(&self, r: usize, ver: u64, res: Result<Stream<H>, <H::Platform as Platform>::Error>) {
        match res {
            Ok(st) => {
                let now = self.now();
                let Some(mut core) = self.lock() else { return };
                let kind = self.with_slot(r, ver, |s| {
                    let kind = match s.state {
                        State::Opening(k) => k,
                        _ => CarrierKind::Tcp,
                    };
                    s.set(State::Open(Rc::new(st), kind));
                    kind
                });
                if kind.is_some() {
                    core.carrier_opened(now, r);
                    self.cdirty.set(true);
                }
            }
            Err(_) => self.fail_carrier(r, ver),
        }
    }

    /// Hand the bytes read and not yet taken to the node; decode WebSocket frames first.
    fn carrier_feed(&self, r: usize, ver: u64) {
        let pending = self
            .with_slot(r, ver, |s| s.inoff < s.inbuf.len() || (s.is_ws() && !s.raw.is_empty()))
            .unwrap_or(false);
        if !pending {
            return;
        }
        let now = self.now();
        let Some(mut core) = self.lock() else { return };
        let mut broken = false;
        self.with_slot(r, ver, |s| {
            for _ in 0..64 {
                if s.inoff >= s.inbuf.len() {
                    s.inbuf.clear();
                    s.inoff = 0;
                    if s.is_ws() {
                        match ws_fill(s) {
                            Ok(true) => {}
                            Ok(false) => break,
                            Err(()) => {
                                broken = true;
                                break;
                            }
                        }
                    } else {
                        break;
                    }
                }
                let Some(rest) = s.inbuf.get(s.inoff..) else { break };
                let n = core.carrier_in(now, r, rest);
                // A key request the carrier handshake waits for is answered by the next service, then the rest is taken.
                let moved = self.service(&mut core, now);
                s.inoff += n;
                if n == 0 && moved == 0 {
                    break;
                }
            }
        });
        drop(core);
        if broken {
            self.fail_carrier(r, ver);
        }
    }

    fn carrier_read_done(&self, r: usize, ver: u64, got: Option<usize>, buf: Vec<u8>) {
        match got {
            Some(n) if n > 0 => {
                self.with_slot(r, ver, |s| {
                    let got = buf.get(..n).unwrap_or_default();
                    if s.is_ws() {
                        s.raw.extend_from_slice(got);
                    } else {
                        s.inbuf.clear();
                        s.inbuf.extend_from_slice(got);
                        s.inoff = 0;
                    }
                    s.rbuf = buf;
                });
                self.cdirty.set(true);
            }
            _ => self.fail_carrier(r, ver),
        }
    }

    /// The next buffer to write, if the node has bytes and no write is in flight.
    fn carrier_write_start(&self, r: usize, ver: u64) -> Option<Vec<u8>> {
        self.with_slot(r, ver, |s| {
            if s.out.is_empty() {
                return None;
            }
            s.writing = true;
            s.wfrom = 0;
            s.pongs = 0;
            let spare = core::mem::take(&mut s.spare);
            Some(core::mem::replace(&mut s.out, spare))
        })
        .flatten()
    }

    /// A write finished: the rest of its buffer to write, or `None` when it is all out or the carrier failed.
    fn carrier_write_done(&self, r: usize, ver: u64, got: Option<usize>, mut buf: Vec<u8>) -> Option<(Vec<u8>, usize)> {
        let again = self
            .with_slot(r, ver, |s| match got {
                Some(n) if n > 0 => {
                    s.wfrom += n;
                    if s.wfrom < buf.len() {
                        return Some(true);
                    }
                    buf.clear();
                    s.spare = core::mem::take(&mut buf);
                    s.writing = false;
                    s.wfrom = 0;
                    Some(false)
                }
                _ => None,
            })
            .flatten();
        match again {
            Some(true) => {
                let from = self.with_slot(r, ver, |s| s.wfrom).unwrap_or(0);
                Some((buf, from))
            }
            Some(false) => None,
            None => {
                self.fail_carrier(r, ver);
                None
            }
        }
    }

    fn carrier_take_closing(&self, r: usize, ver: u64) -> Option<Rc<Stream<H>>> {
        self.with_slot(r, ver, |s| match &mut s.state {
            State::Closing(st) => st.take(),
            _ => None,
        })
        .flatten()
    }

    fn carrier_closed(&self, r: usize, ver: u64) {
        self.with_slot(r, ver, |s| s.set(State::Idle));
    }

    /// The driver's carrier work as one future that never completes; the driving future polls it. Its locals hold the
    /// operations in flight.
    #[allow(
        clippy::too_many_lines,
        reason = "one poll function: the slots of every relay and the exchange share its locals"
    )]
    pub(super) async fn carriers_task(&self) {
        let c = self.host.carriers();
        self.adopt_carriers();
        let mut opens: [Op<_>; RELAYS] = core::array::from_fn(|_| Op::new());
        let mut reads: [Op<_>; RELAYS] = core::array::from_fn(|_| Op::new());
        let mut writes: [Op<_>; RELAYS] = core::array::from_fn(|_| Op::new());
        let mut closes: [Op<_>; RELAYS] = core::array::from_fn(|_| Op::new());
        let mut hop = Op::new();
        poll_fn(|cx| {
            let mut moved = false;
            for r in 0..RELAYS {
                let (Some((ver, view)), Some(open), Some(read), Some(write), Some(close)) = (
                    self.view(r),
                    opens.get_mut(r),
                    reads.get_mut(r),
                    writes.get_mut(r),
                    closes.get_mut(r),
                ) else {
                    continue;
                };
                match view {
                    View::Idle => {
                        open.cancel();
                        read.cancel();
                        write.cancel();
                        close.cancel();
                    }
                    View::Opening(kind) => {
                        read.cancel();
                        write.cancel();
                        close.cancel();
                        if <H::Carriers as Carriers<H::Platform>>::NONE {
                            // No carriers: the open fails in this pass, as an open that answers at once would.
                            moved = true;
                            self.fail_carrier(r, ver);
                        } else {
                            if !open.running(ver)
                                && let Some(rel) = self.relays.get(r)
                            {
                                open.start(ver, open_owned::<_, H::Platform>(c, *rel, kind));
                            }
                            if let Some(res) = open.poll(cx, ver) {
                                moved = true;
                                self.carrier_opened(r, ver, res);
                            }
                        }
                    }
                    View::Open(st) => {
                        open.cancel();
                        close.cancel();
                        self.carrier_feed(r, ver);
                        let want_read = self.with_slot(r, ver, |s| s.want_read()).unwrap_or(false);
                        if want_read && !read.running(ver) {
                            let buf = self
                                .with_slot(r, ver, |s| {
                                    // The host fills at most the length of the vector, from its start.
                                    let mut b = core::mem::take(&mut s.rbuf);
                                    b.resize(READ_BUF, 0);
                                    b
                                })
                                .unwrap_or_default();
                            read.start(ver, read_owned::<_, H::Platform>(c, Rc::clone(&st), buf));
                        }
                        if let Some((res, buf)) = read.poll(cx, ver) {
                            moved = true;
                            self.carrier_read_done(r, ver, res.ok(), buf);
                        }
                        if !write.running(ver)
                            && let Some(buf) = self.carrier_write_start(r, ver)
                        {
                            write.start(ver, write_owned::<_, H::Platform>(c, Rc::clone(&st), buf, 0));
                        }
                        if let Some((res, buf)) = write.poll(cx, ver) {
                            moved = true;
                            if let Some((buf, from)) = self.carrier_write_done(r, ver, res.ok(), buf) {
                                write.start(ver, write_owned::<_, H::Platform>(c, Rc::clone(&st), buf, from));
                            }
                        }
                    }
                    View::Closing => {
                        open.cancel();
                        read.cancel();
                        write.cancel();
                        if !close.running(ver) {
                            let taken = self.carrier_take_closing(r, ver).map(Rc::try_unwrap);
                            if let Some(Ok(st)) = taken {
                                close.start(ver, close_owned::<_, H::Platform>(c, st));
                            } else {
                                moved = true;
                                self.carrier_closed(r, ver);
                            }
                        }
                        if close.poll(cx, ver).is_some() {
                            moved = true;
                            self.carrier_closed(r, ver);
                        }
                    }
                }
            }
            moved |= self.http_drive(cx, &mut hop, |step| http_io::host_step::<_, H::Platform>(c, step));
            if moved {
                // What finished may let the next step start: look again at once.
                cx.waker().wake_by_ref();
            }
            Poll::<()>::Pending
        })
        .await;
    }
}

/// Decode the WebSocket frames in the slot's raw bytes into stream bytes, until some are ready: whether there are any
/// yet; an error if the stream broke the framing.
fn ws_fill<S>(s: &mut Slot<S>) -> Result<bool, ()> {
    let Slot {
        raw,
        inbuf,
        decoder,
        out,
        pongs,
        ..
    } = s;
    while inbuf.is_empty() {
        let (frame, used) = match decoder.decode(raw) {
            Ok(Some(f)) => f,
            Ok(None) => return Ok(false),
            Err(_) => return Err(()),
        };
        match frame {
            WsFrame::Data(p) => inbuf.extend_from_slice(p),
            WsFrame::Ping(p) => {
                // The answer to a ping; the mask of a control frame need not be secret.
                let at = out.len();
                out.resize(at + p.len() + ws::MAX_HEADER, 0);
                let n = out
                    .get_mut(at..)
                    .and_then(|o| ws::encode(Opcode::Pong, p, Some([0x5a, 0xa5, 0x3c, 0xc3]), o).ok())
                    .unwrap_or(0);
                out.truncate(at + n);
                *pongs += n;
            }
            WsFrame::Pong(_) | WsFrame::Close(_) => {}
        }
        raw.drain(..used);
    }
    Ok(true)
}

#[cfg(test)]
#[allow(clippy::cast_possible_truncation, reason = "bytes counted modulo 251")]
mod tests {
    use alloc::vec;

    use super::*;

    /// A source of `total` counted bytes that gives as many as the buffer takes.
    fn source(total: usize) -> impl FnMut(&mut [u8]) -> (usize, [u8; 4]) {
        let mut given = 0usize;
        move |buf| {
            let n = buf.len().min(total - given);
            for (i, b) in buf.iter_mut().take(n).enumerate() {
                *b = ((given + i) % 251) as u8;
            }
            given += n;
            (n, [1, 2, 3, 4])
        }
    }

    #[test]
    fn more_than_one_frame_of_waiting_bytes_is_framed_whole_and_in_order() {
        let total = 3 * ws::MAX_PAYLOAD + 777;
        let (mut out, mut scratch) = (Vec::new(), vec![0u8; 64 * 1024]);
        assert!(take_out(&mut out, &mut scratch, true, source(total)));
        let (mut dec, mut got, mut at) = (Decoder::new(WsRole::Client), Vec::new(), 0);
        while let Ok(Some((frame, used))) = dec.decode(out.get_mut(at..).unwrap_or_default()) {
            if let WsFrame::Data(p) = frame {
                assert!(p.len() <= ws::MAX_PAYLOAD);
                got.extend_from_slice(p);
            }
            at += used;
        }
        let want: Vec<u8> = (0..total).map(|i| (i % 251) as u8).collect();
        assert_eq!((got.len(), got == want, at), (total, true, out.len()));
    }

    #[test]
    fn a_plain_carrier_takes_the_bytes_as_they_are_up_to_the_cap() {
        let (mut out, mut scratch) = (Vec::new(), vec![0u8; 64 * 1024]);
        assert!(take_out(&mut out, &mut scratch, false, source(100_000)));
        assert_eq!(out.len(), 100_000);
        let mut out = Vec::new();
        assert!(take_out(&mut out, &mut scratch, false, source(OUT_CAP + 200_000)));
        assert!(out.len() >= OUT_CAP && out.len() < OUT_CAP + scratch.len());
    }

    /// A peer that pings faster than the host writes the answers stops being read, so the answers stay bounded.
    #[test]
    fn a_peer_that_pings_faster_than_the_host_writes_is_not_read_on() {
        let mut s = Slot::<()>::new();
        let mut ping = [0u8; ws::MAX_HEADER];
        let n = ws::encode(Opcode::Ping, &[], None, &mut ping).unwrap_or(0);
        assert!(n > 0);
        let mut reads = 0;
        while s.want_read() && reads < 1000 {
            reads += 1;
            for _ in 0..READ_BUF / n {
                s.raw.extend_from_slice(ping.get(..n).unwrap_or_default());
            }
            assert_eq!(ws_fill(&mut s), Ok(false));
        }
        assert!(
            reads < 1000,
            "still reading with {} bytes of answers waiting",
            s.pongs
        );
        assert!(
            s.out.len() <= OUT_CAP + 3 * IN_CAP,
            "{} bytes of answers waiting",
            s.out.len()
        );
    }

    /// The node's own outgoing bytes do not stop the reads: a carrier under upload still reads, as its downlink carries
    /// the acknowledgements the upload needs.
    #[test]
    fn data_waiting_to_be_written_does_not_stop_the_reads() {
        let mut s = Slot::<()>::new();
        s.out.resize(OUT_CAP + 1, 0);
        assert!(s.want_read(), "a read waits behind the node's own upload");
    }
}
