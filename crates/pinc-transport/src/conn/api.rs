//! The application calls: streams, datagrams and events.

use pinc_crypto::Provider;
use pinc_security::Env;
use pinc_wire::varint;

use super::ctl::{Ctl, EXT_BODY_MAX};
use super::event::{Ev, Event};
use super::path::CTRL_SMALL;
use super::{Connection, MIN_MTU, Phase};
use crate::packet::PN_LEN_WIDE;
use crate::stream::datagram::DatagramError;
use crate::stream::spill::SpillArena;
use crate::stream::store::ChunkStore;
use crate::stream::{PeerLimits, RecvStatus, StreamError, StreamId, StreamSource};

/// A DATAGRAM frame spends its type and a two-byte length besides the data.
const DATAGRAM_FRAME_OVERHEAD: usize = 3;
/// The largest extension queue entry: the type, then a body of at most [`EXT_BODY_MAX`] bytes.
const EXT_ENTRY_MAX: usize = EXT_BODY_MAX + 9;
/// The length prefix of an extension frame, at most two bytes below the largest MTU.
const EXT_LEN_PREFIX: usize = 2;

/// Why an extension frame could not be queued.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExtensionError {
    /// The type is below 0x40 or cannot be encoded.
    BadType,
    /// The body cannot fit one packet at the current path MTU.
    TooLarge {
        /// The largest body that fits now.
        max_size: usize,
    },
    /// The pool has no chunk left and nothing older could be dropped to make room.
    Exhausted,
}

impl core::fmt::Display for ExtensionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::BadType => "extension frame type below 0x40",
            Self::TooLarge { .. } => "extension frame larger than one packet",
            Self::Exhausted => "buffer pool exhausted",
        })
    }
}

impl core::error::Error for ExtensionError {}
/// A short packet spends its first byte and the 16-byte tag besides the packet number and the connection id.
const SHORT_PACKET_FIXED: usize = 1 + 16;
/// The send buffer holds at least this much whatever the window (192 KiB).
const BUFFER_FLOOR: u64 = 196_608;

conn_impl! {
    /// Whether the connection still takes application data: it is not closing, draining or closed.
    fn is_open(&self) -> bool {
        matches!(self.phase, Phase::Handshaking | Phase::Connected)
    }

    fn ensure_open(&self) -> Result<(), StreamError> {
        if self.is_open() { Ok(()) } else { Err(StreamError::UnknownStream) }
    }

    /// The next event, or `None`. Events that carry data borrow it from the connection and the endpoint's store until
    /// the next call.
    pub fn poll_event<'s>(&'s mut self, mut lent: super::Lent<'s, 'a>) -> Option<Event<'s>> {
        self.with_lent(&mut lent, |c| {
            if c.ext_release {
                c.ext.release(&mut c.pool);
                c.ext_release = false;
            }
            c.notify_open_ready();
        });
        let store: &'s ChunkStore = lent.store;
        loop {
            let ev = self.events.pop()?;
            return Some(match ev {
                Ev::KeyRequest => match self.hs.request.as_ref() {
                    Some(r) => Event::KeyRequest(r.as_request()),
                    None => continue,
                },
                Ev::Extension => {
                    let Some(entry) = self.ext.recv_datagram(self.pool.mem_in(store)) else { continue };
                    let Ok((ty, n)) = varint::decode(entry) else {
                        self.ext_release = true;
                        continue;
                    };
                    self.ext_release = true;
                    Event::Extension { ty, body: entry.get(n..).unwrap_or_default() }
                }
                Ev::ExtensionUndeliverable(ty, len) => Event::ExtensionUndeliverable { ty, len },
                Ev::Connected(resumed) => Event::Connected { resumed },
                Ev::Opened(id) => Event::StreamOpened(id),
                Ev::Readable(id) => Event::StreamReadable(id),
                Ev::Writable(id) => Event::StreamWritable(id),
                Ev::OpenReady => Event::OpenReady,
                Ev::Reset(id, error) => Event::StreamReset { id, error },
                Ev::Stopped(id, error) => Event::StreamStopped { id, error },
                Ev::Datagram => Event::DatagramReceived,
                Ev::PathValidated(p) => Event::PathValidated(p),
                Ev::PathFailed(p) => Event::PathFailed(p),
                Ev::PeerAsleep => Event::PeerAsleep,
                Ev::PeerAwake => Event::PeerAwake,
                Ev::WakeUnanswered => Event::WakeUnanswered,
                Ev::Tickets => match self.events.tickets.take() {
                    Some(b) => Event::TicketsReceived(b),
                    None => continue,
                },
                Ev::Ready => Event::Ready,
                Ev::Closed(r) => Event::Closed(r),
            });
        }
    }

    /// Raise by hand the number of streams this side may open in all, for a peer known to admit more than it said.
    /// The peer's held-back rule then applies to the streams beyond its room: they wait unacknowledged until it has
    /// some.
    pub fn raise_stream_credit(&mut self, limit: u64) {
        self.streams.on_max_streams(limit);
    }

    /// A dial reported connected before its handshake ran: let the application open streams and queue data now, though
    /// the peer's limits are not known. Nothing leaves before the keys exist; once the peer's record arrives, a stream
    /// within its stream limit goes out and one past it waits for credit, in the order the streams were opened. Each
    /// stream may queue what the smallest window a record can state (one 16 KiB unit) allows until the record arrives.
    pub fn allow_early_streams(&mut self) {
        self.streams.set_early(true);
        self.streams.set_peer_limits(&PeerLimits { window: super::hooks::PENDING_WINDOW, max_streams: 0 });
    }

    /// Whether a stream of the given kind could open now. A host whose open got [`StreamError::StreamLimit`] (no
    /// credit yet) or [`StreamError::Exhausted`] (no pool room for the window) keeps the open and asks again after each
    /// input it feeds the connection, until this is `Ok`; credit and room return only through such inputs.
    ///
    /// # Errors
    /// The error an open would return.
    pub fn open_ready(&self, store: &ChunkStore, bidi: bool) -> Result<(), StreamError> {
        self.ensure_open()?;
        self.streams.can_open(self.pool.mem_in(store), bidi)
    }

    /// Open a bidirectional stream.
    ///
    /// # Errors
    /// [`StreamError::StreamLimit`] at the peer's limit, [`StreamError::TableFull`] when the table has no slot,
    /// [`StreamError::Exhausted`] when the first charge of the stream's receive window does not fit in the buffer pool
    /// yet.
    pub fn open_bi(&mut self, lent: &mut super::Lent<'_, 'a>) -> Result<StreamId, StreamError> {
        self.ensure_open()?;
        self.with_lent(lent, |c| c.opened(true))
    }

    /// Open a unidirectional stream.
    ///
    /// # Errors
    /// As [`open_bi`](Self::open_bi).
    pub fn open_uni(&mut self, lent: &mut super::Lent<'_, 'a>) -> Result<StreamId, StreamError> {
        self.ensure_open()?;
        self.with_lent(lent, |c| c.opened(false))
    }

    /// Open a stream; a refusal for want of credit or room is remembered, so [`Event::OpenReady`] follows once an open
    /// of that kind would work.
    fn opened(&mut self, bidi: bool) -> Result<StreamId, StreamError> {
        let r = self.streams.open_stream(&self.pool, bidi);
        if matches!(r, Err(StreamError::StreamLimit | StreamError::Exhausted)) {
            self.open_wait |= 1 << u8::from(bidi);
        }
        r
    }

    /// Queue [`Event::OpenReady`] when an open that was refused would work now. One check of two flags per poll while
    /// no open waits.
    fn notify_open_ready(&mut self) {
        if self.open_wait == 0 {
            return;
        }
        for bidi in [false, true] {
            let bit = 1 << u8::from(bidi);
            if self.open_wait & bit != 0 && self.is_open() && self.streams.can_open(self.pool.mem(), bidi).is_ok() {
                self.open_wait &= !bit;
                self.events.push(Ev::OpenReady);
            }
        }
    }

    /// How much written data may wait for its acknowledgement at once, over all streams: the smaller of
    /// [`Config::send_window`] and `max(192 KiB, 1.5 x the congestion window)`. The window the peer granted bounds
    /// each stream on its own.
    pub(super) fn send_buffer_cap(&self) -> u64 {
        self.cfg.send_window.min(BUFFER_FLOOR.max(self.rec.cwnd().saturating_mul(3) / 2))
    }

    /// Buffer bytes for sending on a stream; returns how many were accepted (0 when the peer's credit, the pool,
    /// the stream's buffer or the send buffer limit is full: try again after [`Event::StreamWritable`] or
    /// when acknowledgements free room). Every write, finish and reset needs no clock, so none takes an `Env`.
    ///
    /// # Errors
    /// The errors of [`Streams::write`](crate::stream::Streams::write).
    pub fn write(&mut self, lent: &mut super::Lent<'_, 'a>, id: StreamId, data: &[u8]) -> Result<usize, StreamError> {
        self.ensure_open()?;
        let cap = self.send_buffer_cap();
        let n = self.with_lent(lent, |c| c.streams.write(&mut c.pool, id, data, cap))?;
        self.life.app_written = true;
        self.life.data_written |= data.len() > CTRL_SMALL;
        Ok(n)
    }

    /// Set the urgency of a stream: streams are served in order of urgency (lower first, 3 by default), then id.
    ///
    /// # Errors
    /// The errors of [`Streams::set_urgency`](crate::stream::Streams::set_urgency).
    pub fn set_urgency(&mut self, id: StreamId, urgency: u8) -> Result<(), StreamError> {
        self.streams.set_urgency(id, urgency)
    }

    /// Back a stream with application storage of `len` bytes: nothing is buffered, bytes are read from `source`
    /// when a packet is built and again when a range is lost, and the stream ends after `len` bytes.
    ///
    /// # Errors
    /// The errors of [`Streams::open_source`](crate::stream::Streams::open_source).
    pub fn write_source(&mut self, id: StreamId, source: S, len: u64) -> Result<(), StreamError> {
        self.streams.open_source(id, source, len)
    }

    /// End a buffered stream after the bytes written so far.
    ///
    /// # Errors
    /// The errors of [`Streams::finish`](crate::stream::Streams::finish).
    pub fn finish(&mut self, id: StreamId) -> Result<(), StreamError> {
        self.streams.finish(id)
    }

    /// Abandon the send side of a stream and tell the peer with `error`.
    ///
    /// # Errors
    /// The errors of [`Streams::reset`](crate::stream::Streams::reset).
    pub fn reset(&mut self, lent: &mut super::Lent<'_, 'a>, id: StreamId, error: u64) -> Result<(), StreamError> {
        self.with_lent(lent, |c| c.streams.reset(&mut c.pool, id, error))
    }

    /// Ask the peer to stop sending on a stream; it resets the stream with `error`, which arrives as a reset. The
    /// request is repeated until acknowledged. Nothing happens if the peer already ended the stream.
    ///
    /// # Errors
    /// The errors of [`Streams::stop_sending`](crate::stream::Streams::stop_sending).
    pub fn stop_sending(&mut self, id: StreamId, error: u64) -> Result<(), StreamError> {
        self.streams.stop_sending(id, error)
    }

    /// The readable bytes of a stream, borrowed from the pool. Release them with [`consume`](Self::consume).
    pub fn read_chunk<'s>(&'s self, store: &'s ChunkStore, id: StreamId) -> Option<&'s [u8]> {
        self.streams.read_chunk(self.pool.mem_in(store), id)
    }

    /// The stored bytes of a stream from absolute offset `at`, up to the end of the run holding them or of one chunk,
    /// borrowed from the pool. The run may lie beyond a hole, so a host can check bytes as they arrive out of order.
    /// Release bytes only through [`consume`](Self::consume), which moves through the contiguous prefix. `spill` is
    /// the endpoint's arena, read only: a read changes nothing, so it needs no [`Lent`](super::Lent).
    pub fn read_at<'s>(
        &'s self,
        spill: &SpillArena<'_>,
        store: &'s ChunkStore,
        id: StreamId,
        at: u64,
    ) -> Option<&'s [u8]> {
        self.streams.read_at(self.pool.mem_in(store), spill, id, at)
    }

    /// The first run of stored bytes of a stream that reaches past `from`, cut to begin at `from` or later.
    pub fn stored_after(&self, spill: &SpillArena<'_>, id: StreamId, from: u64) -> Option<core::ops::Range<u64>> {
        self.streams.stored_after(spill, id, from)
    }

    /// The urgency of a stream; `None` if it is unknown.
    pub fn urgency(&self, id: StreamId) -> Option<u8> {
        self.streams.urgency(id)
    }

    /// The state of a stream's send half; `None` if the stream is unknown or already closed.
    pub fn send_view(&self, id: StreamId) -> Option<crate::stream::SendView> {
        self.streams.send_view(id)
    }

    /// Release `n` readable bytes of a stream; consuming 0 after the end was read lets the stream close. The clock
    /// and the round trip drive the autotuning of the receive window.
    ///
    /// # Errors
    /// The errors of [`Streams::consume`](crate::stream::Streams::consume).
    pub fn consume(
        &mut self,
        env: &mut Env<'_, P>,
        lent: &mut super::Lent<'_, 'a>,
        id: StreamId,
        n: usize,
    ) -> Result<RecvStatus, StreamError> {
        let srtt = self.rec.rtt().smoothed();
        self.with_lent(lent, |c| c.streams.consume(&mut c.pool, id, n, env.now, srtt))
    }

    /// The state of a stream's receive side.
    pub fn recv_status(&self, id: StreamId) -> Option<RecvStatus> {
        self.streams.recv_status(id)
    }

    /// The most data one datagram can carry on the active path now.
    pub fn max_datagram_size(&self) -> usize {
        if !self.is_open() {
            return 0;
        }
        let mtu = self.paths.active().map_or(usize::from(MIN_MTU), |p| usize::from(p.mtu.current));
        let fixed = SHORT_PACKET_FIXED + self.pn_len.clamp(crate::packet::PN_LEN_BASE, PN_LEN_WIDE);
        let peer = usize::from(self.peer_credit.max_datagram);
        mtu.saturating_sub(fixed + self.cfg.cid_len + DATAGRAM_FRAME_OVERHEAD)
            .min(peer.saturating_sub(DATAGRAM_FRAME_OVERHEAD))
    }

    /// Queue an unreliable datagram. The oldest queued datagram is dropped if the queue is full.
    ///
    /// # Errors
    /// [`DatagramError::TooLarge`] above [`max_datagram_size`](Self::max_datagram_size), or
    /// [`DatagramError::Exhausted`] when the pool is empty.
    pub fn send_datagram(&mut self, lent: &mut super::Lent<'_, 'a>, data: &[u8]) -> Result<(), DatagramError> {
        let max = self.max_datagram_size();
        self.life.app_written = true;
        self.with_lent(lent, |c| c.dgrams.send_datagram(&mut c.pool, data, max))
    }

    /// The largest body [`send_extension`](Self::send_extension) takes for type `ty` on the active path now: what is
    /// left of a packet's payload after the type and the length prefix of the frame.
    pub fn max_extension_size(&self, ty: u64) -> usize {
        if !self.is_open() {
            return 0;
        }
        let mtu = self.paths.active().map_or(usize::from(MIN_MTU), |p| usize::from(p.mtu.current));
        // The widest packet number, so the room holds if the width grows after the frame is queued.
        let payload = mtu.saturating_sub(SHORT_PACKET_FIXED + PN_LEN_WIDE + self.cfg.cid_len);
        payload.saturating_sub(varint::encoded_len(ty) + EXT_LEN_PREFIX).min(EXT_BODY_MAX)
    }

    /// Drop every held extension frame that no longer fits one packet at the current path MTU, freeing its slot, and
    /// tell the application with [`Event::ExtensionUndeliverable`].
    pub(super) fn shed_extensions(&mut self) {
        if !self.is_open() {
            return;
        }
        for i in 0..self.ctl.ext.len() {
            let Some((ty, len)) = self.ctl.ext.get(i).and_then(|s| s.as_ref().map(|s| (s.ty, s.len))) else { continue };
            if len > self.max_extension_size(ty) {
                if let Some(s) = self.ctl.ext.get_mut(i) {
                    Ctl::free_ext(s, &mut self.pool);
                }
                self.events.push(Ev::ExtensionUndeliverable(ty, len));
            }
        }
    }

    /// Queue an extension frame (type 0x40 and up) for the endpoint layer. It is sent ahead of stream data and sent
    /// again whenever its packet is declared lost, until a packet carrying it is acknowledged; the peer may therefore
    /// receive it more than once. The queue is bounded and drops its oldest entry when full. The frame must fit one
    /// packet at the current path MTU, see [`max_extension_size`](Self::max_extension_size).
    ///
    /// # Errors
    /// [`ExtensionError::BadType`] if `ty` is below 0x40 or not a varint, [`ExtensionError::TooLarge`] if the body
    /// cannot fit one packet, and [`ExtensionError::Exhausted`] when the pool is empty.
    pub fn send_extension(&mut self, lent: &mut super::Lent<'_, 'a>, ty: u64, body: &[u8]) -> Result<(), ExtensionError> {
        if ty < crate::frame::EXTENSION_BASE {
            return Err(ExtensionError::BadType);
        }
        let max_size = self.max_extension_size(ty);
        if body.len() > max_size {
            return Err(ExtensionError::TooLarge { max_size });
        }
        let mut buf = [0u8; 9];
        let head = varint::encode(ty, &mut buf).map_err(|_| ExtensionError::BadType)?;
        // The queue holds one contiguous entry: the type, then the body.
        let mut entry = [0u8; EXT_ENTRY_MAX];
        let used = entry.get_mut(..head + body.len()).ok_or(ExtensionError::TooLarge { max_size })?;
        let (h, b) = used.split_at_mut(head);
        h.copy_from_slice(buf.get(..head).unwrap_or_default());
        b.copy_from_slice(body);
        let used = &*used;
        self.life.app_written = true;
        self.with_lent(lent, |c| c.ext.send_datagram(&mut c.pool, used, EXT_ENTRY_MAX))
            .map_err(|_| ExtensionError::Exhausted)
    }

    /// Gate the connection: while `gated`, a packet with a frame that would raise an event for the application
    /// (stream data, a reset, a datagram, an extension, READY, tickets, sleep and wake, a path answer) is refused with
    /// [`Drop::Gated`](super::Drop::Gated) before it is processed or acknowledged, so the peer sends it again. Packets
    /// that raise no event, such as ACK-only packets and CLOSE, are still taken. An endpoint gates a session whose
    /// events the application has not read, so the event queue never overflows.
    pub fn set_gated(&mut self, gated: bool) {
        self.gated = gated;
    }

    /// The oldest received datagram, borrowed; remove it with [`pop_datagram`](Self::pop_datagram).
    pub fn recv_datagram<'s>(&'s self, store: &'s ChunkStore) -> Option<&'s [u8]> {
        self.dgrams.recv_datagram(self.pool.mem_in(store))
    }

    /// Remove the datagram [`recv_datagram`](Self::recv_datagram) returned.
    pub fn pop_datagram(&mut self, lent: &mut super::Lent<'_, 'a>) {
        self.with_lent(lent, |c| c.dgrams.release(&mut c.pool));
    }
}
