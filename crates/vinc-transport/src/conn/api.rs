//! The application calls: streams, datagrams and events.

use vinc_crypto::Provider;
use vinc_security::Env;
use vinc_wire::varint;

use super::ctl::EXT_BODY_MAX;
use super::event::{Ev, Event};
use super::path::CTRL_SMALL;
use super::{Connection, MIN_MTU, Phase};
use crate::packet::PN_LEN_WIDE;
use crate::stream::datagram::DatagramError;
use crate::stream::{RecvStatus, StreamError, StreamId, StreamSource};

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

    /// The next event, or `None`. Events that carry data borrow it from the connection until the next call.
    pub fn poll_event(&mut self) -> Option<Event<'_>> {
        if self.ext_release {
            self.ext.release(&mut self.pool);
            self.ext_release = false;
        }
        loop {
            let ev = self.events.pop()?;
            return Some(match ev {
                Ev::KeyRequest => match self.hs.request.as_ref() {
                    Some(r) => Event::KeyRequest(r.as_request()),
                    None => continue,
                },
                Ev::Extension => {
                    let Some(entry) = self.ext.recv_datagram(&self.pool) else { continue };
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
                Ev::Reset(id, error) => Event::StreamReset { id, error },
                Ev::Datagram => Event::DatagramReceived,
                Ev::PathValidated(p) => Event::PathValidated(p),
                Ev::PathFailed(p) => Event::PathFailed(p),
                Ev::PeerAsleep => Event::PeerAsleep,
                Ev::PeerAwake => Event::PeerAwake,
                Ev::WakeUnanswered => Event::WakeUnanswered,
                Ev::Tickets(b) => Event::TicketsReceived(b),
                Ev::Ready => Event::Ready,
                Ev::Closed(r) => Event::Closed(r),
            });
        }
    }

    /// Open a bidirectional stream.
    ///
    /// # Errors
    /// [`StreamError::StreamLimit`] at the peer's limit, [`StreamError::TableFull`] when the table has no slot.
    pub fn open_bi(&mut self) -> Result<StreamId, StreamError> {
        self.ensure_open()?;
        self.streams.open_stream(true)
    }

    /// Open a unidirectional stream.
    ///
    /// # Errors
    /// As [`open_bi`](Self::open_bi).
    pub fn open_uni(&mut self) -> Result<StreamId, StreamError> {
        self.ensure_open()?;
        self.streams.open_stream(false)
    }

    /// How much written data may wait for its acknowledgement at once: the smaller of the window the peer granted
    /// and `max(192 KiB, 1.5 x the congestion window)`.
    pub(super) fn send_buffer_cap(&self) -> u64 {
        let window = self.peer_credit.window_bytes();
        window.min(BUFFER_FLOOR.max(self.rec.cwnd().saturating_mul(3) / 2))
    }

    /// Buffer bytes for sending on a stream; returns how many were accepted (0 when the peer's credit, the pool,
    /// the stream's buffer or the send buffer limit is full: try again after [`Event::StreamWritable`] or
    /// when acknowledgements free room). Every write, finish and reset needs no clock, so none takes an `Env`.
    ///
    /// # Errors
    /// The errors of [`Streams::write`](crate::stream::Streams::write).
    pub fn write(&mut self, id: StreamId, data: &[u8]) -> Result<usize, StreamError> {
        self.ensure_open()?;
        let cap = self.send_buffer_cap();
        let n = self.streams.write(&mut self.pool, id, data, cap)?;
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
    pub fn reset(&mut self, id: StreamId, error: u64) -> Result<(), StreamError> {
        self.streams.reset(&mut self.pool, id, error)
    }

    /// The readable bytes of a stream, borrowed from the pool. Release them with [`consume`](Self::consume).
    pub fn read_chunk(&self, id: StreamId) -> Option<&[u8]> {
        self.streams.read_chunk(&self.pool, id)
    }

    /// Release `n` readable bytes of a stream; consuming 0 after the end was read lets the stream close. The clock
    /// and the round trip drive the autotuning of the receive window.
    ///
    /// # Errors
    /// The errors of [`Streams::consume`](crate::stream::Streams::consume).
    pub fn consume(&mut self, env: &mut Env<'_, P>, id: StreamId, n: usize) -> Result<RecvStatus, StreamError> {
        let srtt = self.rec.rtt().smoothed();
        self.streams.consume(&mut self.pool, id, n, env.now, srtt)
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
    pub fn send_datagram(&mut self, data: &[u8]) -> Result<(), DatagramError> {
        let max = self.max_datagram_size();
        self.life.app_written = true;
        self.dgrams.send_datagram(&mut self.pool, data, max)
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
                    *s = None;
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
    pub fn send_extension(&mut self, ty: u64, body: &[u8]) -> Result<(), ExtensionError> {
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
        self.ext
            .send_datagram(&mut self.pool, used, EXT_ENTRY_MAX)
            .map_err(|_| ExtensionError::Exhausted)
    }

    /// The oldest received datagram, borrowed; remove it with [`pop_datagram`](Self::pop_datagram).
    pub fn recv_datagram(&self) -> Option<&[u8]> {
        self.dgrams.recv_datagram(&self.pool)
    }

    /// Remove the datagram [`recv_datagram`](Self::recv_datagram) returned.
    pub fn pop_datagram(&mut self) {
        self.dgrams.release(&mut self.pool);
    }
}
