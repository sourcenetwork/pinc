//! The application calls: streams, datagrams and events.

use vinc_crypto::Provider;
use vinc_security::Env;
use vinc_wire::varint;

use super::event::{Ev, Event};
use super::{Connection, MIN_MTU, Phase};
use crate::stream::datagram::DatagramError;
use crate::stream::{RecvStatus, StreamError, StreamId, StreamSource};

/// A DATAGRAM frame spends its type and a two-byte length besides the data.
const DATAGRAM_FRAME_OVERHEAD: usize = 3;
/// The largest extension frame, type included, that [`send_extension`](Connection::send_extension) queues.
const EXT_ENTRY_MAX: usize = 9300;
/// A short packet spends its first byte, a 4-byte packet number and the 16-byte tag besides the connection id.
const SHORT_PACKET_FIXED: usize = 1 + 4 + 16;

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
                Ev::Connected(resumed) => Event::Connected { resumed },
                Ev::Opened(id) => Event::StreamOpened(id),
                Ev::Readable(id) => Event::StreamReadable(id),
                Ev::Writable(id) => Event::StreamWritable(id),
                Ev::Reset(id, error) => Event::StreamReset { id, error },
                Ev::Stopped(id, error) => Event::StreamStopped { id, error },
                Ev::Datagram => Event::DatagramReceived,
                Ev::PathValidated(p) => Event::PathValidated(p),
                Ev::PathFailed(p) => Event::PathFailed(p),
                Ev::PeerAsleep => Event::PeerAsleep,
                Ev::PeerAwake => Event::PeerAwake,
                Ev::WakeUnanswered => Event::WakeUnanswered,
                Ev::Tickets(b) => Event::TicketsReceived(b),
                Ev::Ready => Event::Ready,
                Ev::StatelessReset => Event::StatelessReset,
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

    /// Buffer bytes for sending on a stream; returns how many were accepted (0 when the peer's credit, the pool or
    /// the stream's buffer is full: try again after [`Event::StreamWritable`] or
    /// when acknowledgements free room). Every write, finish and reset needs no clock, so none takes an `Env`.
    ///
    /// # Errors
    /// The errors of [`Streams::write`](crate::stream::Streams::write).
    pub fn write(&mut self, id: StreamId, data: &[u8]) -> Result<usize, StreamError> {
        self.ensure_open()?;
        self.streams.write(&mut self.pool, id, data)
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

    /// Ask the peer to stop sending on a stream.
    ///
    /// # Errors
    /// The errors of [`Streams::stop_sending`](crate::stream::Streams::stop_sending).
    pub fn stop(&mut self, id: StreamId, error: u64) -> Result<(), StreamError> {
        self.streams.stop_sending(&mut self.pool, id, error)
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
        let peer = usize::from(self.peer_credit.max_datagram);
        mtu.saturating_sub(SHORT_PACKET_FIXED + self.cfg.cid_len + DATAGRAM_FRAME_OVERHEAD)
            .min(peer.saturating_sub(DATAGRAM_FRAME_OVERHEAD))
    }

    /// Queue an unreliable datagram. The oldest queued datagram is dropped if the queue is full.
    ///
    /// # Errors
    /// [`DatagramError::TooLarge`] above [`max_datagram_size`](Self::max_datagram_size), or
    /// [`DatagramError::Exhausted`] when the pool is empty.
    pub fn send_datagram(&mut self, data: &[u8]) -> Result<(), DatagramError> {
        let max = self.max_datagram_size();
        self.dgrams.send_datagram(&mut self.pool, data, max)
    }

    /// Queue an extension frame (type 0x40 and up) for the endpoint layer: it is sent once, unreliably, ahead of
    /// stream data. The queue is bounded and drops its oldest entry when full.
    ///
    /// vertexia: no retransmission, so a lost extension frame is lost; an endpoint that needs delivery carries its
    /// messages on a stream, and a retransmitting queue would key its entries through the control table.
    ///
    /// # Errors
    /// [`DatagramError::TooLarge`] if the frame does not fit one packet or `ty` is below 0x40, and
    /// [`DatagramError::Exhausted`] when the pool is empty.
    pub fn send_extension(&mut self, ty: u64, body: &[u8]) -> Result<(), DatagramError> {
        let max = self.max_datagram_size();
        if ty < crate::frame::EXTENSION_BASE || body.len() + 9 > max {
            return Err(DatagramError::TooLarge { max_size: max });
        }
        let mut buf = [0u8; 9];
        let head = varint::encode(ty, &mut buf).map_err(|_| DatagramError::TooLarge { max_size: max })?;
        // The queue holds one contiguous entry: the type, then the body.
        let mut entry = [0u8; EXT_ENTRY_MAX];
        let used = entry.get_mut(..head + body.len()).ok_or(DatagramError::TooLarge { max_size: max })?;
        let (h, b) = used.split_at_mut(head);
        h.copy_from_slice(buf.get(..head).unwrap_or_default());
        b.copy_from_slice(body);
        let used = &*used;
        self.ext.send_datagram(&mut self.pool, used, max + 9)
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
