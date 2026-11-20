//! One accepted byte stream: its protected carrier, its WebSocket framing, and the bytes queued for it.
//!
//! Invariants: the queue of a stream and the write in flight together hold whole sealed units and never more than the
//! backlog limit (plus one unit and one pong); a read or write buffer is owned by at most one operation; the buffers of
//! a stream are allocated once and reused.

use alloc::boxed::Box;
use alloc::rc::Rc;
use alloc::vec::Vec;

use pinc_connect::carrier::session::ProtectedCarrier;
use pinc_connect::carrier::ws::{self, Decoder, Opcode, Role};
use pinc_connect::relay::SessionId;
use pinc_crypto::{NodeId, Software};

use super::stats::Closed;
use crate::carrier::CarrierKind;

/// The bytes one read may return.
pub(crate) const READ_LEN: usize = 32 * 1024;

pub(crate) struct Conn<S> {
    pub(crate) stream: Rc<S>,
    /// A number no other stream of this relay ever had; completions carry it with the slot.
    pub(crate) id: u64,
    /// The slot is on the list of streams with an operation to start.
    pub(crate) queued: bool,
    pub(crate) kind: CarrierKind,
    pub(crate) carrier: Box<ProtectedCarrier<Software>>,
    pub(crate) node: Option<NodeId>,
    pub(crate) session: Option<SessionId>,
    /// The stream is a session with a peer relay, not a member.
    pub(crate) peer: bool,
    /// This relay opened the stream (to a peer relay), and its WebSocket frames are masked.
    pub(crate) dialer: bool,
    /// The peer slot this stream dials.
    pub(crate) dial: Option<usize>,
    /// Records still to send to the peer relay on this stream, last first.
    pub(crate) sync: Vec<NodeId>,
    /// When the handshake must have finished.
    pub(crate) deadline: u64,
    pub(crate) last_rx: u64,
    pub(crate) dying: Option<Closed>,
    pub(crate) dec: Decoder,
    pub(crate) ws_in: Vec<u8>,
    rbuf: Option<Vec<u8>>,
    q: Vec<u8>,
    qpos: usize,
    ctl: Vec<u8>,
    wbuf: Option<Vec<u8>>,
    woff: usize,
    /// The bytes of the write buffer not yet written: they stay part of the backlog while the write is in flight.
    unsent: usize,
}

impl<S> Conn<S> {
    pub(crate) fn new(stream: S, kind: CarrierKind, carrier: Box<ProtectedCarrier<Software>>, deadline: u64) -> Self {
        Self {
            stream: Rc::new(stream),
            id: 0,
            queued: false,
            kind,
            carrier,
            node: None,
            session: None,
            peer: false,
            dialer: false,
            dial: None,
            sync: Vec::new(),
            deadline,
            last_rx: 0,
            dying: None,
            dec: Decoder::new(Role::Client),
            ws_in: Vec::new(),
            rbuf: Some(alloc::vec![0; READ_LEN]),
            q: Vec::new(),
            qpos: 0,
            ctl: Vec::new(),
            wbuf: Some(Vec::new()),
            woff: 0,
            unsent: 0,
        }
    }

    /// The read buffer, if no read is in flight and the stream is still wanted.
    pub(crate) fn take_read(&mut self) -> Option<Vec<u8>> {
        if self.dying.is_some() {
            return None;
        }
        self.rbuf.take()
    }

    pub(crate) fn put_read(&mut self, buf: Vec<u8>) {
        self.rbuf = Some(buf);
    }

    /// Queue sealed bytes (whole units); false if the queue and the write in flight would pass `limit` bytes.
    pub(crate) fn push(&mut self, wire: &[u8], limit: usize) -> bool {
        if self.backlog() + wire.len() > limit {
            return false;
        }
        self.q.extend_from_slice(wire);
        true
    }

    /// Bytes queued and not yet written, in the queue or in the write in flight.
    pub(crate) fn backlog(&self) -> usize {
        self.q.len() - self.qpos + self.unsent
    }

    /// Queue the answer to a WebSocket ping. It replaces an answer still waiting: a peer may answer only the most
    /// recent ping (RFC 6455, 5.5.3), so the answers waiting are one frame, whatever the peer sends.
    pub(crate) fn push_pong(&mut self, frame: &[u8]) {
        self.ctl.clear();
        self.ctl.extend_from_slice(frame);
    }

    /// The next bytes to write and the offset to write from, if there are any and no write is in flight.
    pub(crate) fn take_write(&mut self, mask: Option<[u8; 4]>) -> Option<(Vec<u8>, usize)> {
        if self.dying.is_some() {
            return None;
        }
        let mut buf = self.wbuf.take()?;
        if self.woff < buf.len() {
            self.unsent = buf.len() - self.woff;
            return Some((buf, self.woff));
        }
        buf.clear();
        self.woff = 0;
        if self.fill(&mut buf, mask) {
            self.unsent = buf.len();
            Some((buf, 0))
        } else {
            self.wbuf = Some(buf);
            None
        }
    }

    /// A write finished: `n` bytes of `buf` went out.
    pub(crate) fn wrote(&mut self, buf: Vec<u8>, n: usize) {
        self.woff += n;
        self.unsent = buf.len().saturating_sub(self.woff);
        self.wbuf = Some(buf);
    }

    fn fill(&mut self, buf: &mut Vec<u8>, mask: Option<[u8; 4]>) -> bool {
        if !self.ctl.is_empty() {
            buf.append(&mut self.ctl);
            return true;
        }
        let Some(rest) = self.q.get(self.qpos..).filter(|r| !r.is_empty()) else {
            return false;
        };
        if self.kind == CarrierKind::Tcp {
            buf.extend_from_slice(rest);
            self.qpos = self.q.len();
        } else {
            let Some(&[a, b]) = rest.first_chunk::<2>() else {
                return false;
            };
            let n = 2 + usize::from(u16::from_be_bytes([a, b]));
            let Some(unit) = rest.get(..n) else {
                return false;
            };
            if self.kind == CarrierKind::Ws {
                buf.resize(n + ws::MAX_HEADER, 0);
                let Ok(used) = ws::encode(Opcode::Binary, unit, mask, buf) else {
                    return false;
                };
                buf.truncate(used);
            } else {
                buf.extend_from_slice(unit);
            }
            self.qpos += n;
        }
        if self.qpos == self.q.len() {
            self.q.clear();
            self.qpos = 0;
        }
        true
    }
}
