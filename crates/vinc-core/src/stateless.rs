//! Answers without a session: a first handshake message that the responder would only reject, a resumption Hello whose
//! ticket does not open or a short Initial whose prekey this node does not hold, is answered by the endpoint with the
//! reject and nothing is kept for the sender, so it takes no half-open slot.
//!
//! The reject is the message the responder would have sent, in a datagram of its own. It is bounded like every answer
//! to an address not yet heard from: the datagram is charged to the amplification ledger when it is queued, and when
//! the ledger refuses it nothing is queued or sent. The queue holds at most [`REJECT_QUEUE`] datagrams, built whole when
//! queued; one that finds it full is dropped without a charge.
//!
//! Invariants: a queued datagram has been charged to the ledger exactly once; nothing here allocates; the queue never
//! holds more than [`REJECT_QUEUE`] datagrams.

use core::net::SocketAddr;

use vinc_security::ConnId;
use vinc_security::message::REJECT_LEN;
use vinc_transport::packet::handshake_packet;

use crate::endpoint::ep_impl;
use crate::trace::trace;
use crate::tx::Transmit;

/// The most rejects waiting to be sent.
pub(crate) const REJECT_QUEUE: usize = 16;
/// The longest datagram of a reject: the long header with two 20-byte ids, the message length and offset, the message.
const REJECT_DATAGRAM_MAX: usize = 1 + 1 + 2 * (1 + 20) + 2 + 2 + REJECT_LEN;

/// One reject, built whole, and where it goes.
#[derive(Debug, Clone, Copy)]
struct Pending {
    local: SocketAddr,
    remote: SocketAddr,
    len: usize,
    bytes: [u8; REJECT_DATAGRAM_MAX],
}

/// The rejects waiting to be sent, oldest first.
#[derive(Debug)]
pub(crate) struct Rejects {
    ring: [Option<Pending>; REJECT_QUEUE],
    head: usize,
    len: usize,
}

impl Rejects {
    pub(crate) const fn new() -> Self {
        Self {
            ring: [None; REJECT_QUEUE],
            head: 0,
            len: 0,
        }
    }

    pub(crate) const fn is_empty(&self) -> bool {
        self.len == 0
    }

    const fn is_full(&self) -> bool {
        self.len == REJECT_QUEUE
    }

    fn push(&mut self, p: Pending) {
        let at = (self.head + self.len) % REJECT_QUEUE;
        if let Some(cell) = self.ring.get_mut(at) {
            *cell = Some(p);
            self.len += 1;
        }
    }

    fn pop(&mut self) -> Option<Pending> {
        let p = self.ring.get_mut(self.head)?.take()?;
        self.head = (self.head + 1) % REJECT_QUEUE;
        self.len -= 1;
        Some(p)
    }
}

ep_impl! {
    /// Answer a first message from `remote` with `message`, a reject, without a session: to the id the dialer chose
    /// (`scid`), from the id it dialed (`odcid`). Counted in [`NodeStats`](crate::NodeStats) as sent, or refused when
    /// the ledger holds the answer back; a full queue drops it uncharged.
    pub(crate) fn reject_stateless(
        &mut self,
        now: u64,
        local: SocketAddr,
        remote: SocketAddr,
        (odcid, scid): (ConnId, ConnId),
        message: &[u8; REJECT_LEN],
    ) {
        let mut bytes = [0u8; REJECT_DATAGRAM_MAX];
        let Some(len) = handshake_packet(&mut bytes, scid, odcid, REJECT_LEN, 0, message) else {
            self.counters.dropped_in += 1;
            return;
        };
        if self.rejects.is_full() {
            self.counters.dropped_in += 1;
            return;
        }
        let allowed = self.ledger.allow_send(remote, len as u64);
        trace!(self, now, LedgerTx {
            addr: crate::rx::addr_key(&remote),
            allowed: u64::from(allowed),
            rx: self.ledger.get(&remote).map_or(0, |e| e.rx),
            tx: self.ledger.get(&remote).map_or(0, |e| e.tx),
        });
        if !allowed {
            self.counters.stateless_refused += 1;
            return;
        }
        self.counters.stateless_rejects += 1;
        self.rejects.push(Pending { local, remote, len, bytes });
    }

    /// Write the oldest queued reject into `out`, if any.
    pub(crate) fn send_reject(&mut self, out: &mut [u8]) -> Option<Transmit> {
        let p = self.rejects.pop()?;
        let (Some(dst), Some(src)) = (out.get_mut(..p.len), p.bytes.get(..p.len)) else {
            self.counters.dropped_out += 1;
            return None;
        };
        dst.copy_from_slice(src);
        self.counters.datagrams_out += 1;
        Some(Transmit { local: p.local, remote: p.remote, len: p.len, segment_size: p.len })
    }
}
