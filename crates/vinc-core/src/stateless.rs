//! Answers without a session: a first handshake message that the responder would only reject, a resumption Hello whose
//! ticket does not open or a short Initial whose prekey this node does not hold, is answered by the endpoint with the
//! reject and nothing is kept for the sender, so it takes no half-open slot.
//!
//! The reject is the message the responder would have sent, in a datagram of its own. It is bounded like every answer
//! to an address not yet heard from: the datagram is charged to the amplification ledger when it is queued, and when
//! the ledger refuses it nothing is queued or sent and `stateless_refused` counts it. The queue holds at most
//! [`REJECT_QUEUE`] datagrams, built whole when queued; one that finds it full is dropped without a charge and counted
//! only in `dropped_in`. A reject is counted as sent (`stateless_rejects`, `datagrams_out`) when it is written to the
//! caller's buffer; if that buffer is shorter than the datagram, the reject is lost and counted once in `dropped_out`,
//! the same as a datagram kept by a session, and its charge to the ledger is not given back.
//!
//! Invariants: a queued datagram has been charged to the ledger exactly once and counted as sent at most once; nothing
//! here allocates; the queue never holds more than [`REJECT_QUEUE`] datagrams.

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
        // Asked on every transmit poll: an empty queue costs one test, not the move of a cell.
        if self.len == 0 {
            return None;
        }
        let p = self.ring.get_mut(self.head)?.take()?;
        self.head = (self.head + 1) % REJECT_QUEUE;
        self.len -= 1;
        Some(p)
    }
}

ep_impl! {
    /// Answer a first message from `remote` with `message`, a reject, without a session: to the id the dialer chose
    /// (`scid`), from the id it dialed (`odcid`). Queued for [`send_reject`](Self::send_reject), which counts it as
    /// sent; counted as refused and thrown away when the ledger will not let this node answer that address; a full
    /// queue drops it uncharged and counts it in `dropped_in` only.
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
        self.rejects.push(Pending { local, remote, len, bytes });
    }

    /// Write the oldest queued reject into `out`, if any, and count it as sent. When `out` is shorter than the reject
    /// the reject is lost and counted in `dropped_out` instead. Out of line and cold: the transmit poll of an
    /// established session tests the queue and calls this only when a reject waits.
    #[cold]
    #[inline(never)]
    pub(crate) fn send_reject(&mut self, out: &mut [u8]) -> Option<Transmit> {
        let p = self.rejects.pop()?;
        let (Some(dst), Some(src)) = (out.get_mut(..p.len), p.bytes.get(..p.len)) else {
            self.counters.dropped_out += 1;
            return None;
        };
        dst.copy_from_slice(src);
        self.counters.stateless_rejects += 1;
        self.counters.datagrams_out += 1;
        Some(Transmit { local: p.local, remote: p.remote, len: p.len, segment_size: p.len })
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "test assertions")]
mod tests {
    use vinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
    use vinc_security::{KeyHandle, LocalIdentity};
    use vinc_transport::conn::{Resources, Tables};
    use vinc_transport::recovery::LossEstimate;
    use vinc_transport::stream::pool::{BufferPool, RawChunk};
    use vinc_transport::stream::{self, NoSource, Streams};

    use super::*;
    use crate::endpoint::{Endpoint, EndpointConfig};
    use crate::slot::Slot;

    type Ep<'s> = Endpoint<'s, 's, Software, NoSource, 1, 2, 16, 1, 1, 10, 1, 1, 1>;

    fn addr(i: u8) -> SocketAddr {
        SocketAddr::from(([10, 0, 0, i], 9))
    }

    fn ids() -> (ConnId, ConnId) {
        (ConnId::new(&[1; 8]).unwrap(), ConnId::new(&[2; 4]).unwrap())
    }

    /// An address the ledger has heard too little from to be answered. No endpoint state reaches this through
    /// `handle_datagram` (a first message is at least 93 bytes and the reject's datagram, with its overhead, is under
    /// three times that), so the ledger's bound is exercised here directly.
    #[test]
    fn a_reject_the_ledger_will_not_pay_for_is_counted_refused_and_never_sent() {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[7u8; 32]).unwrap();
        let id = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
        let mut slab: [RawChunk; 0] = [];
        let pool = BufferPool::from_slab(&mut slab);
        let mut streams = Streams::<NoSource, 1, 2>::new(&stream::Config::new(false), &pool);
        let loss = LossEstimate::new();
        let mut slots = [Slot::<Software, NoSource, 1, 2, 16, 1>::new(Resources {
            pool,
            streams: (&mut streams).into(),
            loss: (&loss).into(),
            tables: Tables::new(),
        })];
        let mut ep: Ep<'_> = Endpoint::new(0, Software, Drbg::new(&[3; 32]), id, EndpointConfig::new(5), &mut slots);
        let msg = [0u8; REJECT_LEN];
        // 10 bytes heard: three times that is under the reject's 65 bytes plus the 28 of overhead
        assert!(ep.ledger.on_receive(addr(1), 10));
        ep.reject_stateless(0, addr(9), addr(1), ids(), &msg);
        let ns = ep.node_stats();
        assert_eq!((ns.stateless_refused, ns.dropped_in), (1, 0), "{ns:?}");
        let mut out = [0u8; 1200];
        assert!(ep.send_reject(&mut out).is_none(), "a refused reject was queued");
        let ns = ep.node_stats();
        assert_eq!(
            (ns.stateless_rejects, ns.datagrams_out, ns.dropped_out),
            (0, 0, 0),
            "{ns:?}"
        );
        // an address heard from enough is answered, once, and counted when written
        assert!(ep.ledger.on_receive(addr(2), 93));
        ep.reject_stateless(0, addr(9), addr(2), ids(), &msg);
        assert!(ep.send_reject(&mut out).is_some());
        let ns = ep.node_stats();
        assert_eq!((ns.stateless_rejects, ns.stateless_refused), (1, 1), "{ns:?}");
    }
}
