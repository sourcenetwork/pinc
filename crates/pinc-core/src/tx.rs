//! Datagrams out: the send queue, the ledger gate and batching across connections.
//!
//! Sessions that may have something to send wait on two queues, ordinary sessions first and broadcast sessions after
//! them (a broadcast session with a sub-session open still to leave counts as ordinary, so the open keeps its
//! place). [`Endpoint::poll_transmit`] takes the first session, asks its connection for a datagram, and sends it
//! through the ledger gate: a datagram the ledger holds back is dropped, which the connection treats as loss (the size
//! probe is the exception: it is not built for a path whose address the ledger holds).
//! Between connections the endpoint batches for segmentation offload: after a datagram, the next sessions' datagrams
//! to the same destination of the same size follow in the same buffer, ending with a shorter one; a datagram for another
//! destination is kept for the next call. The session just served moves to the back of its queue, so each gets a turn.
//!
//! The endpoint's own answers, the rejects it sends to a first message without a session (see `stateless`), go first,
//! each already charged to the ledger.
//!
//! Invariants: one call returns one destination and a run of equal-size segments (the last may be shorter); no
//! datagram leaves without passing the ledger; the buffer never holds more than the configured number of segments;
//! the kept datagram is the only extra buffer and is sent first on the next call.

use core::net::SocketAddr;

use pinc_transport::conn::PathId;

use crate::endpoint::{MAX_DATAGRAM, StashMeta, env, ep_impl};
use crate::trace::trace;

/// A datagram, or a batch of equal-size datagrams, for the host to send.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Transmit {
    /// The local address to send from.
    pub local: SocketAddr,
    /// The address to send to.
    pub remote: SocketAddr,
    /// The bytes written to the buffer: one datagram, or several of `segment_size` bytes (the last may be shorter).
    pub len: usize,
    /// The size of each datagram; equal to `len` for one datagram.
    pub segment_size: usize,
}

ep_impl! {
    /// Write the next datagram, or batch of datagrams, into `out`. Returns `None` when nothing waits to leave; call it
    /// again after every input and timeout until it does.
    pub fn poll_transmit(&mut self, now: u64, out: &mut [u8]) -> Option<Transmit> {
        if let Some(m) = self.stash_meta.take()
            && let Some(t) = self.send_stash(now, out, &m)
        {
            return Some(t);
        }
        if !self.rejects.is_empty()
            && let Some(t) = self.send_reject(out)
        {
            return Some(t);
        }
        loop {
            let (q, i) = self.dirty_front()?;
            let Some(slot) = self.slots.get_mut(i).filter(|s| s.m.in_use) else {
                self.dirty_pop(q);
                continue;
            };
            let Some(conn) = slot.conn.as_mut() else {
                self.dirty_pop(q);
                continue;
            };
            let mut env = env!(self, now);
            let Some(tx) = conn.poll_transmit(&mut env, out) else {
                self.dirty_pop(q);
                let closing = self.run_deferred_close(i, now);
                self.settle_core(i, now, closing);
                continue;
            };
            let segments = tx.len.div_ceil(tx.segment_size.max(1));
            self.note_sent(i, now, tx.path);
            self.dirty_rotate(q);
            self.settle_core(i, now, false);
            let Some((local, remote)) = self.path_addrs(tx.path) else {
                self.counters.dropped_out += 1;
                continue;
            };
            if !self.gate(now, remote, tx.len, segments) {
                continue;
            }
            let mut first = Transmit { local, remote, len: tx.len, segment_size: tx.segment_size };
            self.batch(now, out, &mut first);
            return Some(first);
        }
    }

    /// Whether [`poll_transmit`](Self::poll_transmit) has anything to write or to do: a datagram kept from the last
    /// call, a reject waiting to be sent, or a session that may have something to send. When it says no, a call
    /// returns `None` and changes nothing.
    pub fn transmit_waiting(&self) -> bool {
        self.stash_meta.is_some() || !self.rejects.is_empty() || self.dirty_front().is_some()
    }

    /// Record that session `i` produced a datagram on `path`.
    fn note_sent(&mut self, i: usize, now: u64, path: PathId) {
        if let Some(s) = self.slots.get_mut(i) {
            s.m.last_tx = now;
            s.m.ctrl_pending = false;
            if let Some(p) = s.m.stamp(path) {
                p.tx = now;
            }
        }
    }

    /// Pass `segments` datagrams totalling `len` bytes to `remote` through the ledger.
    fn gate(&mut self, now: u64, remote: SocketAddr, len: usize, segments: usize) -> bool {
        let n = (len + crate::ledger::DATAGRAM_OVERHEAD as usize * segments.saturating_sub(1)) as u64;
        let allowed = self.ledger.allow_send(remote, n);
        trace!(self, now, LedgerTx {
            addr: crate::rx::addr_key(&remote),
            allowed: u64::from(allowed),
            rx: self.ledger.get(&remote).map_or(0, |e| e.rx),
            tx: self.ledger.get(&remote).map_or(0, |e| e.tx),
        });
        if allowed {
            self.counters.datagrams_out += segments as u64;
        } else {
            self.counters.held_by_ledger += 1;
        }
        allowed
    }

    /// Send the datagram kept from the last call.
    fn send_stash(&mut self, now: u64, out: &mut [u8], m: &StashMeta) -> Option<Transmit> {
        let Some((local, remote)) = self.path_addrs(m.path) else {
            self.counters.dropped_out += 1;
            return None;
        };
        let (Some(src), Some(dst)) = (self.stash.get(..m.len), out.get_mut(..m.len)) else {
            self.counters.dropped_out += 1;
            return None;
        };
        dst.copy_from_slice(src);
        let segments = m.len.div_ceil(m.segment.max(1));
        if !self.gate(now, remote, m.len, segments) {
            return None;
        }
        Some(Transmit { local, remote, len: m.len, segment_size: m.segment })
    }

    /// Append datagrams of other sessions to `first` while they go to the same destination at the same size.
    fn batch(&mut self, now: u64, out: &mut [u8], first: &mut Transmit) {
        let limit = self.cfg.conn.max_gso.max(1);
        let seg = first.segment_size;
        let mut segments = first.len.div_ceil(seg.max(1));
        while segments < limit && first.len == seg * segments && out.len() > first.len {
            let Some((q, j)) = self.dirty_front() else { return };
            let Some(slot) = self.slots.get_mut(j).filter(|s| s.m.in_use) else {
                self.dirty_pop(q);
                continue;
            };
            let Some(conn) = slot.conn.as_mut() else {
                self.dirty_pop(q);
                continue;
            };
            let room = (out.len() - first.len).min(MAX_DATAGRAM);
            let Some(window) = out.get_mut(first.len..first.len + room) else { return };
            let mut env = env!(self, now);
            let Some(tx) = conn.poll_transmit(&mut env, window) else {
                // A window shorter than a full datagram may be why there was none: the session stays for the next call.
                if room < MAX_DATAGRAM {
                    return;
                }
                self.dirty_pop(q);
                let closing = self.run_deferred_close(j, now);
                self.settle_core(j, now, closing);
                continue;
            };
            let more = tx.len.div_ceil(tx.segment_size.max(1));
            self.note_sent(j, now, tx.path);
            self.dirty_rotate(q);
            self.settle_core(j, now, false);
            let same_dest = self.path_addrs(tx.path) == Some((first.local, first.remote));
            // A run of segments of the first's size, or one shorter datagram that ends the run, may join.
            let full = tx.segment_size == seg && tx.len % seg == 0;
            let last = tx.segment_size == tx.len && tx.len < seg;
            if !same_dest || segments + more > limit || !(full || last || tx.segment_size == seg) {
                // Another destination or size: keep it for the next call.
                if let (Some(s), Some(w)) = (self.stash.get_mut(..tx.len), out.get(first.len..first.len + tx.len)) {
                    s.copy_from_slice(w);
                    self.stash_meta = Some(StashMeta { path: tx.path, len: tx.len, segment: tx.segment_size });
                }
                return;
            }
            if !self.gate(now, first.remote, tx.len, more) {
                continue;
            }
            first.len += tx.len;
            segments += more;
            if !full {
                return;
            }
        }
    }
}
