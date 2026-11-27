//! Datagrams out: the send queue, the ledger gate and batching across connections.
//!
//! Sessions that may have something to send wait on two queues, ordinary sessions first and broadcast sessions after
//! them (a broadcast session with a sub-session open still to leave counts as ordinary: it moves to the ordinary
//! queue as soon as the open is queued, so the open keeps its place). [`Endpoint::poll_transmit`] takes the first
//! session, asks its connection for a datagram, and sends it through the ledger gate: a datagram the ledger holds back
//! is dropped, which the connection treats as loss (the size probe is the exception: it is not built for a path whose
//! address the ledger holds). A datagram whose path has no address left is dropped and its connection is told the
//! path is lost (`path_lost`).
//! Between connections the endpoint batches for segmentation offload: after a datagram, the next sessions' datagrams
//! to the same destination of the same size follow in the same buffer, ending with a shorter one; a datagram for
//! another destination is kept for the next call. The session just served moves to the back of the queue its class
//! names after the send, so each gets a turn and a session whose open has left waits behind the ordinary ones.
//!
//! The endpoint's own answers, the rejects it sends to a first message without a session (see `stateless`), go first,
//! each already charged to the ledger.
//!
//! Invariants: one call returns one destination and a run of equal-size segments (the last may be shorter); no
//! datagram leaves without passing the ledger; the buffer never holds more than the configured number of segments;
//! the kept datagram is the only extra buffer and is sent first on the next call.

use core::net::SocketAddr;

use pinc_transport::conn::PathId;

use crate::endpoint::{MAX_DATAGRAM, StashMeta, env, ep_impl, lent};
use crate::slot::NIL;
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
            trace!(self, now, TxReject {
                dest: crate::rx::addr_key(&t.remote),
                len: t.len as u64,
                seg: t.segment_size as u64,
            });
            return Some(t);
        }
        loop {
            let (q, i) = self.dirty_front()?;
            let Some(slot) = self.slots.get_mut(i).filter(|s| s.m.in_use) else {
                trace!(self, now, TxGone { slot: i as u64 });
                self.dirty_pop(q);
                continue;
            };
            let Some(conn) = slot.conn.as_mut() else {
                trace!(self, now, TxGone { slot: i as u64 });
                self.dirty_pop(q);
                continue;
            };
            let mut env = env!(self, now);
            let Some(tx) = conn.poll_transmit(&mut env, &mut lent!(self), out) else {
                trace!(self, now, TxConn {
                    slot: i as u64,
                    room: out.len() as u64,
                    len: u64::MAX,
                    seg: u64::MAX,
                    dest: u64::MAX,
                });
                self.dirty_pop(q);
                let closing = self.run_deferred_close(i, now);
                self.settle_core(i, now, closing);
                continue;
            };
            #[cfg(feature = "trace")]
            let dest = self.trace_dest(tx.path);
            trace!(self, now, TxConn {
                slot: i as u64,
                room: out.len() as u64,
                len: tx.len as u64,
                seg: tx.segment_size as u64,
                dest,
            });
            let segments = tx.len.div_ceil(tx.segment_size.max(1));
            // The addresses are read before the settle: it may free the session (the CLOSE just built) and with it
            // the pair, and a datagram built for an address leaves for it.
            let dest = self.path_addrs(tx.path);
            self.note_sent(i, now, tx.path);
            self.dirty_rotate(q, now);
            self.settle_core(i, now, false);
            let Some((local, remote)) = dest else {
                self.counters.dropped_out += 1;
                trace!(self, now, TxDrop { slot: i as u64 });
                self.lose_path(i, now, tx.path);
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

    /// The remote of `path` as a trace number, `u64::MAX - 1` when the path has no address (cargo feature `trace`).
    #[cfg(feature = "trace")]
    fn trace_dest(&self, path: PathId) -> u64 {
        self.path_addrs(path)
            .map_or(u64::MAX - 1, |(_, remote)| crate::rx::addr_key(&remote))
    }

    /// The slots waiting on send queue `q` (0 ordinary, 1 broadcast), front first. At most `K` are given.
    #[cfg(feature = "trace")]
    pub fn trace_dirty(&self, q: usize) -> impl Iterator<Item = usize> + '_ {
        let head = self.dirty_head.get(q).copied().filter(|h| *h != NIL);
        core::iter::successors(head.map(|h| h as usize), move |&i| {
            self.slots
                .get(i)
                .map(|s| s.m.dirty_next)
                .filter(|n| *n != NIL)
                .map(|n| n as usize)
        })
        .take(K)
    }

    /// The datagram kept for the next call: the remote of its path (None when the path has no address any more), its
    /// length and its segment size.
    #[cfg(feature = "trace")]
    pub fn trace_stash(&self) -> Option<(Option<SocketAddr>, usize, usize)> {
        let m = self.stash_meta.as_ref()?;
        Some((Some(m.remote), m.len, m.segment))
    }

    /// Whether slot `i` is a broadcast session (its `gossip` flag), or None for a slot out of range.
    #[cfg(feature = "trace")]
    pub fn trace_gossip(&self, i: usize) -> Option<bool> {
        self.slots.get(i).map(|s| s.m.gossip)
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

    /// The host wants to send a datagram of `len` bytes to `remote` (the relay role): whether the ledger allows it; a
    /// refused one must not be sent.
    pub fn host_send(&mut self, now: u64, remote: SocketAddr, len: usize) -> bool {
        self.charge(now, remote, len as u64)
    }

    /// Ask the ledger to send `n` bytes to `remote` and record the call.
    pub(crate) fn charge(&mut self, now: u64, remote: SocketAddr, n: u64) -> bool {
        let allowed = self.ledger.allow_send(remote, n);
        trace!(self, now, LedgerTx {
            addr: crate::rx::addr_key(&remote),
            allowed: u64::from(allowed),
            rx: self.ledger.get(&remote).map_or(0, |e| e.rx),
            tx: self.ledger.get(&remote).map_or(0, |e| e.tx),
        });
        allowed
    }

    /// Pass `segments` datagrams totalling `len` bytes to `remote` through the ledger.
    fn gate(&mut self, now: u64, remote: SocketAddr, len: usize, segments: usize) -> bool {
        let n = (len + crate::ledger::DATAGRAM_OVERHEAD as usize * segments.saturating_sub(1)) as u64;
        let allowed = self.charge(now, remote, n);
        trace!(self, now, TxGate {
            dest: crate::rx::addr_key(&remote),
            len: len as u64,
            segments: segments as u64,
            n,
            allowed: u64::from(allowed),
        });
        if allowed {
            self.counters.datagrams_out += segments as u64;
        } else {
            self.counters.held_by_ledger += 1;
        }
        allowed
    }

    /// A datagram of session `i` on `path` found no address: no pair is held for the path. The connection is told
    /// the path is lost, so it leaves it for a usable path at once or as soon as one validates. A slot the settle
    /// freed meanwhile is left alone.
    fn lose_path(&mut self, i: usize, now: u64, path: PathId) {
        let Some(conn) = self.slots.get_mut(i).filter(|s| s.m.in_use).and_then(|s| s.conn.as_mut()) else {
            return;
        };
        // `Unknown`: the connection no longer tracks the path, so there is nothing to leave.
        if conn.path_lost(path).is_ok() {
            self.settle_core(i, now, false);
        }
    }

    /// Send the datagram kept from the last call.
    fn send_stash(&mut self, now: u64, out: &mut [u8], m: &StashMeta) -> Option<Transmit> {
        let (local, remote) = (m.local, m.remote);
        let (Some(src), Some(dst)) = (self.stash.get(..m.len), out.get_mut(..m.len)) else {
            self.counters.dropped_out += 1;
            trace!(self, now, TxDrop { slot: u64::MAX });
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
        debug_assert!(first.segment_size > 0, "a transmit has a segment size");
        let seg = first.segment_size;
        let mut segments = first.len.div_ceil(seg.max(1));
        while segments < limit && first.len == seg * segments && out.len() > first.len {
            let Some((q, j)) = self.dirty_front() else { return };
            let Some(slot) = self.slots.get_mut(j).filter(|s| s.m.in_use) else {
                trace!(self, now, TxGone { slot: j as u64 });
                self.dirty_pop(q);
                continue;
            };
            let Some(conn) = slot.conn.as_mut() else {
                trace!(self, now, TxGone { slot: j as u64 });
                self.dirty_pop(q);
                continue;
            };
            let room = (out.len() - first.len).min(MAX_DATAGRAM);
            let Some(window) = out.get_mut(first.len..first.len + room) else { return };
            let mut env = env!(self, now);
            let Some(tx) = conn.poll_transmit(&mut env, &mut lent!(self), window) else {
                trace!(self, now, TxConn {
                    slot: j as u64,
                    room: room as u64,
                    len: u64::MAX,
                    seg: u64::MAX,
                    dest: u64::MAX,
                });
                // A window shorter than a full datagram may be why there was none: the session stays for the next call.
                if room < MAX_DATAGRAM {
                    return;
                }
                self.dirty_pop(q);
                let closing = self.run_deferred_close(j, now);
                self.settle_core(j, now, closing);
                continue;
            };
            #[cfg(feature = "trace")]
            let dest = self.trace_dest(tx.path);
            trace!(self, now, TxConn {
                slot: j as u64,
                room: room as u64,
                len: tx.len as u64,
                seg: tx.segment_size as u64,
                dest,
            });
            let more = tx.len.div_ceil(tx.segment_size.max(1));
            let resolved = self.path_addrs(tx.path);
            self.note_sent(j, now, tx.path);
            self.dirty_rotate(q, now);
            self.settle_core(j, now, false);
            let Some((local, remote)) = resolved else {
                self.counters.dropped_out += 1;
                trace!(self, now, TxDrop { slot: j as u64 });
                self.lose_path(j, now, tx.path);
                continue;
            };
            let same_dest = (local, remote) == (first.local, first.remote);
            // A run of segments of the first's size, or one shorter datagram that ends the run, may join.
            let full = tx.segment_size == seg && tx.len % seg.max(1) == 0;
            let last = tx.segment_size == tx.len && tx.len < seg;
            if !same_dest || segments + more > limit || !(full || last || tx.segment_size == seg) {
                // Another destination or size: keep it for the next call.
                if let (Some(s), Some(w)) = (self.stash.get_mut(..tx.len), out.get(first.len..first.len + tx.len)) {
                    s.copy_from_slice(w);
                    self.stash_meta = Some(StashMeta {
                        local,
                        remote,
                        len: tx.len,
                        segment: tx.segment_size,
                    });
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

    /// The first session waiting to send: ordinary sessions before broadcast ones.
    pub(crate) fn dirty_front(&self) -> Option<(usize, usize)> {
        (0..2).find_map(|q| {
            let h = self.dirty_head.get(q).copied()?;
            (h != NIL).then_some((q, h as usize))
        })
    }

    /// Take the first session of queue `q` off it.
    pub(crate) fn dirty_pop(&mut self, q: usize) {
        let Some(h) = self.dirty_head.get(q).copied().filter(|h| *h != NIL) else { return };
        let Some(s) = self.slots.get_mut(h as usize) else { return };
        let next = s.m.dirty_next;
        s.m.dirty = 0;
        s.m.dirty_next = NIL;
        if let Some(x) = self.dirty_head.get_mut(q) {
            *x = next;
        }
        if next == NIL
            && let Some(t) = self.dirty_tail.get_mut(q)
        {
            *t = NIL;
        }
    }

    /// Move the first session of queue `q` to the end of the queue its class names now, so the others get a turn.
    pub(crate) fn dirty_rotate(&mut self, q: usize, now: u64) {
        let Some(h) = self.dirty_head.get(q).copied().filter(|h| *h != NIL) else { return };
        if self.dirty_head.get(q) == self.dirty_tail.get(q)
            && self.slots.get(h as usize).is_some_and(|s| s.m.send_queue() == q)
        {
            return;
        }
        self.dirty_pop(q);
        self.mark_dirty(h as usize, now);
    }

    /// Move session `i` from the broadcast queue to the back of the ordinary one when its class became ordinary (a
    /// sub-session open was queued in it, or it stopped being a broadcast session). A session that became broadcast
    /// moves at its next turn instead (`dirty_rotate`).
    // vertexia: walks the broadcast queue (one step per waiting broadcast session), per open or flag change and
    // never per packet; a previous-link per slot if a node waits on more than a few hundred broadcast sessions.
    pub(crate) fn dirty_promote(&mut self, i: usize, now: u64) {
        let Ok(idx) = u32::try_from(i) else { return };
        let Some(s) = self.slots.get(i) else { return };
        if s.m.dirty != 2 || s.m.send_queue() != 0 {
            return;
        }
        let next = s.m.dirty_next;
        let mut prev = NIL;
        let mut cur = self.dirty_head.get(1).copied().unwrap_or(NIL);
        for _ in 0..self.slots.len() {
            if cur == idx || cur == NIL {
                break;
            }
            prev = cur;
            cur = self.slots.get(cur as usize).map_or(NIL, |s| s.m.dirty_next);
        }
        if cur != idx {
            return;
        }
        match self.slots.get_mut(prev as usize) {
            Some(p) => p.m.dirty_next = next,
            None => {
                if let Some(h) = self.dirty_head.get_mut(1) {
                    *h = next;
                }
            }
        }
        if self.dirty_tail.get(1) == Some(&idx)
            && let Some(t) = self.dirty_tail.get_mut(1)
        {
            *t = prev;
        }
        if let Some(s) = self.slots.get_mut(i) {
            s.m.dirty = 0;
            s.m.dirty_next = NIL;
        }
        self.mark_dirty(i, now);
    }
}
