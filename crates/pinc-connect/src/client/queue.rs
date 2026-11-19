//! The packets a relay's carrier holds while it is not open.
//!
//! A packet for a peer through a carrier that is still dialing waits here, oldest first, and leaves in order when
//! the carrier opens. The queue holds up to [`QUEUED`] packets and [`QUEUE_BYTES`] bytes: the bytes are what runs
//! out, so the packets share one inline buffer instead of each owning a full-size slot. A full queue drops its
//! oldest packet (recovery resends it). On a slow link the packets that waited out a long dial are mostly stale
//! copies, so [`HeldQueue::retain`] lets the caller thin the queue before it is drained.
//!
//! Invariants: the packets are contiguous in `data` in queue order; `len` never exceeds [`QUEUE_BYTES`] and the
//! count never exceeds [`QUEUED`]; nothing allocates.

use pinc_crypto::NodeId;

use crate::carrier::frame::MAX_PACKET_LEN;

/// The most packets held for a carrier.
pub const QUEUED: usize = 512;
/// The most bytes held for a carrier.
// vertexia: a fixed byte budget per carrier; 512 full-size packets would take three quarters of a megabyte per relay
// inline, and the layer is built on the stack. Upgrade: size it from the node's memory budget.
pub const QUEUE_BYTES: usize = 48 * 1024;

#[derive(Debug, Clone, Copy)]
struct Ent {
    dst: NodeId,
    off: usize,
    len: usize,
}

/// A held packet.
#[derive(Debug, Clone, Copy)]
pub struct Held<'a> {
    /// The peer it is for.
    pub dst: NodeId,
    /// The packet.
    pub packet: &'a [u8],
}

/// The packets waiting for one carrier.
pub struct HeldQueue {
    ents: [Option<Ent>; QUEUED],
    head: usize,
    n: usize,
    data: [u8; QUEUE_BYTES],
}

impl Default for HeldQueue {
    fn default() -> Self {
        Self::new()
    }
}

impl HeldQueue {
    /// An empty queue.
    pub const fn new() -> Self {
        Self {
            ents: [None; QUEUED],
            head: 0,
            n: 0,
            data: [0; QUEUE_BYTES],
        }
    }

    /// How many packets wait.
    pub const fn len(&self) -> usize {
        self.n
    }

    /// Whether none waits.
    pub const fn is_empty(&self) -> bool {
        self.n == 0
    }

    fn ent(&self, i: usize) -> Option<Ent> {
        self.ents.get(self.head.checked_add(i)?).copied().flatten()
    }

    fn used(&self) -> usize {
        match self.n.checked_sub(1) {
            Some(last) => self.ent(last).map_or(0, |e| e.off + e.len),
            None => 0,
        }
    }

    /// Move the live packets to the start of the buffers.
    fn compact(&mut self) {
        let Some(first) = self.ent(0) else {
            self.head = 0;
            return;
        };
        let end = self.used();
        self.data.copy_within(first.off..end, 0);
        for i in 0..self.n {
            let e = self.ent(i).map(|e| Ent {
                off: e.off - first.off,
                ..e
            });
            if let Some(s) = self.ents.get_mut(i) {
                *s = e;
            }
        }
        for s in self.ents.iter_mut().skip(self.n) {
            *s = None;
        }
        self.head = 0;
    }

    /// Drop the oldest packet.
    fn drop_front(&mut self) {
        if self.n == 0 {
            return;
        }
        if let Some(s) = self.ents.get_mut(self.head) {
            *s = None;
        }
        self.head += 1;
        self.n -= 1;
        if self.n == 0 {
            self.head = 0;
        }
    }

    /// Queue `packet` for `dst`. Returns how many older packets were dropped to make room (0 or more); a packet
    /// longer than [`MAX_PACKET_LEN`] is refused and counts as one drop.
    pub fn push(&mut self, dst: &NodeId, packet: &[u8]) -> usize {
        if packet.len() > MAX_PACKET_LEN {
            return 1;
        }
        let mut dropped = 0;
        while self.n > 0
            && (self.n >= QUEUED
                || self.used().saturating_sub(self.ent(0).map_or(0, |e| e.off)) + packet.len() > QUEUE_BYTES)
        {
            self.drop_front();
            dropped += 1;
        }
        if self.head + self.n >= QUEUED || self.used() + packet.len() > QUEUE_BYTES {
            self.compact();
        }
        let off = self.used();
        let slot = self.head + self.n;
        if let (Some(d), Some(s)) = (self.data.get_mut(off..off + packet.len()), self.ents.get_mut(slot)) {
            d.copy_from_slice(packet);
            *s = Some(Ent {
                dst: *dst,
                off,
                len: packet.len(),
            });
            self.n += 1;
        }
        dropped
    }

    /// Take the oldest packet, copying it into `out`; returns its destination and length.
    pub fn pop(&mut self, out: &mut [u8; MAX_PACKET_LEN]) -> Option<(NodeId, usize)> {
        let e = self.ent(0)?;
        let src = self.data.get(e.off..e.off + e.len)?;
        out.get_mut(..e.len)?.copy_from_slice(src);
        self.drop_front();
        Some((e.dst, e.len))
    }

    /// The packet at position `i`, oldest first.
    pub fn get(&self, i: usize) -> Option<Held<'_>> {
        let e = self.ent(i).filter(|_| i < self.n)?;
        Some(Held {
            dst: e.dst,
            packet: self.data.get(e.off..e.off + e.len)?,
        })
    }

    /// Keep the packets for which `keep(queue, position, packet)` holds, in order. `keep` sees the whole queue as it
    /// was before the call, so a decision may look at the packets before and after.
    pub fn retain(&mut self, mut keep: impl FnMut(&Self, usize, &Held<'_>) -> bool) {
        let mut flags = [true; QUEUED];
        for (i, f) in flags.iter_mut().enumerate().take(self.n) {
            *f = self.get(i).is_none_or(|h| keep(self, i, &h));
        }
        let mut w = 0;
        let mut off = 0;
        for (i, f) in flags.iter().enumerate().take(self.n) {
            let Some(e) = self.ent(i) else { continue };
            if !*f {
                continue;
            }
            self.data.copy_within(e.off..e.off + e.len, off);
            if let Some(s) = self.ents.get_mut(self.head + w) {
                *s = Some(Ent { off, ..e });
            }
            off += e.len;
            w += 1;
        }
        for s in self.ents.iter_mut().skip(self.head + w).take(self.n - w) {
            *s = None;
        }
        self.n = w;
        if w == 0 {
            self.head = 0;
        }
    }
}
