//! The mailbox: encrypted packets held for a sleeping member (CMP-CON-07).
//!
//! A relay that holds a member's sleep notice keeps the packets addressed to that member here, up to a byte quota
//! per member and a maximum age, and hands them over when the member returns. The relay never reads the content: a
//! message is the source node, the opaque flag byte and the already end-to-end protected packet.
//!
//! Invariants:
//! - The bytes held for one member never exceed `BYTES` (headers included), and the members never exceed `NODES`.
//! - A message is delivered at most once: [`Mailbox::pop`] removes it before returning it, and [`Mailbox::look`] then
//!   [`Mailbox::remove`] is the same step in two halves for a caller that removes it only once it was handed over;
//!   [`Mailbox::drain`] takes a message out only when the caller says it took it.
//! - Overflow drops the oldest messages first, and age drops from the front; every drop is counted in [`Stats`], so
//!   a loss is never silent.
//! - Messages leave in the order they arrived. [`Mailbox::drain`] steps over a message too long for the caller: the
//!   ones it hands over keep their order and the ones it leaves stay in theirs.
//! - A drain reads every held byte once and moves it at most once, in place.
//! - Nothing allocates or panics; a ring holds a message in at most two pieces and copies it out whole.

use pinc_crypto::NodeId;
use pinc_wire::{Reader, Writer};

use crate::carrier::frame::MAX_PACKET_LEN;
use crate::carrier::node::{self, NODE_ID_LEN};
use crate::relay::table::Table;

/// The stored size of a message header: source node, flag, length, arrival time and sequence number.
pub const ENTRY_HEAD: usize = NODE_ID_LEN + 1 + 2 + 8 + 8;

/// Counters of everything the mailbox did; none is ever reset by the mailbox itself.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Stats {
    /// Messages stored.
    pub stored: u64,
    /// Messages handed to a returning member.
    pub delivered: u64,
    /// Messages dropped because the quota was full (oldest first).
    pub dropped_oldest: u64,
    /// Bytes of those messages.
    pub dropped_oldest_bytes: u64,
    /// Messages dropped because they reached the maximum age.
    pub expired: u64,
    /// Messages refused because they cannot fit the quota alone or are empty or longer than a packet.
    pub refused_oversize: u64,
    /// Messages refused because no member slot was free.
    pub refused_members: u64,
}

/// The result of storing a message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Push {
    /// Stored.
    Stored {
        /// The message's sequence number (increasing over the whole mailbox).
        seq: u64,
        /// How many older messages the quota pushed out.
        dropped: u32,
        /// Whether the member had no message before this one (the moment to trigger a wake-up).
        first: bool,
    },
    /// The message is empty, longer than a packet, or does not fit the quota even alone.
    TooLarge,
    /// All member slots are taken by members with held messages.
    NoSlot,
}

/// A message handed back by [`Mailbox::pop`], [`Mailbox::pop_fitting`] or [`Mailbox::look`]; its body is in the buffer
/// given to the call.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Delivered {
    /// The node the message came from.
    pub src: NodeId,
    /// The flag byte.
    pub flag: u8,
    /// The body length.
    pub len: usize,
    /// The sequence number [`Push::Stored`] reported.
    pub seq: u64,
}

#[derive(Debug)]
struct Held<const B: usize> {
    ring: [u8; B],
    head: usize,
    used: usize,
    count: usize,
    /// Bytes moved by drains, for the tests that check the bound.
    #[cfg(test)]
    moved: usize,
}

impl<const B: usize> Held<B> {
    fn new() -> Self {
        Self {
            ring: [0; B],
            head: 0,
            used: 0,
            count: 0,
            #[cfg(test)]
            moved: 0,
        }
    }

    fn copy_out(&self, from: usize, dst: &mut [u8]) {
        for (i, d) in dst.iter_mut().enumerate() {
            *d = self.ring.get((from + i) % B).copied().unwrap_or(0);
        }
    }

    fn copy_in(&mut self, from: usize, src: &[u8]) {
        for (i, s) in src.iter().enumerate() {
            if let Some(d) = self.ring.get_mut((from + i) % B) {
                *d = *s;
            }
        }
    }

    /// Copy `len` bytes from ring offset `from` to ring offset `to`, lowest first, so a destination behind its
    /// source may overlap it.
    fn slide(&mut self, from: usize, to: usize, len: usize) {
        for i in 0..len {
            let b = self.ring.get((from + i) % B).copied().unwrap_or(0);
            if let Some(d) = self.ring.get_mut((to + i) % B) {
                *d = b;
            }
        }
        #[cfg(test)]
        {
            self.moved += len;
        }
    }

    /// The header at ring offset `at`: (source, flag, body length, arrival, sequence).
    fn header(&self, at: usize) -> Option<(NodeId, u8, usize, u64, u64)> {
        let mut head = [0u8; ENTRY_HEAD];
        self.copy_out(at, &mut head);
        let mut r = Reader::new(&head);
        let src = node::read(&mut r).ok()?;
        let flag = r.read_u8().ok()?;
        let len = usize::from(r.read_u16().ok()?);
        let at = r.read_u64().ok()?;
        let seq = r.read_u64().ok()?;
        Some((src, flag, len, at, seq))
    }

    /// The header at the front.
    fn front(&self) -> Option<(NodeId, u8, usize, u64, u64)> {
        if self.count == 0 {
            return None;
        }
        self.header(self.head)
    }

    fn skip_front(&mut self) -> usize {
        let Some((_, _, len, _, _)) = self.front() else {
            return 0;
        };
        let size = ENTRY_HEAD + len;
        self.head = (self.head + size) % B;
        self.used -= size;
        self.count -= 1;
        size
    }
}

/// What a [`Mailbox::drain`] caller answers for a message it was offered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Offer {
    /// The caller took the message: it leaves the mailbox and counts as delivered.
    pub taken: bool,
    /// Offer the messages behind it too; when false nothing more is offered and the rest stays held.
    pub go_on: bool,
}

/// The state of one drain: messages are read in order from `read`; one that stays is moved down to `write`, the front
/// of the gap the removed ones left, so every byte is read once and moved at most once. All are distances in bytes
/// from the front the walk began at.
#[derive(Clone, Copy)]
struct Walk {
    total: usize,
    read: usize,
    write: usize,
    base: usize,
    kept: usize,
    left: usize,
}

/// Packets held for sleeping members: at most `NODES` members and `BYTES` bytes each.
#[derive(Debug)]
pub struct Mailbox<const NODES: usize, const BYTES: usize> {
    held: Table<Held<BYTES>, NODES>,
    max_age_ns: u64,
    next_seq: u64,
    stats: Stats,
}

impl<const NODES: usize, const BYTES: usize> Mailbox<NODES, BYTES> {
    /// An empty mailbox whose messages expire after `max_age_ns`; `seed` keys the member table's hash.
    pub fn new(max_age_ns: u64, seed: u64) -> Self {
        Self {
            held: Table::new(seed),
            max_age_ns,
            next_seq: 0,
            stats: Stats::default(),
        }
    }

    /// The counters.
    pub const fn stats(&self) -> Stats {
        self.stats
    }

    /// Messages and bytes held for `node`.
    pub fn pending(&self, node: &NodeId) -> (usize, usize) {
        self.held.get(node).map_or((0, 0), |h| (h.count, h.used))
    }

    /// Members with held messages.
    pub const fn members(&self) -> usize {
        self.held.len()
    }

    fn expire(held: &mut Held<BYTES>, stats: &mut Stats, now: u64, max_age: u64) {
        while let Some((_, _, _, at, _)) = held.front() {
            if now.saturating_sub(at) < max_age {
                break;
            }
            held.skip_front();
            stats.expired += 1;
        }
    }

    /// Store `body` from `src` for `node`.
    pub fn push(&mut self, now: u64, node: &NodeId, src: &NodeId, flag: u8, body: &[u8]) -> Push {
        self.push_at(now, now, node, src, flag, body)
    }

    /// Store a message that arrived at `at`, which is before `now` when the host restores what it kept across a
    /// restart: the message expires `max_age` after `at`. The host does not restore a message that has expired, and
    /// restores a member's messages oldest first so their order and the quota's choice of what to push out hold.
    pub fn restore(&mut self, now: u64, at: u64, node: &NodeId, src: &NodeId, flag: u8, body: &[u8]) -> Push {
        self.push_at(now, at, node, src, flag, body)
    }

    /// The `index`th message held for `node`, oldest first: its body is copied into `buf` and its header returned
    /// together with the time it arrived. Walks from the oldest, so a host exporting a member's messages reads
    /// indexes `0..count` ([`Mailbox::pending`]).
    pub fn peek(&self, node: &NodeId, index: usize, buf: &mut [u8; MAX_PACKET_LEN]) -> Option<(Delivered, u64)> {
        let h = self.held.get(node)?;
        if index >= h.count {
            return None;
        }
        let mut at_off = h.head;
        for i in 0..=index {
            let (src, flag, len, at, seq) = h.header(at_off)?;
            if i == index {
                h.copy_out(at_off + ENTRY_HEAD, buf.get_mut(..len)?);
                return Some((Delivered { src, flag, len, seq }, at));
            }
            at_off = (at_off + ENTRY_HEAD + len) % BYTES;
        }
        None
    }

    fn push_at(&mut self, now: u64, at: u64, node: &NodeId, src: &NodeId, flag: u8, body: &[u8]) -> Push {
        let size = ENTRY_HEAD + body.len();
        if body.is_empty() || body.len() > MAX_PACKET_LEN || size > BYTES {
            self.stats.refused_oversize += 1;
            return Push::TooLarge;
        }
        if !self.held.contains(node) && self.held.insert(*node, Held::new()).is_err() {
            self.stats.refused_members += 1;
            return Push::NoSlot;
        }
        let Self {
            held,
            max_age_ns,
            next_seq,
            stats,
        } = self;
        let Some(h) = held.get_mut(node) else {
            return Push::NoSlot;
        };
        Self::expire(h, stats, now, *max_age_ns);
        let first = h.count == 0;
        let mut dropped = 0u32;
        while h.used + size > BYTES {
            let freed = h.skip_front();
            if freed == 0 {
                break;
            }
            stats.dropped_oldest += 1;
            stats.dropped_oldest_bytes += freed as u64;
            dropped += 1;
        }
        let mut head = [0u8; ENTRY_HEAD];
        let mut w = Writer::new(&mut head);
        let wrote = node::write(&mut w, src)
            .and_then(|()| w.put_u8(flag))
            .and_then(|()| w.put_u16(u16::try_from(body.len()).unwrap_or(0)))
            .and_then(|()| w.put_u64(at))
            .and_then(|()| w.put_u64(*next_seq));
        if wrote.is_err() {
            return Push::TooLarge;
        }
        let tail = (h.head + h.used) % BYTES;
        h.copy_in(tail, &head);
        h.copy_in(tail + ENTRY_HEAD, body);
        h.used += size;
        h.count += 1;
        let seq = *next_seq;
        *next_seq += 1;
        stats.stored += 1;
        Push::Stored { seq, dropped, first }
    }

    /// Remove the oldest live message of `node` and copy its body into `buf`. The message is gone: it is delivered
    /// at most once, whatever the host does with it.
    pub fn pop(&mut self, now: u64, node: &NodeId, buf: &mut [u8; MAX_PACKET_LEN]) -> Option<Delivered> {
        self.pop_fitting(now, node, buf, MAX_PACKET_LEN)
    }

    /// Like [`Mailbox::pop`], but an oldest live message with a body longer than `max_len` stays held, in front, and
    /// `None` is returned: the caller has no way to deliver it now (a UDP datagram is shorter than a carrier packet).
    pub fn pop_fitting(
        &mut self,
        now: u64,
        node: &NodeId,
        buf: &mut [u8; MAX_PACKET_LEN],
        max_len: usize,
    ) -> Option<Delivered> {
        let m = self.look(now, node, buf, max_len)?;
        self.remove(node, m.seq);
        Some(m)
    }

    /// The oldest live message of `node` if its body is at most `max_len` long: the body is copied into `buf` and
    /// the message stays held, in front, until [`Mailbox::remove`] takes it out. Expired messages are dropped first.
    pub fn look(
        &mut self,
        now: u64,
        node: &NodeId,
        buf: &mut [u8; MAX_PACKET_LEN],
        max_len: usize,
    ) -> Option<Delivered> {
        let Self {
            held,
            max_age_ns,
            stats,
            ..
        } = self;
        let h = held.get_mut(node)?;
        Self::expire(h, stats, now, *max_age_ns);
        let out = h
            .front()
            .filter(|f| f.2 <= max_len)
            .and_then(|(src, flag, len, _, seq)| {
                let dst = buf.get_mut(..len)?;
                h.copy_out(h.head + ENTRY_HEAD, dst);
                Some(Delivered { src, flag, len, seq })
            });
        if h.count == 0 {
            held.remove(node);
        }
        out
    }

    /// Take the message numbered `seq` out of `node`'s mailbox and count it delivered, if it is the oldest one held
    /// (the one [`Mailbox::look`] returned). Returns whether it was removed.
    pub fn remove(&mut self, node: &NodeId, seq: u64) -> bool {
        let Some(h) = self.held.get_mut(node) else {
            return false;
        };
        let removed = h.front().is_some_and(|f| f.4 == seq) && h.skip_front() > 0;
        if removed {
            self.stats.delivered += 1;
        }
        if h.count == 0 {
            self.held.remove(node);
        }
        removed
    }

    /// Offer `node`'s held messages to `offer`, oldest first, in one pass. Expired messages are dropped first. A
    /// message whose body is longer than `max_len` is not offered: it stays held, in its place. For each message
    /// that fits, the body is copied into `buf` and `offer` says whether it took it (it leaves the mailbox and counts
    /// as delivered) and whether to go on; after a stop nothing more is offered. What stays keeps its order, the
    /// member is freed when nothing is left, and the counts and byte totals are exact.
    ///
    /// The pass reads every held byte once and moves it at most once, in place, and allocates nothing. The mailbox
    /// is reached through `mailbox` at each step and not borrowed while `offer` runs, so `offer` may use the rest of
    /// `ctx` (it must not touch this member's messages).
    pub fn drain<X>(
        ctx: &mut X,
        mailbox: fn(&mut X) -> &mut Self,
        now: u64,
        node: &NodeId,
        max_len: usize,
        buf: &mut [u8; MAX_PACKET_LEN],
        mut offer: impl FnMut(&mut X, &Delivered, &[u8]) -> Offer,
    ) {
        let mut walk = {
            let Self {
                held,
                max_age_ns,
                stats,
                ..
            } = mailbox(ctx);
            let Some(h) = held.get_mut(node) else {
                return;
            };
            Self::expire(h, stats, now, *max_age_ns);
            Walk {
                total: h.used,
                read: 0,
                write: 0,
                base: 0,
                kept: 0,
                left: h.count,
            }
        };
        while walk.left > 0 {
            let seen = {
                let Some(h) = mailbox(ctx).held.get_mut(node) else {
                    return;
                };
                let Some((src, flag, len, _, seq)) = h.header((h.head + walk.read) % BYTES) else {
                    break;
                };
                let fits = len <= max_len.min(MAX_PACKET_LEN);
                if fits && let Some(dst) = buf.get_mut(..len) {
                    h.copy_out(h.head + walk.read + ENTRY_HEAD, dst);
                }
                (Delivered { src, flag, len, seq }, fits)
            };
            let (d, fits) = seen;
            let size = ENTRY_HEAD + d.len;
            let answer = if fits {
                offer(ctx, &d, buf.get(..d.len).unwrap_or_default())
            } else {
                Offer {
                    taken: false,
                    go_on: true,
                }
            };
            if !answer.taken && !answer.go_on {
                break;
            }
            let Self { held, stats, .. } = mailbox(ctx);
            let Some(h) = held.get_mut(node) else {
                return;
            };
            if answer.taken {
                stats.delivered += 1;
                walk.read += size;
                if walk.kept == 0 {
                    walk.base = walk.read;
                    walk.write = walk.read;
                }
            } else {
                if walk.write != walk.read {
                    h.slide(h.head + walk.read, h.head + walk.write, size);
                }
                walk.read += size;
                walk.write += size;
                walk.kept += 1;
            }
            walk.left -= 1;
            if !answer.go_on {
                break;
            }
        }
        let Self { held, .. } = mailbox(ctx);
        let Some(h) = held.get_mut(node) else {
            return;
        };
        if walk.write != walk.read {
            h.slide(h.head + walk.read, h.head + walk.write, walk.total - walk.read);
        }
        h.used = (walk.write - walk.base) + (walk.total - walk.read);
        h.count = walk.kept + walk.left;
        h.head = (h.head + walk.base) % BYTES;
        if h.count == 0 {
            held.remove(node);
        }
    }

    /// Bytes the drains moved for `node` so far (tests only).
    #[cfg(test)]
    fn moved(&self, node: &NodeId) -> usize {
        self.held.get(node).map_or(0, |h| h.moved)
    }

    /// Drop expired messages of every member and free the empty ones.
    pub fn sweep(&mut self, now: u64) {
        let Self {
            held,
            max_age_ns,
            stats,
            ..
        } = self;
        held.retain(|_, h| {
            Self::expire(h, stats, now, *max_age_ns);
            h.count > 0
        });
    }

    /// Drop everything held for `node` (for example when the host forgets the member); counted as expired.
    pub fn clear(&mut self, node: &NodeId) {
        if let Some(h) = self.held.remove(node) {
            self.stats.expired += h.count as u64;
        }
    }
}

#[cfg(test)]
mod tests;
