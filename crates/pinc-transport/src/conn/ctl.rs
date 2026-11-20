//! Control frames that must be sent again when their packet is lost, and how recovery feedback reaches every layer.
//!
//! A [`FrameRef::Control`] carries only a kind and one number, so the frames with a payload (the stream layer's flow
//! control and reset frames) live in a small table keyed by that number, and the extension frames in a second one
//! whose bodies are kept in chunks of the connection's buffer pool, charged like every other buffer and touched only
//! while a frame is held. The frames fully described by a flag (READY, tickets, REKEY) are re-derived from their
//! owners.
//!
//! Invariants: the tables hold at most [`TABLE`] stream frames and [`EXT_SLOTS`] extension frames in flight, so a
//! packet that cannot record one more stops adding them; an entry is removed when its packet is acknowledged, and a
//! lost entry hands its frame back to the layer that produced it or is sent again; a held extension frame owns exactly
//! one pool chunk, freed when its slot is.

use pinc_security::TicketBatch;

use crate::frame::Frame;
use crate::recovery::{Event, FrameRef, FrameRefs, MAX_FRAME_REFS};
use crate::stream::pool::{BufferPool, Chunk};
use crate::stream::{ControlFrame, StreamSource, Streams};

/// A stream-layer control frame; the id keys the table.
pub(crate) const K_STREAM_CTL: u8 = 2;
/// NEW_TICKETS.
pub(crate) const K_TICKETS: u8 = 5;
/// READY.
pub(crate) const K_READY: u8 = 6;
/// REKEY; the id is 1 for an answer and 0 for a request.
pub(crate) const K_REKEY: u8 = 7;
/// An extension frame; the id keys the extension table.
pub(crate) const K_EXT: u8 = 8;

const TABLE: usize = 24;
/// Extension frames kept for retransmission at once.
pub(crate) const EXT_SLOTS: usize = 8;
/// Extension frames queued behind the held ones.
pub(crate) const EXT_QUEUED: usize = 16;
/// The room a held extension frame body has: a packet at the largest path MTU never carries more.
pub(crate) const EXT_BODY_MAX: usize = super::config::JUMBO_MTU as usize;

/// An extension frame waiting for its acknowledgement.
#[derive(Debug)]
pub(crate) struct ExtSlot {
    pub(crate) key: u64,
    pub(crate) ty: u64,
    pub(crate) len: usize,
    /// The pool chunk the body is kept in, its first `len` bytes.
    pub(crate) chunk: Chunk,
    /// Whether the frame waits to be (re)sent; false while a packet carries it.
    pub(crate) pending: bool,
}

/// What a batch of recovery events turned up for the connection.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct Outcome {
    pub(crate) probe_acked: Option<u32>,
    pub(crate) probe_lost: Option<u32>,
    /// The newest acknowledged packet larger than the minimum datagram size.
    pub(crate) big_acked: Option<u64>,
    /// A REKEY answer was lost.
    pub(crate) rekey_answer_lost: bool,
    /// A REKEY request was lost.
    pub(crate) rekey_request_lost: bool,
    pub(crate) lost_packets: u32,
    pub(crate) acked_packets: u32,
    /// Acknowledged packets that count toward the loss average (every one but repair packets).
    pub(crate) loss_acked: u32,
    /// Lost packets that count toward the loss average (every one but repair packets and path MTU probes).
    pub(crate) loss_lost: u32,
    /// Per path slot, the highest packet number acknowledged on it.
    pub(crate) acked_pn: [Option<u64>; crate::recovery::MAX_PATHS],
}

/// Pending control state and the table of frames in flight.
#[derive(Debug)]
pub(crate) struct Ctl {
    table: [Option<(u64, ControlFrame)>; TABLE],
    next_key: u64,
    pub(crate) ready: bool,
    pub(crate) tickets: Option<TicketBatch>,
    pub(crate) tickets_pending: bool,
    /// Which batch `tickets` is: a frame carries it, so an answer about an older batch leaves a newer one alone.
    // vertexia: a u32 generation; an answer 2^32 batches late would match, far past the recovery window.
    tickets_gen: u32,
    pub(crate) ext: [Option<ExtSlot>; EXT_SLOTS],
    next_ext: u64,
}

impl Ctl {
    pub(crate) const fn new() -> Self {
        Self {
            table: [None; TABLE],
            next_key: 1,
            ready: false,
            tickets: None,
            tickets_pending: false,
            tickets_gen: 0,
            ext: [const { None }; EXT_SLOTS],
            next_ext: 1,
        }
    }

    /// Keep an extension frame for sending and resending until acknowledged, its body in a chunk of `pool`. Returns
    /// false when every slot is busy, the body is too long or the pool has no chunk to spare; the frame then waits in
    /// its queue for a later try.
    pub(crate) fn hold_ext(&mut self, pool: &mut BufferPool<'_>, ty: u64, body: &[u8]) -> bool {
        let Some(slot) = self.ext.iter_mut().find(|s| s.is_none()) else {
            return false;
        };
        if body.len() > EXT_BODY_MAX {
            return false;
        }
        let Ok(chunk) = pool.alloc_chunk() else {
            return false;
        };
        let Some(dst) = pool.bytes_mut(&chunk).get_mut(..body.len()) else {
            pool.free_chunk(chunk);
            return false;
        };
        dst.copy_from_slice(body);
        *slot = Some(ExtSlot {
            key: self.next_ext,
            ty,
            len: body.len(),
            chunk,
            pending: true,
        });
        self.next_ext += 1;
        true
    }

    /// READY goes in the packet when it is owed and the packet's frame references have room. `put` writes a frame in
    /// the packet and says whether it fitted. Returns whether READY went.
    pub(crate) fn fill_ready(&mut self, refs: &mut FrameRefs, put: impl FnOnce(&Frame<'_>) -> bool) -> bool {
        if self.ready && refs.len() < MAX_FRAME_REFS && put(&Frame::Ready) {
            self.ready = false;
            let _ = refs.push(FrameRef::Control { kind: K_READY, id: 0 });
            return true;
        }
        false
    }

    /// The ticket batch goes in the packet when it is pending and the packet's frame references have room; as
    /// [`Self::fill_ready`]. Returns whether it went.
    pub(crate) fn fill_tickets(&mut self, refs: &mut FrameRefs, put: impl FnOnce(&Frame<'_>) -> bool) -> bool {
        if self.tickets_pending
            && refs.len() < MAX_FRAME_REFS
            && let Some(batch) = self.tickets
            && put(&Frame::NewTickets(batch))
        {
            self.tickets_pending = false;
            let _ = refs.push(FrameRef::Control {
                kind: K_TICKETS,
                id: u64::from(self.tickets_gen),
            });
            return true;
        }
        false
    }

    /// A held extension frame goes in the packet when it waits to be sent and the packet's frame references have
    /// room; `put` writes it and says whether it fitted. Returns whether it went.
    pub(crate) fn fill_ext(slot: &mut ExtSlot, refs: &mut FrameRefs, put: impl FnOnce(&ExtSlot) -> bool) -> bool {
        if !slot.pending || refs.len() >= MAX_FRAME_REFS || !put(slot) {
            return false;
        }
        slot.pending = false;
        let _ = refs.push(FrameRef::Control {
            kind: K_EXT,
            id: slot.key,
        });
        true
    }

    /// Hold a new ticket batch to send; it replaces one not yet acknowledged.
    pub(crate) const fn hold_tickets(&mut self, batch: TicketBatch) {
        self.tickets = Some(batch);
        self.tickets_pending = true;
        self.tickets_gen = self.tickets_gen.wrapping_add(1);
    }

    /// A packet carrying batch `id` was acknowledged: the batch is done unless a newer one replaced it.
    pub(crate) fn tickets_acked(&mut self, id: u64) {
        if id == u64::from(self.tickets_gen) {
            self.tickets = None;
            self.tickets_pending = false;
        }
    }

    /// A packet carrying batch `id` was lost or not sent: send the batch again unless a newer one replaced it.
    pub(crate) fn tickets_lost(&mut self, id: u64) {
        if id == u64::from(self.tickets_gen) {
            self.tickets_pending = self.tickets.is_some();
        }
    }

    /// Owe the peer a READY.
    pub(crate) const fn owe_ready(&mut self) {
        self.ready = true;
    }

    /// Empty extension slot `slot` and give its chunk back to `pool`.
    pub(crate) fn free_ext(slot: &mut Option<ExtSlot>, pool: &mut BufferPool<'_>) {
        if let Some(s) = slot.take() {
            pool.free_chunk(s.chunk);
        }
    }

    /// Give back every held extension frame's chunk (the connection is going away).
    pub(crate) fn release_ext(&mut self, pool: &mut BufferPool<'_>) {
        for slot in &mut self.ext {
            Self::free_ext(slot, pool);
        }
    }

    /// The extension slot with `key`.
    pub(crate) fn ext_mut(&mut self, key: u64) -> Option<&mut ExtSlot> {
        self.ext.iter_mut().flatten().find(|s| s.key == key)
    }

    /// Record `frame` as in flight and return the key to put in the frame reference, or `None` if the table is full.
    pub(crate) fn track(&mut self, frame: ControlFrame) -> Option<u64> {
        let slot = self.table.iter_mut().find(|s| s.is_none())?;
        let key = self.next_key;
        self.next_key += 1;
        *slot = Some((key, frame));
        Some(key)
    }

    pub(crate) fn untrack(&mut self, key: u64) -> Option<ControlFrame> {
        self.take(key)
    }

    fn take(&mut self, key: u64) -> Option<ControlFrame> {
        self.table
            .iter_mut()
            .find(|s| s.is_some_and(|(k, _)| k == key))
            .and_then(Option::take)
            .map(|(_, f)| f)
    }
}

/// Apply one recovery event to every layer: stream bytes, control frames, acknowledgement bookkeeping and the
/// summary the connection acts on.
pub(crate) fn apply<S: StreamSource, const N: usize, const C: usize>(
    ev: &Event<'_>,
    streams: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    ctl: &mut Ctl,
    out: &mut Outcome,
) {
    match *ev {
        Event::Acked {
            frames,
            mtu_probe,
            size,
            repair,
            pn,
            path,
            ..
        } => {
            out.acked_packets += 1;
            if let Some(s) = out.acked_pn.get_mut(usize::from(path)) {
                *s = (*s).max(Some(pn));
            }
            if size > u32::from(super::config::MIN_MTU) {
                out.big_acked = out.big_acked.max(Some(pn));
            }
            out.loss_acked += u32::from(!repair);
            if mtu_probe {
                out.probe_acked = Some(size);
            }
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => {
                        streams.on_acked(pool, id, offset, u64::from(len), fin);
                    }
                    FrameRef::Control { kind, id } => acked(kind, id, streams, pool, ctl),
                }
            }
        }
        Event::LateAcked { frames, .. } => {
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => {
                        streams.on_late_acked(pool, id, offset, u64::from(len), fin);
                    }
                    FrameRef::Control { kind, id } => acked(kind, id, streams, pool, ctl),
                }
            }
        }
        Event::Lost {
            size,
            frames,
            requeue,
            mtu_probe,
            ..
        } => {
            out.lost_packets += 1;
            out.loss_lost += u32::from(requeue);
            if mtu_probe {
                out.probe_lost = Some(size);
            }
            if !requeue {
                return;
            }
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => streams.on_lost(id, offset, u64::from(len), fin),
                    FrameRef::Control { kind, id } => lost(kind, id, streams, ctl, out),
                }
            }
        }
    }
}

fn acked<S: StreamSource, const N: usize, const C: usize>(
    kind: u8,
    id: u64,
    streams: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    ctl: &mut Ctl,
) {
    match kind {
        K_STREAM_CTL => {
            if let Some(f) = ctl.take(id) {
                streams.on_control_acked(pool, &f);
            }
        }
        K_EXT => {
            if let Some(s) = ctl.ext.iter_mut().find(|s| s.as_ref().is_some_and(|s| s.key == id)) {
                Ctl::free_ext(s, pool);
            }
        }
        K_TICKETS => ctl.tickets_acked(id),
        _ => {}
    }
}

fn lost<S: StreamSource, const N: usize, const C: usize>(
    kind: u8,
    id: u64,
    streams: &mut Streams<S, N, C>,
    ctl: &mut Ctl,
    out: &mut Outcome,
) {
    match kind {
        K_STREAM_CTL => {
            if let Some(f) = ctl.take(id) {
                streams.on_control_lost(&f);
            }
        }
        K_EXT => {
            if let Some(s) = ctl.ext_mut(id) {
                s.pending = true;
            }
        }
        K_REKEY => {
            if id == 1 {
                out.rekey_answer_lost = true;
            } else {
                out.rekey_request_lost = true;
            }
        }
        K_TICKETS => ctl.tickets_lost(id),
        K_READY => ctl.ready = true,
        _ => {}
    }
}

/// A real control state, pool and stream table driven by the trace validation (cargo feature `trace`).
#[cfg(all(feature = "trace", feature = "alloc"))]
pub(super) mod trace {
    use alloc::vec::Vec;

    use pinc_security::{TicketBatch, TicketEntry};

    use super::{Ctl, EXT_BODY_MAX as BODY_MAX, K_EXT, K_READY, K_STREAM_CTL, K_TICKETS, Outcome, apply};
    use crate::conn::send::{put, put_extension};
    use crate::recovery::{Event, FrameRef, FrameRefs};
    use crate::stream::pool::{BufferPool, Chunk};
    use crate::stream::{Config, ControlFrame, NoSource, Streams};

    /// Longest extension body a slot holds.
    pub const EXT_BODY_MAX: usize = BODY_MAX;

    /// The control state after a call.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct CtlView {
        /// Per table place (24): the key it holds, 0 when empty.
        pub tab: Vec<u64>,
        /// Per extension slot (8): `(key, pending)`, `None` when empty.
        pub ext: Vec<Option<(u64, bool)>>,
        /// `next_key`.
        pub nk: u64,
        /// `next_ext`.
        pub ne: u64,
        /// `ready`.
        pub ready: bool,
        /// The generation of the ticket batch held (as given to `issue`), 0 when none.
        pub tk: u64,
        /// `tickets_pending`.
        pub tp: bool,
        /// The id the frame reference of the batch held carries.
        pub tg: u64,
        /// `pool.used_chunks()`.
        pub used: usize,
    }

    /// A real `Ctl` with a pool of `p` chunks and a stream table.
    pub struct CtlProbe {
        pool: BufferPool<'static>,
        streams: Streams<NoSource, 4, 16>,
        ctl: Ctl,
        generation: u64,
        mine: Vec<Chunk>,
        limit: u64,
        /// The packet the frames are put in (one at a time, from its start), as large as a datagram.
        packet: Vec<u8>,
        /// How many frame references the packet already holds when a frame is put in it.
        refs_held: usize,
    }

    /// The room of the packet a probe call writes into.
    const PACKET: usize = 1500;

    /// The kind code of a frame reference, by its trace name.
    fn kind_code(kind: &str) -> Option<u8> {
        match kind {
            "sc" => Some(K_STREAM_CTL),
            "ext" => Some(K_EXT),
            "tk" => Some(K_TICKETS),
            "rd" => Some(K_READY),
            _ => None,
        }
    }

    impl CtlProbe {
        /// `BufferPool::new_boxed(p)`, `Streams::new(&Config::new(false), &pool)`, `Ctl::new()`.
        #[must_use]
        pub fn new(p: usize) -> Self {
            let pool = BufferPool::new_boxed(p);
            let streams = Streams::new(&Config::new(false), &pool);
            Self {
                pool,
                streams,
                ctl: Ctl::new(),
                generation: 0,
                mine: Vec::new(),
                limit: 0,
                packet: alloc::vec![0u8; PACKET],
                refs_held: 0,
            }
        }

        /// `ctl.track(ControlFrame::MaxStreams { limit })` with `limit` a counter from 1: the key, or `None` when full.
        pub fn track(&mut self) -> Option<u64> {
            self.limit += 1;
            self.ctl.track(ControlFrame::MaxStreams { limit: self.limit })
        }

        /// `ctl.hold_ext(&mut pool, 0x40, &body)` with a body of `len` bytes (any `len`, also above `EXT_BODY_MAX`).
        pub fn hold(&mut self, len: usize) -> bool {
            let body = alloc::vec![0u8; len];
            self.ctl.hold_ext(&mut self.pool, 0x40, &body)
        }

        /// The packet of the next calls holds `len` bytes (a datagram's worth at the start), so a frame longer than
        /// that does not fit.
        pub fn set_room(&mut self, len: usize) {
            self.packet = alloc::vec![0u8; len];
        }

        /// The packet of the next calls already holds `n` frame references (`MAX_FRAME_REFS` leaves no room).
        pub const fn set_refs(&mut self, n: usize) {
            self.refs_held = n;
        }

        /// The frame references a packet holds when a frame is put in it.
        fn refs(&self) -> FrameRefs {
            let mut refs = FrameRefs::new();
            for _ in 0..self.refs_held {
                let _ = refs.push(FrameRef::Control { kind: 0, id: 0 });
            }
            refs
        }

        /// `Ctl::fill_ext` with the real `put_extension`, as `conn/send.rs` puts a held frame in a packet: when slot
        /// `slot` holds a pending frame that fits, clear `pending` and return its key (the id of the frame
        /// reference); else `None` and nothing changes.
        pub fn send_ext(&mut self, slot: usize) -> Option<u64> {
            let mut refs = self.refs();
            let s = self.ctl.ext.get_mut(slot)?.as_mut()?;
            let (pool, packet) = (&self.pool, &mut self.packet);
            let mut pos = 0;
            if !Ctl::fill_ext(s, &mut refs, |s| put_extension(pool, s, packet, &mut pos)) {
                return None;
            }
            Some(s.key)
        }

        /// `Ctl::free_ext(&mut ctl.ext[slot], &mut pool)` (as `conn/api.rs` gives a held frame up).
        pub fn shed(&mut self, slot: usize) {
            if let Some(s) = self.ctl.ext.get_mut(slot) {
                Ctl::free_ext(s, &mut self.pool);
            }
        }

        /// `pool.alloc_chunk()` by another user of the pool, kept in `mine`; whether it got one.
        pub fn take(&mut self) -> bool {
            self.pool.alloc_chunk().map(|c| self.mine.push(c)).is_ok()
        }

        /// `pool.free_chunk` of the last chunk in `mine`; false (nothing done) when `mine` is empty.
        pub fn give(&mut self) -> bool {
            self.mine.pop().map(|c| self.pool.free_chunk(c)).is_some()
        }

        /// As `conn/drive.rs` takes a ticket batch (`Ctl::hold_tickets`, with one ticket: `drive` holds no empty
        /// batch); the probe keeps `g` as the generation of the batch held.
        pub fn issue(&mut self, g: u64) {
            let mut batch = TicketBatch::new();
            let _ = batch.push(TicketEntry::default());
            self.ctl.hold_tickets(batch);
            self.generation = g;
        }

        /// `Ctl::fill_tickets` with the real `put`, as `conn/send.rs` puts the batch in a packet: when
        /// `tickets_pending` and a batch is held and fits, return the id of the frame reference and the generation
        /// held; else `None`.
        pub fn send_tickets(&mut self) -> Option<(u64, u64)> {
            let mut refs = self.refs();
            let mut pos = 0;
            let packet = &mut self.packet;
            if !self.ctl.fill_tickets(&mut refs, |f| put(packet, &mut pos, f)) {
                return None;
            }
            let id = refs.iter().skip(self.refs_held).find_map(|r| match *r {
                FrameRef::Control { id, .. } => Some(id),
                FrameRef::Stream { .. } => None,
            })?;
            Some((id, self.generation))
        }

        /// As `conn/drive.rs`: `Ctl::owe_ready`.
        pub fn send_ready(&mut self) {
            self.ctl.owe_ready();
        }

        /// `Ctl::fill_ready` with the real `put`, as `conn/send.rs` builds READY: whether it went in the packet.
        pub fn build_ready(&mut self) -> bool {
            let mut refs = self.refs();
            let mut pos = 0;
            let packet = &mut self.packet;
            self.ctl.fill_ready(&mut refs, |f| put(packet, &mut pos, f))
        }

        /// `apply` of an `Event::Acked` with one `FrameRef::Control { kind, id }`; when `ctl.tickets` is then
        /// `None`, the generation kept becomes 0. `kind` is `"sc"`, `"ext"`, `"tk"` or `"rd"`. Returns whether the stream layer was handed the frame: for
        /// `"sc"`, whether `id` was in the table before the call; false for the others (and for any other kind, which
        /// changes nothing).
        pub fn ack(&mut self, kind: &str, id: u64) -> bool {
            self.report(kind, id, |frames| Event::Acked {
                pn: 0,
                size: 0,
                frames,
                mtu_probe: false,
                repair: false,
                path: 0,
            })
        }

        /// The same with `Event::LateAcked { pn: 0, frames }`.
        pub fn late_ack(&mut self, kind: &str, id: u64) -> bool {
            self.report(kind, id, |frames| Event::LateAcked { pn: 0, frames })
        }

        /// The same with `Event::Lost { pn: 0, size: 0, frames, requeue: true, mtu_probe: false }` (no glue).
        pub fn lose(&mut self, kind: &str, id: u64) -> bool {
            self.report(kind, id, |frames| Event::Lost {
                pn: 0,
                size: 0,
                frames,
                requeue: true,
                mtu_probe: false,
            })
        }

        /// `apply` of the event `make` builds for one control reference, with the glue of the connection.
        fn report(&mut self, kind: &str, id: u64, make: impl for<'f> FnOnce(&'f FrameRefs) -> Event<'f>) -> bool {
            let Some(code) = kind_code(kind) else {
                return false;
            };
            let handed = code == K_STREAM_CTL && self.ctl.table.iter().flatten().any(|(k, _)| *k == id);
            let mut frames = FrameRefs::new();
            let _ = frames.push(FrameRef::Control { kind: code, id });
            let mut out = Outcome::default();
            apply(
                &make(&frames),
                &mut self.streams,
                &mut self.pool,
                &mut self.ctl,
                &mut out,
            );
            if self.ctl.tickets.is_none() {
                self.generation = 0;
            }
            handed
        }

        /// The state after a call.
        #[must_use]
        pub fn view(&self) -> CtlView {
            CtlView {
                tab: self.ctl.table.iter().map(|s| s.map_or(0, |(k, _)| k)).collect(),
                ext: self
                    .ctl
                    .ext
                    .iter()
                    .map(|s| s.as_ref().map(|s| (s.key, s.pending)))
                    .collect(),
                nk: self.ctl.next_key,
                ne: self.ctl.next_ext,
                ready: self.ctl.ready,
                tk: if self.ctl.tickets.is_some() { self.generation } else { 0 },
                tp: self.ctl.tickets_pending,
                tg: u64::from(self.ctl.tickets_gen),
                used: self.pool.used_chunks(),
            }
        }
    }

    impl Drop for CtlProbe {
        fn drop(&mut self) {
            self.ctl.release_ext(&mut self.pool);
            for c in self.mine.drain(..) {
                self.pool.free_chunk(c);
            }
        }
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// A held extension frame keeps its body in exactly one pool chunk, read back intact, and gives it back when its
    /// slot is freed; with no chunk to spare the frame is not held (it stays queued), and a closing connection gives
    /// every chunk back.
    #[test]
    fn a_held_extension_frame_owns_one_pool_chunk_until_its_slot_is_freed() {
        let mut pool = BufferPool::new_boxed(3);
        let mut ctl = Ctl::new();
        assert!(ctl.hold_ext(&mut pool, 0x41, b"one"));
        assert!(ctl.hold_ext(&mut pool, 0x42, b"two"));
        assert_eq!(pool.used_chunks(), 2);
        let held = ctl.ext.iter().flatten().find(|s| s.ty == 0x41).unwrap();
        assert_eq!(pool.bytes(&held.chunk).get(..held.len), Some(&b"one"[..]));
        let key = held.key;
        let slot = ctl
            .ext
            .iter_mut()
            .find(|s| s.as_ref().is_some_and(|s| s.key == key))
            .unwrap();
        Ctl::free_ext(slot, &mut pool);
        assert_eq!(pool.used_chunks(), 1);
        assert!(ctl.hold_ext(&mut pool, 0x43, b"three"));
        assert!(ctl.hold_ext(&mut pool, 0x44, b"four"));
        assert!(
            !ctl.hold_ext(&mut pool, 0x45, b"five"),
            "a frame was held with no chunk to keep it in"
        );
        assert!(!ctl.hold_ext(&mut pool, 0x46, &[0; EXT_BODY_MAX + 1]));
        assert_eq!(ctl.ext.iter().flatten().count(), 3);
        ctl.release_ext(&mut pool);
        assert_eq!(pool.used_chunks(), 0);
        assert!(ctl.ext.iter().all(Option::is_none));
    }

    /// One NEW_TICKETS packet's frame references, with the batch sent (as `conn/send.rs` puts it in a packet).
    fn send_tickets(ctl: &mut Ctl) -> FrameRefs {
        let mut refs = FrameRefs::new();
        assert!(ctl.fill_tickets(&mut refs, |_| true));
        refs
    }

    /// Report the packet of `refs` as acknowledged (`lost` false) or lost to every layer, as the recovery events do.
    fn report(ctl: &mut Ctl, refs: &FrameRefs, lost: bool) {
        use crate::stream::{Config, NoSource};
        let mut pool = BufferPool::new_boxed(1);
        let mut streams: Streams<NoSource, 4, 16> = Streams::new(&Config::new(false), &pool);
        let mut out = Outcome::default();
        let ev = if lost {
            Event::Lost {
                pn: 0,
                size: 0,
                frames: refs,
                requeue: true,
                mtu_probe: false,
            }
        } else {
            Event::Acked {
                pn: 0,
                size: 0,
                frames: refs,
                mtu_probe: false,
                repair: false,
                path: 0,
            }
        };
        apply(&ev, &mut streams, &mut pool, ctl, &mut out);
    }

    /// The acknowledgement or the loss of the packet that carried an older ticket batch leaves a newer batch held and
    /// owed; only the packet of the newest batch finishes it or sends it again.
    #[test]
    fn a_newer_ticket_batch_survives_the_acknowledgement_of_an_older_one() {
        let mut ctl = Ctl::new();
        ctl.hold_tickets(TicketBatch::new());
        let a = send_tickets(&mut ctl);
        assert!(!ctl.tickets_pending);
        ctl.hold_tickets(TicketBatch::new());
        report(&mut ctl, &a, false);
        assert!(
            ctl.tickets.is_some() && ctl.tickets_pending,
            "the acknowledgement of batch A dropped batch B"
        );
        let b = send_tickets(&mut ctl);
        report(&mut ctl, &a, false);
        assert!(
            ctl.tickets.is_some(),
            "a second acknowledgement of batch A dropped batch B"
        );
        report(&mut ctl, &a, true);
        assert!(!ctl.tickets_pending, "the loss of batch A's packet sent batch B again");
        report(&mut ctl, &b, true);
        assert!(
            ctl.tickets_pending,
            "the loss of batch B's packet did not send it again"
        );
        let b = send_tickets(&mut ctl);
        report(&mut ctl, &b, false);
        assert!(
            ctl.tickets.is_none() && !ctl.tickets_pending,
            "batch B stays after its acknowledgement"
        );
    }
}
