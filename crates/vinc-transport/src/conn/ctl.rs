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

use vinc_security::TicketBatch;

use crate::recovery::{Event, FrameRef};
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
    /// Per path slot, the size and packet number of a size probe acknowledged on it: the newest of the batch.
    pub(crate) probe_acked: [Option<(u32, u64)>; crate::recovery::MAX_PATHS],
    /// Per path slot, the size and packet number of a size probe lost on it.
    pub(crate) probe_lost: [Option<(u32, u64)>; crate::recovery::MAX_PATHS],
    /// Per path slot, the newest acknowledged packet larger than the minimum datagram size that left on it.
    pub(crate) big_acked: [Option<u64>; crate::recovery::MAX_PATHS],
    /// A REKEY answer was lost.
    pub(crate) rekey_answer_lost: bool,
    /// A REKEY request was lost.
    pub(crate) rekey_request_lost: bool,
    pub(crate) tickets_acked: bool,
    pub(crate) lost_packets: u32,
    pub(crate) acked_packets: u32,
    /// Acknowledged packets that count toward the loss average (every one but repair packets).
    pub(crate) loss_acked: u32,
    /// Lost packets that count toward the loss average (every one but repair packets and path MTU probes).
    pub(crate) loss_lost: u32,
    /// Per path slot, the highest packet number acknowledged on it.
    pub(crate) acked_pn: [Option<u64>; crate::recovery::MAX_PATHS],
    /// Probe outcomes of the batch that an older one of the same slot lost to; counted as dropped.
    pub(crate) probes_passed: u32,
}

/// Pending control state and the table of frames in flight.
#[derive(Debug)]
pub(crate) struct Ctl {
    table: [Option<(u64, ControlFrame)>; TABLE],
    next_key: u64,
    pub(crate) ready: bool,
    pub(crate) tickets: Option<TicketBatch>,
    pub(crate) tickets_pending: bool,
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
            if size > u32::from(super::config::MIN_MTU)
                && let Some(s) = out.big_acked.get_mut(usize::from(path))
            {
                *s = (*s).max(Some(pn));
            }
            out.loss_acked += u32::from(!repair);
            if mtu_probe {
                out.probes_passed += keep_newest(out.probe_acked.get_mut(usize::from(path)), size, pn);
            }
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => {
                        streams.on_acked(pool, id, offset, u64::from(len), fin);
                    }
                    FrameRef::Control { kind, id } => acked(kind, id, streams, pool, ctl, out),
                }
            }
        }
        Event::LateAcked { frames, .. } => {
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => {
                        streams.on_late_acked(pool, id, offset, u64::from(len), fin);
                    }
                    FrameRef::Control { kind, id } => acked(kind, id, streams, pool, ctl, out),
                }
            }
        }
        Event::Lost {
            pn,
            size,
            path,
            frames,
            requeue,
            mtu_probe,
        } => {
            out.lost_packets += 1;
            out.loss_lost += u32::from(requeue);
            if mtu_probe {
                out.probes_passed += keep_newest(out.probe_lost.get_mut(usize::from(path)), size, pn);
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

/// Keep the newest probe outcome of a slot. Returns 1 when an outcome was passed over (the older of the two, or one
/// for a slot that does not exist): it can never match the live probe, which holds the newest packet number.
fn keep_newest(slot: Option<&mut Option<(u32, u64)>>, size: u32, pn: u64) -> u32 {
    let Some(cell) = slot else { return 1 };
    match *cell {
        Some((_, q)) if q >= pn => 1,
        old => {
            *cell = Some((size, pn));
            u32::from(old.is_some())
        }
    }
}

fn acked<S: StreamSource, const N: usize, const C: usize>(
    kind: u8,
    id: u64,
    streams: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    ctl: &mut Ctl,
    out: &mut Outcome,
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
        K_TICKETS => {
            ctl.tickets = None;
            ctl.tickets_pending = false;
            out.tickets_acked = true;
        }
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
        K_TICKETS => ctl.tickets_pending = ctl.tickets.is_some(),
        K_READY => ctl.ready = true,
        _ => {}
    }
}

#[cfg(all(test, feature = "alloc"))]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;
    use crate::recovery::FrameRefs;
    use crate::stream::{Config, NoSource};

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

    /// Run `events` through [`apply`] into one fresh [`Outcome`].
    fn batch(events: &[Event<'_>]) -> Outcome {
        let mut pool = BufferPool::new_boxed(8);
        let mut streams: Streams<NoSource, 2, 2> = Streams::new(&Config::new(true), &pool);
        let mut ctl = Ctl::new();
        let mut out = Outcome::default();
        for ev in events {
            apply(ev, &mut streams, &mut pool, &mut ctl, &mut out);
        }
        out
    }

    /// One acknowledgement can cover the probe of a path that is gone and the probe of the path that took its slot.
    /// Only the newer one can match a probe in flight; the older one is passed over, in either order, and counted, and
    /// the outcomes of other slots and of the other kind are not touched.
    #[test]
    fn a_probe_outcome_passed_over_in_a_batch_is_counted() {
        let refs = FrameRefs::new();
        let acked = |pn, path| Event::Acked {
            pn,
            size: 1452,
            frames: &refs,
            mtu_probe: true,
            repair: false,
            path,
        };
        let lost = |pn, path| Event::Lost {
            pn,
            size: 1452,
            path,
            frames: &refs,
            requeue: false,
            mtu_probe: true,
        };
        for order in [[7, 9], [9, 7]] {
            let out = batch(&[acked(order[0], 1), acked(order[1], 1)]);
            assert_eq!(out.probe_acked[1], Some((1452, 9)), "order {order:?}");
            assert_eq!(out.probes_passed, 1, "order {order:?}");
            let out = batch(&[lost(order[0], 2), lost(order[1], 2)]);
            assert_eq!(out.probe_lost[2], Some((1452, 9)), "order {order:?}");
            assert_eq!(out.probes_passed, 1, "order {order:?}");
        }
        // Other slots, an acknowledgement next to a loss and a packet that is no probe pass nothing over.
        let plain = Event::Acked {
            pn: 3,
            size: 1452,
            frames: &refs,
            mtu_probe: false,
            repair: false,
            path: 1,
        };
        let out = batch(&[acked(7, 1), acked(9, 2), lost(8, 1), lost(6, 2), plain]);
        assert_eq!(out.probes_passed, 0);
        assert_eq!(out.probe_acked[1], Some((1452, 7)));
        assert_eq!(out.probe_acked[2], Some((1452, 9)));
        assert_eq!(out.probe_lost[1], Some((1452, 8)));
        assert_eq!(out.probe_lost[2], Some((1452, 6)));
    }
}
