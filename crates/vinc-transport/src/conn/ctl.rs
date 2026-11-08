//! Control frames that must be sent again when their packet is lost, and how recovery feedback reaches every layer.
//!
//! A [`FrameRef::Control`] carries only a kind and one number, so the frames with a payload (the stream layer's flow
//! control frames) live in a small table keyed by that number. The frames that are fully described by a sequence
//! number (connection ids) or by a flag are re-derived from their owners.
//!
//! Invariants: the table holds at most [`TABLE`] frames in flight, so a packet that cannot record one more stops
//! adding control frames; an entry is removed when its packet is acknowledged or lost, and a lost entry hands its
//! frame back to the layer that produced it.

use vinc_security::TicketBatch;

use super::cid::Cids;
use crate::recovery::{Event, FrameRef, ReceivedPackets};
use crate::stream::pool::BufferPool;
use crate::stream::{ControlFrame, StreamSource, Streams};

/// An acknowledgement of ours was in the packet.
pub(crate) const K_ACK: u8 = 1;
/// A stream-layer control frame; the id keys the table.
pub(crate) const K_STREAM_CTL: u8 = 2;
/// NEW_CONNECTION_ID; the id is the sequence number.
pub(crate) const K_NEW_CID: u8 = 3;
/// RETIRE_CONNECTION_ID; the id is the sequence number.
pub(crate) const K_RETIRE: u8 = 4;
/// NEW_TICKETS.
pub(crate) const K_TICKETS: u8 = 5;
/// READY.
pub(crate) const K_READY: u8 = 6;

const TABLE: usize = 24;

/// What a batch of recovery events turned up for the connection.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct Outcome {
    pub(crate) probe_acked: Option<u32>,
    pub(crate) probe_lost: Option<u32>,
    pub(crate) tickets_acked: bool,
    pub(crate) lost_packets: u32,
    pub(crate) acked_packets: u32,
}

/// Pending control state and the table of frames in flight.
#[derive(Debug)]
pub(crate) struct Ctl {
    table: [Option<(u64, ControlFrame)>; TABLE],
    next_key: u64,
    pub(crate) ready: bool,
    pub(crate) tickets: Option<TicketBatch>,
    pub(crate) tickets_pending: bool,
}

impl Ctl {
    pub(crate) const fn new() -> Self {
        Self {
            table: [None; TABLE],
            next_key: 1,
            ready: false,
            tickets: None,
            tickets_pending: false,
        }
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
#[allow(
    clippy::too_many_arguments,
    reason = "disjoint fields borrowed from the connection by a closure"
)]
pub(crate) fn apply<S: StreamSource, const N: usize, const C: usize, const R: usize>(
    ev: &Event<'_>,
    now: u64,
    streams: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    ctl: &mut Ctl,
    cids: &mut Cids,
    rx: &mut ReceivedPackets<R>,
    out: &mut Outcome,
) {
    match *ev {
        Event::Acked {
            pn,
            frames,
            mtu_probe,
            size,
        } => {
            out.acked_packets += 1;
            if mtu_probe {
                out.probe_acked = Some(size);
            }
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => {
                        streams.on_acked(pool, id, offset, u64::from(len), fin);
                    }
                    FrameRef::Control { kind, id } => acked(kind, id, pn, now, streams, pool, ctl, cids, rx, out),
                }
            }
        }
        Event::LateAcked { pn, frames } => {
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => {
                        streams.on_late_acked(pool, id, offset, u64::from(len), fin);
                    }
                    FrameRef::Control { kind, id } => acked(kind, id, pn, now, streams, pool, ctl, cids, rx, out),
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
            if mtu_probe {
                out.probe_lost = Some(size);
            }
            if !requeue {
                return;
            }
            for f in frames {
                match *f {
                    FrameRef::Stream { id, offset, len, fin } => streams.on_lost(id, offset, u64::from(len), fin),
                    FrameRef::Control { kind, id } => lost(kind, id, streams, ctl, cids),
                }
            }
        }
    }
}

#[allow(
    clippy::too_many_arguments,
    reason = "disjoint fields borrowed from the connection by a closure"
)]
fn acked<S: StreamSource, const N: usize, const C: usize, const R: usize>(
    kind: u8,
    id: u64,
    pn: u64,
    now: u64,
    streams: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    ctl: &mut Ctl,
    cids: &mut Cids,
    rx: &mut ReceivedPackets<R>,
    out: &mut Outcome,
) {
    match kind {
        K_ACK => rx.on_ack_confirmed(pn, now),
        K_STREAM_CTL => {
            if let Some(f) = ctl.take(id) {
                streams.on_control_acked(pool, &f);
            }
        }
        K_NEW_CID => cids.new_acked(id),
        K_RETIRE => cids.retire_acked(id),
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
    cids: &mut Cids,
) {
    match kind {
        K_STREAM_CTL => {
            if let Some(f) = ctl.take(id) {
                streams.on_control_lost(&f);
            }
        }
        K_NEW_CID => cids.new_lost(id),
        K_RETIRE => cids.retire_lost(id),
        K_TICKETS => ctl.tickets_pending = ctl.tickets.is_some(),
        K_READY => ctl.ready = true,
        _ => {}
    }
}
