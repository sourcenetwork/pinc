//! The send side of the stream table: which slot emits next (urgency, then id), the copy of a chunk out, the
//! acknowledgement and loss of ranges, and the control-frame queue.
//!
//! A child of the table so it reaches the table's private slots; it holds no state of its own.

use super::{HOT_CTL, HOT_NEW, HOT_RETX, NONE, Streams};
use crate::stream::pool::BufferPool;
use crate::stream::{ControlFrame, StreamChunk, StreamError, StreamId, StreamSource};

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// The slot after `floor` in (urgency, id) order that has a frame to send, with its key.
    fn next_hot(&self, floor: Option<(u8, u64)>) -> Option<((u8, u64), usize)> {
        // The order as one number, urgency above id. Folding the pair itself cost a stalled load for every slot, hot or
        // not: a sixth of a sender's time on a bulk transfer, where this runs twice for each packet.
        let rank = |(urgency, id): (u8, u64)| (u128::from(urgency) << 64) | u128::from(id);
        let floor = floor.map(rank);
        let (r, i) = self
            .hot
            .iter()
            .take(self.used())
            .enumerate()
            .filter(|(_, h)| **h & (HOT_RETX | HOT_NEW) != 0)
            .filter_map(|(i, _)| {
                let r = rank((self.slots.get(i)?.urgency, self.ids.get(i).copied()?));
                floor.is_none_or(|f| r > f).then_some((r, i))
            })
            .min()?;
        Some((
            (
                u8::try_from(r >> 64).ok()?,
                u64::try_from(r & u128::from(u64::MAX)).ok()?,
            ),
            i,
        ))
    }

    /// Whether any stream has data or a retransmission to send.
    pub fn has_data_to_send(&self) -> bool {
        self.next_hot(None).is_some()
    }

    /// The next stream frame of at most `budget` data bytes: the first stream in (urgency, id) order that has anything
    /// to send, its retransmissions first (lowest hole first), then new data. A better stream drains before a worse
    /// one gets anything. Copy its data with [`Streams::copy_out`].
    pub fn next_stream_frame(&mut self, budget: usize) -> Option<StreamChunk> {
        let mut floor = None;
        while let Some((key, i)) = self.next_hot(floor) {
            let frame = self.slots.get_mut(i).and_then(|slot| {
                slot.send
                    .next_frame(key.1, true, budget)
                    .or_else(|| slot.send.next_frame(key.1, false, budget))
            });
            self.refresh(i);
            if frame.is_some() {
                return frame;
            }
            floor = Some(key);
        }
        None
    }

    /// Copy the data of a frame returned by [`Streams::next_stream_frame`] into `dst`; returns its length.
    ///
    /// # Errors
    /// [`StreamError::BufferTooSmall`], or [`StreamError::DataUnavailable`] if a source returned fewer bytes than asked
    /// (the range is queued again).
    pub fn copy_out(
        &mut self,
        pool: &BufferPool<'_>,
        chunk: &StreamChunk,
        dst: &mut [u8],
    ) -> Result<usize, StreamError> {
        let i = self.require(chunk.id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.send.copy_out(pool, chunk, dst);
        self.refresh(i);
        result
    }

    // ---- feedback from recovery ---------------------------------------------------------------------------------

    /// The frame was acknowledged: free the bytes it covered.
    pub fn on_acked(&mut self, pool: &mut BufferPool<'_>, id: StreamId, offset: u64, len: u64, fin: bool) {
        if let Some(i) = self.find(id) {
            let overflows = self
                .with_send(i, |send| send.on_acked(pool, offset, len, fin))
                .unwrap_or(0);
            self.stats.range_overflows += overflows as u64;
            self.settle(pool, i);
        }
    }

    /// The frame was declared lost: queue its range again, lowest first.
    pub fn on_lost(&mut self, id: StreamId, offset: u64, len: u64, fin: bool) {
        if let Some(i) = self.find(id) {
            let overflows = self.slots.get_mut(i).map_or(0, |s| s.send.on_lost(offset, len, fin));
            self.stats.range_overflows += overflows as u64;
            self.refresh(i);
        }
    }

    /// A frame declared lost was acknowledged after all: cancel its queued retransmission. This is the same operation
    /// as [`Streams::on_acked`], which also removes the range from the retransmission queue.
    pub fn on_late_acked(&mut self, pool: &mut BufferPool<'_>, id: StreamId, offset: u64, len: u64, fin: bool) {
        self.on_acked(pool, id, offset, len, fin);
    }

    /// A control frame from [`Streams::pending_control`] was declared lost (or could not be sent): queue it again unless
    /// it was superseded.
    pub fn on_control_lost(&mut self, frame: &ControlFrame) {
        match *frame {
            ControlFrame::MaxStreamData { id, max } => {
                if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i)
                        && max >= slot.recv.win.limit
                    {
                        slot.recv.win.pending = true;
                    }
                    self.refresh(i);
                }
            }
            ControlFrame::MaxStreams { limit } => self.admit.lost(limit),
            ControlFrame::StopSending { id, .. } => {
                if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i) {
                        slot.recv.stop_lost();
                    }
                    self.refresh(i);
                }
            }
            ControlFrame::ResetStream { id, .. } => {
                if let Some(i) = self.find(id) {
                    if let Some(slot) = self.slots.get_mut(i) {
                        slot.send.control_lost(frame);
                    }
                    self.refresh(i);
                }
            }
        }
    }

    /// A control frame was acknowledged. Only a stream reset matters: the stream may close once it is acknowledged.
    pub fn on_control_acked(&mut self, pool: &mut BufferPool<'_>, frame: &ControlFrame) {
        if let ControlFrame::StopSending { id, .. } = *frame {
            if let Some(slot) = self.find(id).and_then(|i| self.slots.get_mut(i)) {
                slot.recv.stop_acked();
            }
        } else if let ControlFrame::ResetStream { id, .. } = *frame
            && let Some(i) = self.find(id)
        {
            if let Some(slot) = self.slots.get_mut(i) {
                slot.send.reset_acked();
            }
            self.settle(pool, i);
        }
    }

    /// The next control frame to send, if any. The frame counts as sent; if it is not sent after all, give it back
    /// with [`Streams::on_control_lost`].
    pub fn pending_control(&mut self) -> Option<ControlFrame> {
        if let Some(limit) = self.admit.take() {
            return Some(ControlFrame::MaxStreams { limit });
        }
        for i in 0..self.used() {
            if self.hot.get(i).is_none_or(|h| h & HOT_CTL == 0) {
                continue;
            }
            let id = self.ids.get(i).copied().unwrap_or(NONE);
            let frame = self.slots.get_mut(i).and_then(|slot| {
                if let Some(f) = slot.send.take_control(id) {
                    return Some(f);
                }
                if let Some(error_code) = slot.recv.take_stop() {
                    return Some(ControlFrame::StopSending { id, error_code });
                }
                if slot.recv.win.pending {
                    slot.recv.win.pending = false;
                    return Some(ControlFrame::MaxStreamData {
                        id,
                        max: slot.recv.win.limit,
                    });
                }
                None
            });
            self.refresh(i);
            if frame.is_some() {
                return frame;
            }
        }
        None
    }
}
