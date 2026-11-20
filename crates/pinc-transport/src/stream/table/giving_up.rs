//! The application-facing and peer-driven giving-up calls of the stream table: stop requests, resets, and the
//! frames that carry them.
//!
//! A child of the table so it reaches the table's private slots and helpers.

use super::Streams;
use crate::stream::pool::BufferPool;
use crate::stream::{StreamError, StreamId, StreamSource, is_uni};

impl<S: StreamSource, const N: usize, const C: usize> Streams<S, N, C> {
    /// A stop request arrived for a stream we send on: reset it with `error_code`. Returns whether this call reset it
    /// (false if it was already reset, finished or gone).
    ///
    /// # Errors
    /// [`StreamError::StreamState`] for a stream we cannot send on; the errors of opening a peer stream as in
    /// [`Streams::on_stream_frame`].
    pub fn on_stop_sending(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        error_code: u64,
    ) -> Result<bool, StreamError> {
        if is_uni(id) && !self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(pool, id)? else {
            return Ok(false);
        };
        let fresh = self.slots.get(i).is_some_and(|s| s.send.can_stop());
        let result = self
            .with_send(i, |send| send.reset(pool, error_code))
            .unwrap_or(Err(StreamError::UnknownStream));
        self.settle(pool, i);
        result.map(|()| fresh)
    }

    /// Ask the peer to stop sending on a stream we receive on; it resets the stream with `error_code`. The request is
    /// queued as a control frame and sent again if lost.
    /// A stream whose end already arrived is not asked: its bytes are dropped and it counts as read to its end, so it
    /// leaves the table once its send half is done and the peer gets its place in the stream limit back.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`], or [`StreamError::StreamState`] for a stream we cannot receive on.
    pub fn stop_sending(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        error_code: u64,
    ) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        if !slot.recv.open {
            return Err(StreamError::StreamState);
        }
        if slot.recv.request_stop(pool, error_code) {
            self.settle(pool, i);
        } else {
            self.refresh(i);
        }
        Ok(())
    }

    /// A stream reset frame arrived.
    ///
    /// # Errors
    /// As [`Streams::on_stream_frame`].
    pub fn on_reset_stream(
        &mut self,
        pool: &mut BufferPool<'_>,
        id: StreamId,
        error_code: u64,
        final_size: u64,
    ) -> Result<(), StreamError> {
        if is_uni(id) && self.is_local(id) {
            return Err(StreamError::StreamState);
        }
        let Some(i) = self.locate(pool, id)? else { return Ok(()) };
        let slot = self.slots.get_mut(i).ok_or(StreamError::UnknownStream)?;
        let result = slot.recv.on_reset(pool, error_code, final_size);
        self.settle(pool, i);
        result
    }

    /// Abandon the send side: drop its buffers and queue a stream reset.
    ///
    /// # Errors
    /// [`StreamError::UnknownStream`] or [`StreamError::StreamState`] for a receive-only stream.
    pub fn reset(&mut self, pool: &mut BufferPool<'_>, id: StreamId, error_code: u64) -> Result<(), StreamError> {
        let i = self.require(id)?;
        let result = self
            .with_send(i, |send| send.reset(pool, error_code))
            .unwrap_or(Err(StreamError::UnknownStream));
        self.settle(pool, i);
        result
    }
}
