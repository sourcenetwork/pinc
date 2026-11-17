//! The stop requests of the stream table: one the peer sends for a stream we send on, and one we send for a stream we
//! receive on.
//!
//! A child of the table so it reaches the table's private slots; it holds no state of its own. Our own stop abandons
//! the receive half (see `Recv::abandon`): what is buffered is released and what still arrives is checked and
//! discarded.

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
    /// queued as a control frame and sent again if lost. Nothing is queued if the peer already ended the stream. The
    /// receive half is abandoned at once: what is buffered goes back to the pool, what still arrives is checked and
    /// discarded, no more credit is granted, and the slot is freed when the peer's end has arrived and the send half
    /// is done. Calling it again changes nothing.
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
        slot.recv.abandon(pool, error_code);
        self.refresh(i);
        self.settle(pool, i);
        Ok(())
    }
}
