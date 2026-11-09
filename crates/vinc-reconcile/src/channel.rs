//! The abstract message channel a session runs over.
//!
//! Invariants: the channel is ordered and reliable until it resets. A message is one whole framed message
//! (`len3 | body`); how the host cuts a byte stream into messages is the host's, using [`crate::frame_len`].

use alloc::vec::Vec;

/// What a receive produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Recv {
    /// One whole framed message was written to the buffer.
    Message,
    /// The peer finished the stream cleanly; no more messages come.
    Finished,
    /// The stream was reset; the session is lost and the initiator retries it whole.
    Reset,
}

/// An ordered, reliable stream of framed messages with a reset.
pub trait Channel {
    /// The host's failure.
    type Error;

    /// Send one framed message; `fin` also finishes the sending side. An empty `msg` with `fin` only finishes.
    ///
    /// # Errors
    /// The host's error.
    fn send(&mut self, msg: &[u8], fin: bool) -> Result<(), Self::Error>;

    /// Wait for the next message and write it to `buf` (which the call clears first).
    ///
    /// # Errors
    /// The host's error.
    fn recv(&mut self, buf: &mut Vec<u8>) -> Result<Recv, Self::Error>;

    /// Abort the stream so that the peer sees a reset.
    fn reset(&mut self);
}
