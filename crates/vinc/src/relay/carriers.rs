//! The host's carriers, as a completion queue: the relay submits operations and the host reports what finished.
//!
//! A relay holds a thousand streams and most are idle. Polling a future per stream costs a poll of every stream at every
//! wake; a completion contract costs the relay O(1) work per finished operation and never scans its streams. The host
//! does the multiplexing in whatever way its runtime does it best: a task per operation and a queue, or the completion
//! queue of the ring it already has.
//!
//! The relay calls the `submit_*` methods, which start an operation and return at once; each operation finishes with one
//! [`Completion`] that carries the [`Tag`] the relay gave and the buffer back. The buffers are owned (see
//! [`crate::carrier`] for the convention: a read fills at most `buf.len()` bytes from the start and returns the count,
//! zero when the peer closed; a write writes from the offset to the end and returns how many bytes went). The relay
//! keeps at most one read and one write in flight per stream and at most one accept.
//!
//! The streams are `Rc`s: the host's operation holds a clone while it runs. To end a stream the relay calls
//! [`Carriers::close`], which names the stream by [`Tag::conn`]; the host abandons what it still has in flight for it
//! (an abandoned operation need not complete, and the relay ignores a completion that arrives late) and closes the
//! stream.
//!
//! Invariants: a completion for a stream the relay already closed is ignored; the relay never submits a second read or
//! write on a stream before the first one's completion; every call is made from the task that runs the relay.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::task::{Context, Poll};

use super::peers::Peer;
use crate::carrier::CarrierKind;
use crate::error::Result;

/// Names an operation the relay submitted; the host hands it back with the completion and never looks inside.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Tag {
    conn: u64,
}

impl Tag {
    pub(crate) const fn new(conn: u64) -> Self {
        Self { conn }
    }

    /// Names the stream the operation is on: the same for every operation on one stream, different for two streams.
    pub const fn conn(self) -> u64 {
        self.conn
    }
}

/// How an operation ended, with the buffer of a read or a write.
#[derive(Debug)]
pub enum Done<S> {
    /// A member opened a stream; its kind says how its bytes travel.
    Accepted(Result<(S, CarrierKind)>),
    /// The stream to a peer relay is open.
    Opened(Result<S>),
    /// A read finished: the count (zero: the peer closed) and the buffer.
    Read(Result<usize>, Vec<u8>),
    /// A write finished: how many bytes went out and the buffer.
    Written(Result<usize>, Vec<u8>),
}

/// A finished operation.
#[derive(Debug)]
pub struct Completion<S> {
    /// The tag the relay gave when it submitted the operation.
    pub tag: Tag,
    /// How it ended.
    pub done: Done<S>,
}

/// The host's carriers: byte streams the relay accepts and opens, reads and writes, and closes.
///
/// A host with a task runtime implements it in a few lines: each `submit_*` spawns a task that does the operation and
/// pushes a [`Completion`] on a queue, [`Carriers::poll_completed`] pops the queue (and keeps the waker if it is empty),
/// and [`Carriers::drive`] never finishes. [`CarrierFns`](super::CarrierFns) builds the same from async closures.
pub trait Carriers {
    /// The host's byte stream.
    type Stream;

    /// Wait for the next stream a member opened (the host has done the TCP accept, or the HTTP upgrade of a WebSocket).
    fn submit_accept(&self, tag: Tag);

    /// Open a stream of `kind` to a peer relay.
    fn submit_open(&self, tag: Tag, peer: &Peer, kind: CarrierKind);

    /// Start a read into `buf`.
    fn submit_read(&self, stream: &Rc<Self::Stream>, tag: Tag, buf: Vec<u8>);

    /// Start a write of `buf` from offset `from`.
    fn submit_write(&self, stream: &Rc<Self::Stream>, tag: Tag, buf: Vec<u8>, from: usize);

    /// End the stream the tag's [`Tag::conn`] names: abandon its operations in flight and close it. The relay does not
    /// wait for it.
    fn close(&self, tag: Tag, stream: Rc<Self::Stream>);

    /// The next finished operation, or [`Poll::Pending`] after arranging that `cx`'s waker is woken when one finishes.
    fn poll_completed(&self, cx: &mut Context<'_>) -> Poll<Completion<Self::Stream>>;

    /// Work the host does in the relay's own task: the relay polls this future for as long as it runs and it never
    /// finishes. A host whose operations run in tasks of its own returns [`core::future::pending`].
    fn drive(&self) -> impl Future<Output = ()>;

    /// The relay's run (or the part that holds these carriers) has ended or been dropped: abandon every operation still
    /// in flight and drop the queued completions. The relay has dropped its streams without calling [`Carriers::close`],
    /// so a stream whose last drop ends its connection is closed once the host lets go of its clones. It can be called
    /// more than once; the default does nothing, which suits a host whose operations are futures the relay's own task
    /// owns.
    fn ended(&self) {}
}
