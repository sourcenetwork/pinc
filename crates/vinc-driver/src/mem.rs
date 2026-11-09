//! The fixed shape of the endpoint a driver runs, and the memory its connections use.
//!
//! The endpoint's tables are const-generic, so a driver picks one shape: [`MAX_CONNECTIONS`] sessions, [`STREAMS`]
//! streams per session, and [`RING`] chunk entries per stream half. What varies at run time is the pool of 16 KiB
//! chunks each session may use ([`Limits::pool_chunks`]). The memory is allocated once, when the engine starts, and
//! freed when it stops; nothing is leaked.
//!
//! Invariants: the memory of a session returns to its slot when the session ends; the slot table never grows.

use vinc_core::{Endpoint, Slot};
use vinc_crypto::Software;
use vinc_transport::conn::Resources;
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};

use crate::error::{Error, Result};

/// The most sessions at once.
pub const MAX_CONNECTIONS: usize = 32;
/// The stream slots of a session, both directions of opening counted.
pub const STREAMS: usize = 72;
/// The chunk entries of one stream half.
pub const RING: usize = 65;
const FLIGHT: usize = 128;
const PATHS: usize = 4;
const CIDS: usize = 512;
const PREKEYS: usize = 8;
const TICKETS: usize = 64;
const CLIENT_TICKETS: usize = 32;

/// The endpoint a driver runs.
pub(crate) type Ep<'s, 'a> = Endpoint<
    's,
    'a,
    Software,
    NoSource,
    STREAMS,
    RING,
    FLIGHT,
    PATHS,
    MAX_CONNECTIONS,
    CIDS,
    PREKEYS,
    TICKETS,
    CLIENT_TICKETS,
>;
/// One slot of its table.
pub(crate) type EpSlot<'a> = Slot<'a, Software, NoSource, STREAMS, RING, FLIGHT, PATHS>;

/// The sizes a driver runs with; each has a default and a hard ceiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most sessions at once (at most [`MAX_CONNECTIONS`]).
    pub connections: usize,
    /// The 16 KiB chunks one session may hold for its streams and datagrams (at least 8).
    pub pool_chunks: usize,
    /// The receive window of each stream in bytes. The pool must cover the window of every stream the peer may open at
    /// once (`streams` times this), or the peer's extra streams are refused as busy.
    pub stream_window: u64,
    /// The most streams the peer may have open at once on a session (at most 64).
    pub streams: u16,
    /// The most blocks of 16 KiB a stream holds in each direction outside the endpoint (at least 1).
    pub stream_blocks: usize,
    /// The most streams the peer may open that the application has not accepted, per session.
    pub accept_streams: usize,
    /// The most sessions accepted but not yet taken by the application.
    pub accept_sessions: usize,
    /// The most requests waiting for the engine.
    pub requests: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            connections: MAX_CONNECTIONS,
            pool_chunks: 2048,
            stream_window: 512 * 1024,
            streams: 64,
            stream_blocks: 16,
            accept_streams: 64,
            accept_sessions: 64,
            requests: 1024,
        }
    }
}

impl Limits {
    /// Check the limits against the ceilings.
    ///
    /// # Errors
    /// [`ErrorKind::Config`](crate::ErrorKind::Config) naming the limit that is out of range.
    pub fn check(&self) -> Result<()> {
        let ok = (1..=MAX_CONNECTIONS).contains(&self.connections)
            && (8..=65_536).contains(&self.pool_chunks)
            && (1..=1024).contains(&self.stream_blocks)
            && (16 * 1024..=16 * 1024 * 1024).contains(&self.stream_window)
            && (1..=64).contains(&self.streams)
            && self.accept_streams >= 1
            && self.accept_sessions >= 1
            && self.requests >= 1;
        if ok {
            Ok(())
        } else {
            Err(Error::config("a limit is out of range"))
        }
    }
}

/// The streams and loss average the slots borrow.
pub(crate) struct Memory {
    streams: Vec<Streams<NoSource, STREAMS, RING>>,
    loss: LossEstimate,
}

impl Memory {
    pub(crate) fn new() -> Self {
        let pool = BufferPool::new_boxed(1);
        let cfg = stream::Config::new(false);
        let streams = (0..MAX_CONNECTIONS).map(|_| Streams::new(&cfg, &pool)).collect();
        Self {
            streams,
            loss: LossEstimate::new(),
        }
    }

    /// The slot table over this memory.
    pub(crate) fn slots(&mut self, chunks: usize) -> Result<Box<[EpSlot<'_>; MAX_CONNECTIONS]>> {
        let loss = &self.loss;
        let v: Vec<EpSlot<'_>> = self
            .streams
            .iter_mut()
            .map(|s| {
                Slot::new(Resources {
                    pool: BufferPool::new_boxed(chunks),
                    streams: s,
                    loss,
                })
            })
            .collect();
        v.into_boxed_slice()
            .try_into()
            .map_err(|_| Error::config("the slot table has the wrong size"))
    }
}
