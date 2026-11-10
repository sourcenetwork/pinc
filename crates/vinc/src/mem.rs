//! The shape of the endpoint a driver runs, and the memory its connections use.
//!
//! The endpoint's tables are const-generic, so the driver builds one of a ladder of shapes: the smallest of
//! [`CAPACITIES`](crate::CAPACITIES) that holds [`Limits::connections`] sessions. Every shape has [`STREAMS`] stream slots per session
//! and [`RING`] chunk entries per stream half. What varies at run time is the pool of 16 KiB chunks each session may
//! use ([`Limits::pool_chunks`]). The memory is allocated once, when the engine starts, and freed when it stops;
//! nothing is leaked.
//!
//! # Memory
//!
//! Per session, reserved up front for every slot of the shape: about 360 KiB of tables (a connection of 156 KiB and a
//! stream table of 203 KiB, both built when the engine starts) plus the endpoint's own tables of about 1 KiB. The
//! 16 KiB chunk pool of a session is zero-filled memory the system commits only as it is used, so an idle session
//! costs address space for `pool_chunks` chunks and almost no resident memory beyond its tables. Per endpoint, besides
//! the sessions: about 470 KiB of fixed tables. So the default 1024 sessions hold about 370 MiB of tables, 4096 hold
//! about 1.4 GiB, and the ceiling of 65536 holds about 23 GiB. The shape is rounded up to the next capacity of the
//! ladder, which doubles at each step: ask for what you need, not for a round number above it.
//!
//! Invariants: the memory of a session returns to its slot when the session ends; the slot table never grows.

use vinc_core::{Endpoint, Slot};
use vinc_crypto::Software;
use vinc_transport::conn::Resources;
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::BufferPool;
use vinc_transport::stream::{self, NoSource, Streams};

use crate::error::{Error, Result};

/// The most sessions an engine can hold: the top of [`CAPACITIES`](crate::CAPACITIES).
pub const MAX_CONNECTIONS: usize = 65_536;
/// The stream slots of a session, both directions of opening counted.
pub const STREAMS: usize = 72;
/// The chunk entries of one stream half.
pub const RING: usize = 65;
pub(crate) const FLIGHT: usize = 128;
pub(crate) const PATHS: usize = 4;
pub(crate) const PREKEYS: usize = 8;
pub(crate) const TICKETS: usize = 64;
pub(crate) const CLIENT_TICKETS: usize = 32;

/// The endpoint a driver runs, for a table of `K` sessions and `D` connection id entries (ten per session).
pub(crate) type Ep<'s, 'a, const K: usize, const D: usize> =
    Endpoint<'s, 'a, Software, NoSource, STREAMS, RING, FLIGHT, PATHS, K, D, PREKEYS, TICKETS, CLIENT_TICKETS>;
/// One slot of its table.
pub(crate) type EpSlot<'a> = Slot<'a, Software, NoSource, STREAMS, RING, FLIGHT, PATHS>;

/// The sizes a driver runs with; each has a default and a hard ceiling.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Limits {
    /// The most sessions at once (at most [`MAX_CONNECTIONS`]). The memory for the next capacity of [`CAPACITIES`](crate::CAPACITIES)
    /// at or above it is reserved when the engine starts; see the module docs for what that costs.
    pub connections: usize,
    /// The 16 KiB chunks one session may hold for its streams and datagrams (at least 8). The default of 512 is 8 MiB:
    /// the pool of every session is reserved at start, so raise it for a few busy sessions, not for thousands.
    pub pool_chunks: usize,
    /// The receive window of each stream in bytes. The pool must cover the window of every stream the peer may open at
    /// once (`streams` times this), or the peer's extra streams are refused as busy.
    pub stream_window: u64,
    /// The most streams the peer may have open at once on a session (at most 64).
    pub streams: u16,
    /// The most streams the peer may open that the application has not accepted, per session.
    pub accept_streams: usize,
    /// The most sessions accepted but not yet taken by the application.
    pub accept_sessions: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            connections: 1024,
            pool_chunks: 512,
            stream_window: 256 * 1024,
            streams: 64,
            accept_streams: 64,
            accept_sessions: 64,
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
            && (16 * 1024..=16 * 1024 * 1024).contains(&self.stream_window)
            && (1..=64).contains(&self.streams)
            && self.accept_streams >= 1
            && self.accept_sessions >= 1;
        if ok {
            Ok(())
        } else {
            Err(Error::config("a limit is out of range"))
        }
    }
}

/// A table of `K` slots over memory that lives for the rest of the process. The endpoint borrows its slots for its whole
/// life, so the memory is allocated once and handed back through [`Endpoint::into_slots`](vinc_core::Endpoint) to the
/// process-wide pool of [`node`](crate::node), where the next endpoint of the same shape takes it; it is never returned
/// to the system.
// vertexia: the pool holds the peak number of live endpoints; a slot table that owns its memory in vinc-core would free it
pub(crate) type Table<const K: usize> = &'static mut [EpSlot<'static>; K];

/// A new table of `K` slots with `chunks` pool chunks each.
///
/// # Errors
/// [`ErrorKind::Config`](crate::ErrorKind::Config) if the table cannot be made.
#[inline(never)]
pub(crate) fn new_table<const K: usize>(chunks: usize) -> Result<Table<K>> {
    let pool = BufferPool::new_boxed(1);
    let cfg = stream::Config::new(false);
    let streams: &'static mut [Streams<NoSource, STREAMS, RING>] =
        Box::leak((0..K).map(|_| Streams::new(&cfg, &pool)).collect());
    let loss: &'static LossEstimate = Box::leak(Box::new(LossEstimate::new()));
    let v: Vec<EpSlot<'static>> = streams
        .iter_mut()
        .map(|s| {
            Slot::new(Resources {
                pool: BufferPool::new_boxed(chunks),
                streams: s,
                loss,
            })
        })
        .collect();
    let boxed: Box<[EpSlot<'static>; K]> = v
        .into_boxed_slice()
        .try_into()
        .map_err(|_| Error::config("the slot table has the wrong size"))?;
    Ok(Box::leak(boxed))
}
