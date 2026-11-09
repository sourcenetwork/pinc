//! The endpoint type of a suite node and the memory it runs in.
//!
//! Every node uses one set of table sizes, chosen so a cloud node can hold about forty peers with a few protocol
//! sessions each. The connection memory (a buffer pool and a stream table per slot) is leaked, because the endpoint
//! borrows its slot table for as long as it lives and gives it back to nobody; a node is rebuilt on every restart, so a
//! run leaks one slot table per incarnation. The buffer pool is allocated zeroed, so the pages a connection never
//! touches are never resident.
//!
//! Invariants: the table sizes are constants shared by every node; `D` is ten times `K` as the endpoint requires.

use vinc_core::{Endpoint, Slot};
use vinc_transport::conn::Resources;
use vinc_transport::recovery::LossEstimate;
use vinc_transport::stream::pool::{BufferPool, CHUNK_SIZE, RawChunk};
use vinc_transport::stream::{self, NoSource, Streams};

use crate::suite::crypto::Tracked;

/// Streams per connection.
pub(super) const STREAMS: usize = 8;
/// Chunk ring entries per stream half.
pub(super) const CHUNK_RING: usize = 17;
/// Packets tracked in flight per connection.
pub(super) const IN_FLIGHT: usize = 128;
/// Paths per connection.
pub(super) const PATHS: usize = 4;
/// Sessions in the connection table.
pub const SESSIONS: usize = 96;
/// Entries of the connection id table.
pub(super) const CID_TABLE: usize = 10 * SESSIONS;
/// Prekeys in the responder store.
pub(super) const PREKEYS: usize = 8;
/// Tickets in the responder store.
pub(super) const TICKETS: usize = 16;
/// Tickets this node holds as a client.
pub(super) const CLIENT_TICKETS: usize = 8;
/// Pool chunks (16 KiB each) per connection.
pub const CHUNKS_PER_CONN: usize = 16;

/// The endpoint of a suite node.
pub type Ep = Endpoint<
    'static,
    'static,
    Tracked,
    NoSource,
    STREAMS,
    CHUNK_RING,
    IN_FLIGHT,
    PATHS,
    SESSIONS,
    CID_TABLE,
    PREKEYS,
    TICKETS,
    CLIENT_TICKETS,
>;

type NodeSlot = Slot<'static, Tracked, NoSource, STREAMS, CHUNK_RING, IN_FLIGHT, PATHS>;

/// A leaked table of `SESSIONS` free slots, each with its own memory.
pub(super) fn slots() -> Option<&'static mut [NodeSlot; SESSIONS]> {
    // One zeroed byte allocation for every pool of the table: the operating system maps it lazily (an allocation of
    // zeroed arrays is not lazy in a debug build), so the chunks a connection never uses are never resident.
    let bytes: &'static mut [u8] = Box::leak(vec![0u8; SESSIONS * CHUNKS_PER_CONN * CHUNK_SIZE].into_boxed_slice());
    let (slab, _) = bytes.as_chunks_mut::<CHUNK_SIZE>();
    let table: Vec<NodeSlot> = slab.chunks_mut(CHUNKS_PER_CONN).map(|c| Slot::new(memory(c))).collect();
    let boxed: Box<[NodeSlot; SESSIONS]> = table.into_boxed_slice().try_into().ok()?;
    Some(Box::leak(boxed))
}

fn memory(chunks: &'static mut [RawChunk]) -> Resources<'static, NoSource, STREAMS, CHUNK_RING> {
    let pool = BufferPool::from_slab(chunks);
    let streams: &'static mut Streams<NoSource, STREAMS, CHUNK_RING> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    let loss: &'static LossEstimate = Box::leak(Box::new(LossEstimate::new()));
    Resources { pool, streams, loss }
}
