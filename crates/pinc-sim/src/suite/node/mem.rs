//! The endpoint type of a suite node and the memory it runs in.
//!
//! Every node uses one set of table sizes, chosen so a cloud node can hold about forty peers with a few protocol
//! sessions each. The connection memory (a buffer pool and a stream table per slot) is leaked once per table, because
//! the endpoint borrows its slot table for the life of the endpoint; a table is not freed but handed from an ended
//! endpoint to the next one built on the same thread ([`recycle`], [`slots`]), so a run holds as many tables as it has
//! nodes alive at once and a later run reuses them. The buffer pool is allocated zeroed, so the pages a connection
//! never touches are never resident.
//!
//! Invariants: the table sizes are constants shared by every node; `D` is ten times `K` as the endpoint requires; a
//! table in the free list has every slot free and its memory in place; the slots of a table share one loss estimate,
//! as the slots of an endpoint do, and it starts at zero whenever a table is handed out.

use pinc_core::{Endpoint, Slot};
use pinc_transport::conn::{Resources, Tables};
use pinc_transport::recovery::LossEstimate;
use pinc_transport::stream::pool::{BufferPool, CHUNK_SIZE, RawChunk};
use pinc_transport::stream::{self, Streams};
use pinc_values::source::ValueSource;

use super::values::VStore;
use crate::suite::crypto::Tracked;

/// The stream source of the endpoint: values served from the node's store.
pub(super) type Src = ValueSource<VStore>;

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
/// Pool chunks (16 KiB each) per connection. A stream is admitted only while the pool covers the receive window of
/// every stream, and a hub session carries a stream in each direction, so a session needs room for two windows and the
/// send buffers.
pub const CHUNKS_PER_CONN: usize = 64;

/// The endpoint of a suite node.
pub type Ep = Endpoint<
    'static,
    'static,
    Tracked,
    Src,
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

type NodeSlot = Slot<'static, Tracked, Src, STREAMS, CHUNK_RING, IN_FLIGHT, PATHS>;

thread_local! {
    /// The tables ended endpoints gave back, by the node (index in its world) that last used each.
    static FREE: std::cell::RefCell<std::collections::BTreeMap<usize, &'static mut [NodeSlot; SESSIONS]>> = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
    /// The loss estimate shared by the slots of each table, by the table's address.
    static LOSS: std::cell::RefCell<std::collections::BTreeMap<usize, &'static LossEstimate>> = const { std::cell::RefCell::new(std::collections::BTreeMap::new()) };
}

/// End `ep` of node `owner` and keep its connection table for the next endpoint on this thread.
pub(super) fn recycle(owner: usize, ep: Ep) {
    if let Some(table) = ep.into_slots() {
        FREE.with(|f| f.borrow_mut().insert(owner, table));
    }
}

/// A table of `SESSIONS` free slots, each with its own memory: the one `owner` gave back, else any given back, else a
/// new leaked one. A node gets its own table again in the next incarnation and in the next run of the same world, so
/// the memory a run touched is the memory the next one touches and the process stays flat.
pub(super) fn slots(owner: usize) -> Option<&'static mut [NodeSlot; SESSIONS]> {
    let table = FREE
        .with(|f| {
            let mut f = f.borrow_mut();
            let key = if f.contains_key(&owner) {
                Some(owner)
            } else {
                f.keys().next().copied()
            };
            key.and_then(|k| f.remove(&k))
        })
        .or_else(new_table)?;
    let key = std::ptr::from_ref::<[NodeSlot; SESSIONS]>(table) as usize;
    if let Some(loss) = LOSS.with(|l| l.borrow().get(&key).copied()) {
        loss.reset();
    }
    Some(table)
}

fn new_table() -> Option<&'static mut [NodeSlot; SESSIONS]> {
    // One zeroed byte allocation for every pool of the table: the operating system maps it lazily (an allocation of
    // zeroed arrays is not lazy in a debug build), so the chunks a connection never uses are never resident.
    let bytes: &'static mut [u8] = Box::leak(vec![0u8; SESSIONS * CHUNKS_PER_CONN * CHUNK_SIZE].into_boxed_slice());
    let (slab, _) = bytes.as_chunks_mut::<CHUNK_SIZE>();
    let loss: &'static LossEstimate = Box::leak(Box::new(LossEstimate::new()));
    let table: Vec<NodeSlot> = slab
        .chunks_mut(CHUNKS_PER_CONN)
        .map(|c| Slot::new(memory(c, loss)))
        .collect();
    let boxed: Box<[NodeSlot; SESSIONS]> = table.into_boxed_slice().try_into().ok()?;
    let table = Box::leak(boxed);
    LOSS.with(|l| {
        l.borrow_mut()
            .insert(std::ptr::from_ref::<[NodeSlot; SESSIONS]>(table) as usize, loss)
    });
    Some(table)
}

fn memory(
    chunks: &'static mut [RawChunk],
    loss: &'static LossEstimate,
) -> Resources<'static, Src, STREAMS, CHUNK_RING, IN_FLIGHT> {
    let pool = BufferPool::from_slab(chunks);
    let streams: &'static mut Streams<Src, STREAMS, CHUNK_RING> =
        Box::leak(Box::new(Streams::new(&stream::Config::new(false), &pool)));
    Resources {
        pool,
        streams: streams.into(),
        loss: loss.into(),
        tables: Tables::new(),
    }
}
