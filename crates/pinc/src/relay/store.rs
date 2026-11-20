//! What a relay keeps across a restart: the signed records it stores and the packets it holds for sleeping members.
//!
//! The relay's identity is the host's (the key store passed to the builder). Records are verified when they are stored
//! and again when they are restored, so a store that was tampered with can hand back nothing the relay would not have
//! accepted from a member. A record is written with the time it was received and comes back with it, so its remaining
//! lifetime is the same after a restart; a record the relay dropped by lifetime is removed. A member's held packets
//! are written whole each time they change (they are bounded by [`MAILBOX_BYTES`](super::MAILBOX_BYTES)) and are
//! opaque to the store.

use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;

use pinc_crypto::NodeId;

use crate::error::Result;

/// A record the store kept and when the relay received it, in the relay's clock (nanoseconds since the Unix epoch).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct KeptRecord {
    /// The record as its publisher signed it.
    pub bytes: Vec<u8>,
    /// When it was received.
    pub received: u64,
}

/// Everything a store kept.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Kept {
    /// The records the store kept. The relay keeps at most [`RECORDS`](super::RECORDS) of them and removes the rest.
    pub records: Vec<KeptRecord>,
    /// The packets held for sleeping members, as [`Store::put_mailbox`] was given them.
    pub mailboxes: Vec<(NodeId, Vec<u8>)>,
}

/// Storage for what the relay keeps. Methods take `&self`: an implementation keeps its own interior state.
///
/// A write may be repeated (a failed one is tried again, and one in flight when a run ends is tried again in the
/// next), so every write must be idempotent: `remove` of a node the store does not hold is `Ok`.
///
/// The relay holds at most [`RECORDS`](super::RECORDS) records, but while the store refuses removals it may hold more,
/// by at most the removals still owed or given up; the relay's own memory does not grow with it.
pub trait Store {
    /// Everything stored so far.
    fn load(&self) -> impl Future<Output = Result<Kept>>;

    /// Keep `record`, the newest signed record of `node`, received at `received`.
    fn put(&self, node: &NodeId, record: &[u8], received: u64) -> impl Future<Output = Result<()>>;

    /// Forget the record of `node`. A removal the store refuses is tried again a bounded number of times and then left for the
    /// next start, and each refusal is counted in the relay's store errors.
    fn remove(&self, node: &NodeId) -> impl Future<Output = Result<()>>;

    /// Keep the packets held for `node`; an empty `packets` means none are held and forgets them.
    fn put_mailbox(&self, node: &NodeId, packets: &[u8]) -> impl Future<Output = Result<()>>;
}

/// The in-memory [`Store`]: clones share one table, so a second relay built from a clone sees what the first kept.
#[derive(Debug, Clone, Default)]
pub struct MemStore {
    state: Rc<RefCell<Mem>>,
}

#[derive(Debug, Default)]
struct Mem {
    records: BTreeMap<[u8; 33], (NodeId, KeptRecord)>,
    mailboxes: BTreeMap<[u8; 33], (NodeId, Vec<u8>)>,
}

impl MemStore {
    /// An empty store.
    pub fn new() -> Self {
        Self::default()
    }

    /// How many records it holds.
    pub fn len(&self) -> usize {
        self.state.borrow().records.len()
    }

    /// Whether it holds no record.
    pub fn is_empty(&self) -> bool {
        self.state.borrow().records.is_empty()
    }

    /// How many members have packets kept.
    pub fn mailboxes(&self) -> usize {
        self.state.borrow().mailboxes.len()
    }

    /// The bytes kept for the packets held for sleeping members.
    pub fn mailbox_bytes(&self) -> usize {
        self.state.borrow().mailboxes.values().map(|(_, b)| b.len()).sum()
    }

    /// When the record of `node` was received, if it is kept.
    pub fn received(&self, node: &NodeId) -> Option<u64> {
        self.state
            .borrow()
            .records
            .get(&node_key(node))
            .map(|(_, r)| r.received)
    }
}

/// The table key of a node: its algorithm tag and id bytes.
pub(crate) fn node_key(node: &NodeId) -> [u8; 33] {
    let mut k = [node.alg.tag(); 33];
    k.iter_mut().skip(1).zip(node.bytes).for_each(|(d, s)| *d = s);
    k
}

#[allow(clippy::unused_async_trait_impl, reason = "the in-memory store never waits")]
impl Store for MemStore {
    async fn load(&self) -> Result<Kept> {
        let s = self.state.borrow();
        Ok(Kept {
            records: s.records.values().map(|(_, r)| r.clone()).collect(),
            mailboxes: s.mailboxes.values().cloned().collect(),
        })
    }

    async fn put(&self, node: &NodeId, record: &[u8], received: u64) -> Result<()> {
        let kept = KeptRecord {
            bytes: record.to_vec(),
            received,
        };
        self.state.borrow_mut().records.insert(node_key(node), (*node, kept));
        Ok(())
    }

    async fn remove(&self, node: &NodeId) -> Result<()> {
        self.state.borrow_mut().records.remove(&node_key(node));
        Ok(())
    }

    async fn put_mailbox(&self, node: &NodeId, packets: &[u8]) -> Result<()> {
        let mut s = self.state.borrow_mut();
        if packets.is_empty() {
            s.mailboxes.remove(&node_key(node));
        } else {
            s.mailboxes.insert(node_key(node), (*node, packets.to_vec()));
        }
        Ok(())
    }
}
