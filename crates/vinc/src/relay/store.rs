//! What a relay keeps across a restart: the signed records it stores.
//!
//! The relay's identity is the host's (the key store passed to the builder). The records are verified when they are
//! stored and again when they are restored, so a store that was tampered with can hand back nothing the relay would
//! not have accepted from a member. The mailbox is not kept: the state machine holds packets for sleeping members in
//! memory only, and a restart drops them (the members' own retransmissions recover them).

use alloc::collections::BTreeMap;
use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;

use vinc_crypto::NodeId;

use crate::error::Result;

/// Storage for the relay's signed records. Methods take `&self`: an implementation keeps its own interior state.
pub trait Store {
    /// Every record stored so far, each as the bytes the publisher signed. The set is bounded by
    /// [`RECORDS`](super::RECORDS).
    fn load(&self) -> impl Future<Output = Result<Vec<Vec<u8>>>>;

    /// Keep `record`, the newest signed record of `node`.
    fn put(&self, node: &NodeId, record: &[u8]) -> impl Future<Output = Result<()>>;
}

/// The in-memory [`Store`]: clones share one table, so a second relay built from a clone sees what the first kept.
#[derive(Debug, Clone, Default)]
pub struct MemStore {
    records: Rc<RefCell<BTreeMap<[u8; 33], Vec<u8>>>>,
}

impl MemStore {
    /// An empty store.
    pub fn new() -> Self {
        Self::default()
    }

    /// How many records it holds.
    pub fn len(&self) -> usize {
        self.records.borrow().len()
    }

    /// Whether it holds none.
    pub fn is_empty(&self) -> bool {
        self.records.borrow().is_empty()
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
    async fn load(&self) -> Result<Vec<Vec<u8>>> {
        Ok(self.records.borrow().values().cloned().collect())
    }

    async fn put(&self, node: &NodeId, record: &[u8]) -> Result<()> {
        self.records.borrow_mut().insert(node_key(node), record.to_vec());
        Ok(())
    }
}
