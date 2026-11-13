//! Discovery by signed records: a node publishes a record of its addresses and up to [`MAX_HINTS`] bytes of
//! application hints, signed by its identity, to a [`Rendezvous`]; a peer that dials it by node id alone fetches the
//! record, checks the signature and the key to node id binding itself, and dials the addresses.
//!
//! The record is the connectivity layer's (`vinc_connect::record`): the same bytes a relay stores and replicates, so
//! the store is never trusted to vouch for one. A record that does not verify, or that names another node, is
//! refused before any packet is sent. A record that verifies but is stale (its node moved and someone else now holds
//! the address) costs one failed handshake: the handshake authenticates the node id, so the dial to the wrong holder
//! fails and nothing is accepted from it.
//!
//! [`Records`] is the [`Discovery`] the builder takes (`Builder::discovery(Records::new(store))`); the endpoint then
//! has [`publish_record`](crate::Endpoint::publish_record), [`set_hints`](crate::Endpoint::set_hints) and
//! [`lookup`](crate::Endpoint::lookup). The store is the host's: an in-process table for tests, and the node's home
//! relay once the connectivity client runs under the facade.
//!
//! Invariants: the known records are verified, each is the newest of its node seen so far (a lower sequence number
//! never replaces a higher one), and there are at most [`KNOWN_MAX`]; a borrow of the table lasts one call and is
//! never held across an await.

use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::future::Future;
use core::net::SocketAddr;

use vinc_connect::record::{MAX_HINT_LEN, Record};
use vinc_crypto::NodeId;

use crate::endpoint::Discovery;
use crate::error::Result;
use crate::maps::{self, Map};

/// The most hint bytes a record carries.
pub const MAX_HINTS: usize = MAX_HINT_LEN;
/// The most peers whose newest record an endpoint keeps.
pub const KNOWN_MAX: usize = 4096;

/// Where records are published and fetched: a relay, a directory, an in-process table.
pub trait Rendezvous {
    /// Store this node's signed record, replacing its older one.
    fn publish(&self, record: &[u8]) -> impl Future<Output = Result<()>>;
    /// The record the store holds for `node`, as it holds it; `None` if it has none. The endpoint verifies it.
    fn fetch(&self, node: &NodeId) -> impl Future<Output = Option<Vec<u8>>>;
}

/// A peer's record, verified.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PeerRecord {
    /// The node that signed it.
    pub node: NodeId,
    /// Its sequence number: a higher one is newer.
    pub seq: u64,
    /// The addresses it can be dialed at.
    pub addrs: Vec<SocketAddr>,
    /// The application's hints, at most [`MAX_HINTS`] bytes.
    pub hints: Vec<u8>,
}

impl PeerRecord {
    /// The record in `bytes` if it verifies and is `node`'s.
    pub(crate) fn verified(node: &NodeId, bytes: &[u8]) -> Option<Self> {
        let rec = Record::parse_verified(bytes).ok()?;
        (rec.node == *node).then(|| Self {
            node: rec.node,
            seq: rec.seq,
            addrs: rec.addrs().collect(),
            hints: rec.hints.to_vec(),
        })
    }
}

/// Which record stands: the fetched one only if it is newer than the one already known.
pub(crate) fn newest(known: Option<&PeerRecord>, fetched: Option<PeerRecord>) -> Option<PeerRecord> {
    match (known, fetched) {
        (Some(k), Some(f)) if f.seq > k.seq => Some(f),
        (Some(k), _) => Some(k.clone()),
        (None, f) => f,
    }
}

/// Keep `record` as the newest of `node`, forgetting one other peer's record first if the table is at [`KNOWN_MAX`].
fn remember(known: &mut Map<NodeId, PeerRecord>, node: NodeId, record: PeerRecord) {
    if known.len() >= KNOWN_MAX && !known.contains_key(&node) {
        // Full: forget one record; that peer's next lookup takes whatever the store holds.
        let evict = known.keys().next().copied();
        if let Some(k) = evict {
            known.remove(&k);
        }
    }
    known.insert(node, record);
}

/// Discovery by signed records over the store `R`; see the module docs.
pub struct Records<R> {
    store: R,
    pub(crate) hints: RefCell<Vec<u8>>,
    pub(crate) seq: Cell<u64>,
    known: RefCell<Map<NodeId, PeerRecord>>,
}

impl<R> core::fmt::Debug for Records<R> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Records").finish_non_exhaustive()
    }
}

impl<R> Records<R> {
    /// Discovery over `store`, with no hints and no records known.
    pub fn new(store: R) -> Self {
        Self {
            store,
            hints: RefCell::new(Vec::new()),
            seq: Cell::new(0),
            known: RefCell::new(maps::map(0)),
        }
    }

    /// The store.
    pub const fn store(&self) -> &R {
        &self.store
    }
}

impl<R: Rendezvous> Records<R> {
    /// The newest verified record of `node`: what the store holds now if it is newer than what was seen before.
    pub(crate) async fn find(&self, node: &NodeId) -> Option<PeerRecord> {
        let fetched = self
            .store
            .fetch(node)
            .await
            .and_then(|b| PeerRecord::verified(node, &b));
        let mut known = self.known.try_borrow_mut().ok()?;
        let best = newest(known.get(node), fetched)?;
        remember(&mut known, *node, best.clone());
        Some(best)
    }

    pub(crate) async fn put(&self, record: &[u8]) -> Result<()> {
        self.store.publish(record).await
    }
}

impl<R: Rendezvous> Discovery for Records<R> {
    /// The table of known records is empty until the endpoint is built, so it takes the endpoint's seed then; a
    /// `Records` used on its own keeps the fixed one of [`Records::new`].
    fn seed_maps(&self, seed: u64) {
        if let Ok(mut known) = self.known.try_borrow_mut()
            && known.is_empty()
        {
            *known = maps::map(seed);
        }
    }

    async fn lookup(&self, node: &NodeId) -> Vec<SocketAddr> {
        self.find(node).await.map(|r| r.addrs).unwrap_or_default()
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use vinc_crypto::IdentityAlg;

    use super::*;

    fn node(n: u32) -> NodeId {
        let mut bytes = [0u8; 32];
        bytes[..4].copy_from_slice(&n.to_be_bytes());
        NodeId {
            alg: IdentityAlg::Ed25519,
            bytes,
        }
    }

    fn record(n: u32, seq: u64) -> PeerRecord {
        PeerRecord {
            node: node(n),
            seq,
            addrs: Vec::new(),
            hints: Vec::new(),
        }
    }

    #[test]
    fn the_known_table_never_holds_more_than_known_max() {
        let mut known = maps::map(1);
        let extra = 10;
        for n in 0..u32::try_from(KNOWN_MAX + extra).unwrap() {
            remember(&mut known, node(n), record(n, 1));
            assert!(known.len() <= KNOWN_MAX, "after {n}");
            // The record just kept is always in the table.
            assert!(known.contains_key(&node(n)), "after {n}");
        }
        assert_eq!(known.len(), KNOWN_MAX);
    }

    #[test]
    fn a_full_table_replaces_a_known_peer_without_evicting() {
        let mut known = maps::map(2);
        for n in 0..u32::try_from(KNOWN_MAX).unwrap() {
            remember(&mut known, node(n), record(n, 1));
        }
        remember(&mut known, node(7), record(7, 2));
        assert_eq!(known.len(), KNOWN_MAX);
        assert_eq!(known.get(&node(7)).map(|r| r.seq), Some(2));
        assert!((0..u32::try_from(KNOWN_MAX).unwrap()).all(|n| known.contains_key(&node(n))));
    }

    struct Empty;

    impl Rendezvous for Empty {
        fn publish(&self, _record: &[u8]) -> impl Future<Output = Result<()>> {
            core::future::ready(Ok(()))
        }

        fn fetch(&self, _node: &NodeId) -> impl Future<Output = Option<Vec<u8>>> {
            core::future::ready(None)
        }
    }

    #[test]
    fn the_endpoint_seeds_an_empty_table_once() {
        let records = Records::new(Empty);
        records.seed_maps(5);
        assert!(records.known.borrow().is_empty());
        remember(&mut records.known.borrow_mut(), node(1), record(1, 1));
        records.seed_maps(6);
        assert_eq!(records.known.borrow().len(), 1, "a table holding records keeps them");
    }
}
