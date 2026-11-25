//! Discovery by signed records: a node publishes a record of its addresses and up to [`MAX_HINTS`] bytes of
//! application hints, signed by its identity, to a [`Rendezvous`]; a peer that dials it by node id alone fetches the
//! record, checks the signature and the key to node id binding itself, and dials the addresses.
//!
//! The record is the connectivity layer's (`pinc_connect::record`): the same bytes a relay stores and replicates, so
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
//! Invariants: the known records are verified, each is the newest of its node seen while it was held (a lower sequence
//! number never replaces a higher one), and there are at most [`KNOWN_MAX`]; past that one held record is forgotten,
//! and that node's next lookup takes what the store holds (a stale record there costs one failed dial, never a wrong
//! node); a borrow of the table lasts one call and is
//! never held across an await.

use alloc::vec::Vec;
use core::cell::{Cell, RefCell};
use core::future::Future;
use core::net::SocketAddr;

use pinc_connect::record::{MAX_HINT_LEN, Record};
use pinc_crypto::NodeId;

use crate::endpoint::Discovery;
use crate::error::Result;
use crate::maps::{self, Keys, Map};

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
    /// The record in `bytes` if it verifies and is `node`'s. A record with sequence number 0 verifies too: a signer can
    /// make one. [`newest`] replaces a known record only by a higher number, so while the table of known records holds
    /// the node's record, one with number 0 changes nothing; once the table forgot the node (see `remember`), any
    /// record of it stands again as its first, number 0 included, as for every number.
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
        // Full: forget one record, an arbitrary peer's; that peer's next lookup takes whatever the store holds.
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
    /// `None` until the endpoint is built hands over its keys: a `Records` used on its own caches nothing.
    known: RefCell<Option<Map<NodeId, PeerRecord>>>,
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
            known: RefCell::new(None),
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
        self.find_held(node).await.0
    }

    /// As [`find`](Self::find), and whether the store itself held a verified record of `node` (a record only
    /// remembered does not count).
    pub(crate) async fn find_held(&self, node: &NodeId) -> (Option<PeerRecord>, bool) {
        let fetched = self
            .store
            .fetch(node)
            .await
            .and_then(|b| PeerRecord::verified(node, &b));
        let held = fetched.is_some();
        (self.note(node, fetched), held)
    }

    /// Keep `fetched` if it is newer than what is known of `node`; the newest known record.
    pub(crate) fn note(&self, node: &NodeId, fetched: Option<PeerRecord>) -> Option<PeerRecord> {
        let mut table = self.known.try_borrow_mut().ok()?;
        let Some(known) = table.as_mut() else {
            return fetched;
        };
        let best = newest(known.get(node), fetched)?;
        remember(known, *node, best.clone());
        Some(best)
    }

    pub(crate) async fn put(&self, record: &[u8]) -> Result<()> {
        self.store.publish(record).await
    }
}

impl<R: Rendezvous> Discovery for Records<R> {
    /// The table of known records is made when the endpoint is built, from its keys; a `Records` used on its own has
    /// no table and every lookup takes what the store holds.
    fn seed_maps(&self, seed: u64, secrets: &'static [u64; 7]) {
        if let Ok(mut known) = self.known.try_borrow_mut()
            && known.is_none()
        {
            *known = Some(maps::map(Keys::from_parts(seed, secrets)));
        }
    }

    async fn lookup(&self, node: &NodeId) -> Vec<SocketAddr> {
        self.find(node).await.map_or_default(|r| r.addrs)
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use alloc::vec;

    use pinc_crypto::IdentityAlg;

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
        let mut known = maps::map(Keys::for_tests(1));
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
        let mut known = maps::map(Keys::for_tests(2));
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
    fn a_record_a_relay_found_is_not_replaced_by_an_older_one_from_the_store() {
        let records = Records::new(Empty);
        let secrets: &'static [u64; 7] = &[1, 2, 3, 4, 5, 6, 7];
        records.seed_maps(5, secrets);
        // The record a relay answered is kept; an older one the store answers later does not replace it.
        assert_eq!(records.note(&node(1), Some(record(1, 5))).map(|r| r.seq), Some(5));
        assert_eq!(records.note(&node(1), Some(record(1, 3))).map(|r| r.seq), Some(5));
        assert_eq!(records.note(&node(1), None).map(|r| r.seq), Some(5));
    }

    #[test]
    fn find_says_whether_the_store_itself_held_a_record() {
        use core::pin::pin;
        use core::task::{Context, Poll, Waker};

        use pinc_connect::record::{self, MAX_RECORD_LEN, Reach, RecordFields};
        use pinc_crypto::Keypair;

        struct Held(Option<Vec<u8>>);

        impl Rendezvous for Held {
            fn publish(&self, _record: &[u8]) -> impl Future<Output = Result<()>> {
                core::future::ready(Ok(()))
            }

            fn fetch(&self, _node: &NodeId) -> impl Future<Output = Option<Vec<u8>>> {
                core::future::ready(self.0.clone())
            }
        }

        // The stores answer at once: one poll settles the future.
        fn ready<T>(f: impl Future<Output = T>) -> T {
            let mut f = pin!(f);
            match f.as_mut().poll(&mut Context::from_waker(Waker::noop())) {
                Poll::Ready(v) => Some(v),
                Poll::Pending => None,
            }
            .unwrap()
        }

        let key = Keypair::from_seed(IdentityAlg::Ed25519, &[7; 32]).unwrap();
        let me = key.node_id();
        let mut bytes = vec![0u8; MAX_RECORD_LEN];
        let fields = RecordFields {
            home: me,
            seq: 3,
            reach: Reach::Public,
            addrs: &[],
            hints: &[],
        };
        let len = record::sign(&key, &fields, &mut bytes).unwrap();
        bytes.truncate(len);
        let secrets: &'static [u64; 7] = &[1, 2, 3, 4, 5, 6, 7];
        let remembered = PeerRecord {
            node: me,
            seq: 5,
            addrs: Vec::new(),
            hints: Vec::new(),
        };

        let records = Records::new(Held(None));
        records.seed_maps(5, secrets);
        records.note(&me, Some(remembered.clone()));
        let (best, held) = ready(records.find_held(&me));
        assert_eq!(best.map(|r| r.seq), Some(5), "the remembered record is the answer");
        assert!(!held, "the store holds none");

        let records = Records::new(Held(Some(bytes)));
        records.seed_maps(5, secrets);
        records.note(&me, Some(remembered));
        let (best, held) = ready(records.find_held(&me));
        assert!(held, "the store holds one");
        assert_eq!(
            best.map(|r| r.seq),
            Some(5),
            "the newest of the stored and the remembered"
        );
    }

    #[test]
    fn the_endpoint_seeds_an_empty_table_once() {
        let records = Records::new(Empty);
        assert!(records.known.borrow().is_none(), "no table before the endpoint's keys");
        let secrets: &'static [u64; 7] = &[1, 2, 3, 4, 5, 6, 7];
        records.seed_maps(5, secrets);
        remember(records.known.borrow_mut().as_mut().unwrap(), node(1), record(1, 1));
        records.seed_maps(6, secrets);
        assert_eq!(
            records.known.borrow().as_ref().unwrap().len(),
            1,
            "a table holding records keeps them"
        );
    }
}
