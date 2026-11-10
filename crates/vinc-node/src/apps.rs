//! What the host gives the layers above the sessions: the value store, the sets to reconcile, and the bundle store
//! with the keys of delay-tolerant delivery.
//!
//! One trait, [`Apps`], bundles the three host interfaces so the node carries one extra type parameter instead of
//! three. [`NoApps`] is the host with none of them: the node then runs membership and broadcast only, and the
//! calls of the other layers answer that the layer is off.
//!
//! Invariants: a layer the host does not enable ([`Apps::enabled`]) never registers its protocol id, never dials
//! and never holds state; the host's stores are borrowed for the length of one call and never kept.

use vinc_crypto::provider::Provider;
use vinc_crypto::{Keypair, NodeId};
use vinc_dtn::forward::Policy;
use vinc_dtn::head::BundleId;
use vinc_dtn::seal::RecipientKeys;
use vinc_reconcile::{ItemIndex, Limits};
use vinc_transport::stream::{NoSource, StreamSource};
use vinc_values::source::ValueSource;
use vinc_values::store::{StoreError, ValueRead, ValueStore};

/// Which layers the node runs.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Enabled {
    /// Fetch values from providers and serve them.
    pub values: bool,
    /// Reconcile sets with peers.
    pub sets: bool,
    /// Carry bundles for delay-tolerant delivery.
    pub dtn: bool,
}

impl Enabled {
    /// No layer above broadcast.
    pub const NONE: Self = Self {
        values: false,
        sets: false,
        dtn: false,
    };
    /// Every layer.
    pub const ALL: Self = Self {
        values: true,
        sets: true,
        dtn: true,
    };
}

/// How a stream source of the endpoint is made from the store-reading source of a response.
///
/// The endpoint is built with one source type for all its streams. A host that serves values builds it with
/// [`ValueSource`]; one that does not, with [`NoSource`], and then a request for a value is answered as unavailable.
pub trait ServeSource<H: ValueRead>: StreamSource + Sized {
    /// The endpoint's source for the response `source`, or `None` if this endpoint cannot serve from a store.
    fn from_source(source: ValueSource<H>) -> Option<Self>;
}

impl<H: ValueRead> ServeSource<H> for ValueSource<H> {
    fn from_source(source: ValueSource<H>) -> Option<Self> {
        Some(source)
    }
}

impl<H: ValueRead> ServeSource<H> for NoSource {
    fn from_source(_source: ValueSource<H>) -> Option<Self> {
        None
    }
}

/// The sets a node reconciles: each is named by a reference the peers agree on.
pub trait SetsApp {
    /// The sorted item index of one set, borrowed from the host for the length of a step.
    type Index<'a>: ItemIndex
    where
        Self: 'a;

    /// The bounds of a session: item, message and report sizes.
    fn limits(&self) -> Limits {
        Limits::default()
    }

    /// The index of the set named `set_ref`, or `None` if this node holds no such set. The set must not change while
    /// a session over it runs.
    fn index(&self, set_ref: &[u8]) -> Option<Self::Index<'_>>;
}

/// The keys a node opens bundles addressed to it with.
#[derive(Debug)]
pub struct Recipient<'a, P: Provider> {
    /// The published keys; `own.node` is this node.
    pub own: &'a RecipientKeys,
    /// The static ML-KEM decapsulation key.
    pub kem_dk: &'a P::KemDecapsKey,
    /// The static X25519 secret.
    pub x25519: &'a P::X25519Secret,
}

/// The host side of delay-tolerant delivery: the bundle store, the keys and the contact rule.
///
/// The bundle store keeps complete bundles (the sealed bytes and the tree outboard) for as long as the node holds
/// them. The node charges every bundle against [`DtnApp::budget`] before it takes it, so the store never holds more.
pub trait DtnApp<P: Provider> {
    /// The key that signs the heads of the bundles this node creates and the custody acknowledgements it sends.
    fn signer(&self) -> Option<&Keypair>;

    /// The keys that open bundles addressed to this node, if it receives any.
    fn recipient(&self) -> Option<Recipient<'_, P>>;

    /// Keep a complete bundle. False if the store cannot take it; the node then refuses the bundle.
    fn put(&mut self, id: &BundleId, sealed: &[u8], outboard: &[u8]) -> bool;

    /// A complete bundle's sealed bytes and outboard.
    fn get(&self, id: &BundleId) -> Option<(&[u8], &[u8])>;

    /// Forget a bundle (delivered, expired or evicted).
    fn remove(&mut self, id: &BundleId);

    /// The bytes the node may hold in bundles, partial ones included at their full size.
    fn budget(&self) -> u64 {
        64 << 20
    }

    /// The retransmission rule of a handover: the wait in milliseconds of link-up time and the sends before giving up.
    fn policy(&self) -> Policy {
        Policy {
            retry_ms: 10_000,
            max_sends: 4,
        }
    }

    /// Whether `peer` is in contact now, at the wall clock `wall_ms`. A peer in contact is dialed while the node holds
    /// bundles; a session with a peer that is not in contact is closed. The default is every peer.
    fn in_contact(&self, _peer: &NodeId, _wall_ms: u64) -> bool {
        true
    }

    /// The wall clock (milliseconds) at which [`in_contact`](Self::in_contact) next changes for any peer, if the rule
    /// follows the clock (a contact window opening or closing); the node looks at its contacts at that moment and not
    /// before. `None`, the default, says the rule does not change by itself.
    fn next_contact_change(&self, _wall_ms: u64) -> Option<u64> {
        None
    }

    /// Keep the node's record of a bundle (opaque bytes) under `id`, replacing the earlier one. The node saves a
    /// record when it makes a bundle, takes custody, hands copies on, and as a partial bundle grows; it drops the
    /// record with [`drop_record`](Self::drop_record). A host that keeps them (with the bundles it stores) lets the
    /// node resume after a restart with [`Node::dtn_restore`](crate::Node::dtn_restore). The default keeps nothing.
    fn save_record(&mut self, _id: &BundleId, _record: &[u8]) {}

    /// Forget the record of a bundle.
    fn drop_record(&mut self, _id: &BundleId) {}

    /// The `n`th record kept, in any order but the same each time, for [`Node::dtn_restore`](crate::Node::dtn_restore).
    fn record_at(&self, _n: usize) -> Option<(BundleId, &[u8])> {
        None
    }
}

/// The three host interfaces of the layers above the sessions.
pub trait Apps<P: Provider> {
    /// The value store: written by fetches, read by the server through cheap clones.
    type Values: ValueStore + Clone;
    /// The sets.
    type Sets: SetsApp;
    /// The bundle store and keys.
    type Dtn: DtnApp<P>;

    /// Which layers to run. Read once, when the node starts.
    fn enabled(&self) -> Enabled;
    /// The value store.
    fn values(&mut self) -> &mut Self::Values;
    /// The sets.
    fn sets(&self) -> &Self::Sets;
    /// The bundle store.
    fn dtn(&mut self) -> &mut Self::Dtn;
}

/// The value store of a node that runs no values layer.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoValues;

impl ValueRead for NoValues {
    fn servable_len(&self, _root: &[u8; 32]) -> Option<u64> {
        None
    }
    fn read_at(&self, _root: &[u8; 32], _offset: u64, _dst: &mut [u8]) -> usize {
        0
    }
    fn read_outboard(&self, _root: &[u8; 32], _offset: u64, _dst: &mut [u8]) -> usize {
        0
    }
}

impl ValueStore for NoValues {
    fn verified_from(&self, _root: &[u8; 32], _from: u64) -> Option<core::ops::Range<u64>> {
        None
    }
    fn write_at(&mut self, _root: &[u8; 32], _offset: u64, _data: &[u8]) -> Result<(), StoreError> {
        Err(StoreError::Full)
    }
    fn commit(&mut self, _root: &[u8; 32], _range: core::ops::Range<u64>) -> Result<(), StoreError> {
        Err(StoreError::Full)
    }
}

/// The sets of a node that reconciles none.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoSets;

/// The index of no set: empty, and never handed out.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoIndex;

impl ItemIndex for NoIndex {
    type Error = ();
    fn count(&self) -> Result<usize, ()> {
        Ok(0)
    }
    fn rank(&self, _bound: &[u8]) -> Result<usize, ()> {
        Ok(0)
    }
    fn read(&self, _i: usize, _buf: &mut [u8]) -> Result<usize, ()> {
        Err(())
    }
    fn fingerprint(&self, _a: usize, _b: usize) -> Result<vinc_reconcile::Fingerprint, ()> {
        Ok(vinc_reconcile::Fingerprint::ZERO)
    }
}

impl SetsApp for NoSets {
    type Index<'a> = NoIndex;
    fn index(&self, _set_ref: &[u8]) -> Option<NoIndex> {
        None
    }
}

/// The bundle store of a node that carries no bundles.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoDtn;

impl<P: Provider> DtnApp<P> for NoDtn {
    fn signer(&self) -> Option<&Keypair> {
        None
    }
    fn recipient(&self) -> Option<Recipient<'_, P>> {
        None
    }
    fn put(&mut self, _id: &BundleId, _sealed: &[u8], _outboard: &[u8]) -> bool {
        false
    }
    fn get(&self, _id: &BundleId) -> Option<(&[u8], &[u8])> {
        None
    }
    fn remove(&mut self, _id: &BundleId) {}
}

/// The host with no layer above broadcast.
#[derive(Debug, Clone, Copy, Default)]
pub struct NoApps {
    values: NoValues,
    sets: NoSets,
    dtn: NoDtn,
}

impl<P: Provider> Apps<P> for NoApps {
    type Values = NoValues;
    type Sets = NoSets;
    type Dtn = NoDtn;

    fn enabled(&self) -> Enabled {
        Enabled::NONE
    }
    fn values(&mut self) -> &mut NoValues {
        &mut self.values
    }
    fn sets(&self) -> &NoSets {
        &self.sets
    }
    fn dtn(&mut self) -> &mut NoDtn {
        &mut self.dtn
    }
}
