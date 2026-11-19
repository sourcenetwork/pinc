//! The host stores of the layers above broadcast for the simulated nodes: a value store, sets, and a bundle store
//! with the node's keys.
#![allow(
    missing_docs,
    dead_code,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use pinc_crypto::provider::Provider;
use pinc_crypto::{IdentityAlg, Keypair, NodeId};
use pinc_dag::ranges::VerifiedRanges;
use pinc_dag::tree::build_outboard_vec;
use pinc_dtn::forward::Policy;
use pinc_dtn::head::BundleId;
use pinc_dtn::seal::RecipientKeys;
use pinc_node::{Apps, DtnApp, Enabled, Recipient, SetsApp};
use pinc_reconcile::{Fingerprint, ItemIndex, Limits, MemError, MemIndex};
use pinc_sim::WALL_EPOCH;
use pinc_values::source::ValueSource;
use pinc_values::store::{StoreError, ValueRead, ValueStore, verified_after};

use crate::node_sim::SimApps;
use crate::{Caps, SplitMix64};

/// A fault of a providing store.
#[derive(Debug, Clone, Copy)]
pub enum Lie {
    /// Flip a bit in the first byte of every read of the value.
    EveryRead,
}

/// One value a node serves.
#[derive(Clone)]
pub struct Provided {
    pub data: Rc<Vec<u8>>,
    pub outboard: Rc<Vec<u8>>,
}

/// One value a node is fetching.
#[derive(Default)]
pub struct Fetched {
    pub data: Vec<u8>,
    pub verified: VerifiedRanges<64>,
}

#[derive(Default)]
pub struct VState {
    pub served: BTreeMap<[u8; 32], Provided>,
    pub fetched: BTreeMap<[u8; 32], Fetched>,
    pub lie: Option<Lie>,
}

/// The value store of a node: cheap to clone, one state behind it.
#[derive(Clone, Default)]
pub struct VStore(pub Rc<RefCell<VState>>);

impl VStore {
    /// Serve `data`; returns its root.
    pub fn provide(&self, data: Vec<u8>) -> [u8; 32] {
        let (root, outboard) = build_outboard_vec(&data, 4).unwrap();
        self.0.borrow_mut().served.insert(
            root,
            Provided {
                data: Rc::new(data),
                outboard: Rc::new(outboard),
            },
        );
        root
    }

    pub fn lie(&self, lie: Option<Lie>) {
        self.0.borrow_mut().lie = lie;
    }

    /// Make room for a value of `len` bytes ahead of its fetch, so the store's writes allocate nothing.
    pub fn reserve(&self, root: &[u8; 32], len: usize) {
        self.0
            .borrow_mut()
            .fetched
            .entry(*root)
            .or_default()
            .data
            .resize(len, 0);
    }

    pub fn covered(&self, root: &[u8; 32]) -> u64 {
        self.0
            .borrow()
            .fetched
            .get(root)
            .map_or(0, |f| f.verified.iter().map(|r| r.end - r.start).sum())
    }

    /// The fetched bytes of `root`, if all of `len` are verified.
    pub fn fetched(&self, root: &[u8; 32], len: u64) -> Option<Vec<u8>> {
        let s = self.0.borrow();
        let f = s.fetched.get(root)?;
        f.verified
            .contains_range(0..len)
            .then(|| f.data.get(..len as usize).unwrap().to_vec())
    }
}

impl ValueRead for VStore {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        self.0.borrow().served.get(root).map(|p| p.data.len() as u64)
    }

    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let s = self.0.borrow();
        let Some(p) = s.served.get(root) else { return 0 };
        let off = offset as usize;
        let n = dst.len().min(p.data.len().saturating_sub(off));
        dst[..n].copy_from_slice(&p.data[off..off + n]);
        if n > 0 && matches!(s.lie, Some(Lie::EveryRead)) {
            dst[0] ^= 1;
        }
        n
    }

    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let s = self.0.borrow();
        let Some(p) = s.served.get(root) else { return 0 };
        let off = offset as usize;
        let n = dst.len().min(p.outboard.len().saturating_sub(off));
        dst[..n].copy_from_slice(&p.outboard[off..off + n]);
        n
    }
}

impl ValueStore for VStore {
    fn verified_from(&self, root: &[u8; 32], from: u64) -> Option<Range<u64>> {
        self.0
            .borrow()
            .fetched
            .get(root)
            .and_then(|f| verified_after(&f.verified, from))
    }

    fn write_at(&mut self, root: &[u8; 32], offset: u64, data: &[u8]) -> Result<(), StoreError> {
        let mut s = self.0.borrow_mut();
        let f = s.fetched.entry(*root).or_default();
        let end = offset as usize + data.len();
        if f.data.len() < end {
            f.data.resize(end, 0);
        }
        f.data[offset as usize..end].copy_from_slice(data);
        Ok(())
    }

    fn commit(&mut self, root: &[u8; 32], range: Range<u64>) -> Result<(), StoreError> {
        let mut s = self.0.borrow_mut();
        s.fetched.entry(*root).or_default().verified.insert(range)?;
        Ok(())
    }
}

/// An index shared by reference.
#[derive(Clone)]
pub struct RcIndex(pub Rc<MemIndex>);

impl ItemIndex for RcIndex {
    type Error = MemError;
    fn count(&self) -> Result<usize, MemError> {
        self.0.count()
    }
    fn rank(&self, bound: &[u8]) -> Result<usize, MemError> {
        self.0.rank(bound)
    }
    fn read(&self, i: usize, buf: &mut [u8]) -> Result<usize, MemError> {
        self.0.read(i, buf)
    }
    fn fingerprint(&self, a: usize, b: usize) -> Result<Fingerprint, MemError> {
        self.0.fingerprint(a, b)
    }
}

#[derive(Clone, Default)]
pub struct SetStore {
    pub sets: BTreeMap<Vec<u8>, Rc<MemIndex>>,
    pub limits: Option<Limits>,
}

impl SetStore {
    pub fn insert(&mut self, name: &[u8], items: &[Vec<u8>]) {
        let mut sorted: Vec<&[u8]> = items.iter().map(Vec::as_slice).collect();
        sorted.sort_unstable();
        sorted.dedup();
        self.sets
            .insert(name.to_vec(), Rc::new(MemIndex::from_sorted(sorted).unwrap()));
    }
}

impl SetsApp for SetStore {
    type Index<'a> = RcIndex;
    fn limits(&self) -> Limits {
        self.limits.unwrap_or_default()
    }
    fn index(&self, set_ref: &[u8]) -> Option<RcIndex> {
        self.sets.get(set_ref).map(|i| RcIndex(i.clone()))
    }
}

/// The secrets and published keys a node opens bundles with.
pub struct Secrets {
    pub keys: RecipientKeys,
    pub dk: <Caps as Provider>::KemDecapsKey,
    pub xs: <Caps as Provider>::X25519Secret,
}

#[derive(Clone)]
pub struct DtnStore {
    pub key: Rc<Keypair>,
    pub secrets: Rc<Secrets>,
    pub bundles: BTreeMap<BundleId, (Vec<u8>, Vec<u8>)>,
    /// The node's records of the bundles it looks after, kept across a restart.
    pub records: BTreeMap<BundleId, Vec<u8>>,
    /// The bytes written to records, saves and appends together.
    pub record_bytes: u64,
    /// Contact windows `(peer, from_ms, to_ms)` in simulated milliseconds; `None` means every peer, always.
    pub windows: Option<Vec<([u8; 32], u64, u64)>>,
    pub budget: u64,
    pub policy: Policy,
}

fn bytes(seed: u64, len: usize) -> Vec<u8> {
    let mut v = vec![0; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

impl DtnStore {
    pub fn new(tag: u8) -> Self {
        let alg = IdentityAlg::Ed25519;
        let key = Keypair::from_seed(alg, &vec![tag; alg.seed_len()]).unwrap();
        let p = Caps(pinc_crypto::Software, true);
        let seed = 0x1000 + u64::from(tag) * 16;
        let d: [u8; 32] = bytes(seed + 1, 32).try_into().unwrap();
        let z: [u8; 32] = bytes(seed + 2, 32).try_into().unwrap();
        let (dk, ek) = p.kem_keygen(&d, &z);
        let xs = p.x25519_secret(&bytes(seed + 3, 32).try_into().unwrap());
        let keys = RecipientKeys {
            node: key.node_id(),
            epoch: 1,
            kem_ek: p.kem_encaps_key_bytes(&ek),
            x25519: p.x25519_public(&xs),
        };
        Self {
            key: Rc::new(key),
            secrets: Rc::new(Secrets { keys, dk, xs }),
            bundles: BTreeMap::new(),
            records: BTreeMap::new(),
            record_bytes: 0,
            windows: None,
            budget: 8 << 20,
            policy: Policy {
                retry_ms: 4_000,
                max_sends: 6,
            },
        }
    }

    pub fn keys(&self) -> RecipientKeys {
        self.secrets.keys
    }
}

impl DtnApp<Caps> for DtnStore {
    fn signer(&self) -> Option<&Keypair> {
        Some(&self.key)
    }

    fn recipient(&self) -> Option<Recipient<'_, Caps>> {
        Some(Recipient {
            own: &self.secrets.keys,
            kem_dk: &self.secrets.dk,
            x25519: &self.secrets.xs,
        })
    }

    fn put(&mut self, id: &BundleId, sealed: &[u8], outboard: &[u8]) -> bool {
        self.bundles.insert(*id, (sealed.to_vec(), outboard.to_vec()));
        true
    }

    fn get(&self, id: &BundleId) -> Option<(&[u8], &[u8])> {
        self.bundles.get(id).map(|(s, o)| (s.as_slice(), o.as_slice()))
    }

    fn remove(&mut self, id: &BundleId) {
        self.bundles.remove(id);
    }

    fn budget(&self) -> u64 {
        self.budget
    }

    fn next_contact_change(&self, wall_ms: u64) -> Option<u64> {
        let w = self.windows.as_ref()?;
        let epoch = WALL_EPOCH / 1_000_000;
        let t = wall_ms.saturating_sub(epoch);
        w.iter()
            .flat_map(|(_, a, b)| [*a, *b])
            .filter(|e| *e > t)
            .min()
            .map(|e| e + epoch)
    }

    fn save_record(&mut self, id: &BundleId, record: &[u8]) {
        self.record_bytes += record.len() as u64;
        self.records.insert(*id, record.to_vec());
    }

    fn append_record(&mut self, id: &BundleId, more: &[u8]) {
        self.record_bytes += more.len() as u64;
        self.records.entry(*id).or_default().extend_from_slice(more);
    }

    fn drop_record(&mut self, id: &BundleId) {
        self.records.remove(id);
    }

    fn record_at(&self, n: usize) -> Option<(BundleId, &[u8])> {
        self.records.iter().nth(n).map(|(id, r)| (*id, r.as_slice()))
    }

    fn policy(&self) -> Policy {
        self.policy
    }

    fn in_contact(&self, peer: &NodeId, wall_ms: u64) -> bool {
        let Some(w) = &self.windows else { return true };
        let t = wall_ms.saturating_sub(WALL_EPOCH / 1_000_000);
        w.iter().any(|(p, a, b)| *p == peer.bytes && *a <= t && t < *b)
    }
}

#[derive(Clone)]
pub struct LayerApps {
    pub enabled: Enabled,
    pub values: VStore,
    pub sets: SetStore,
    pub dtn: DtnStore,
}

impl LayerApps {
    pub fn new(tag: u8, enabled: Enabled) -> Self {
        Self {
            enabled,
            values: VStore::default(),
            sets: SetStore::default(),
            dtn: DtnStore::new(tag),
        }
    }
}

impl Apps<Caps> for LayerApps {
    type Values = VStore;
    type Sets = SetStore;
    type Dtn = DtnStore;

    fn enabled(&self) -> Enabled {
        self.enabled
    }
    fn values(&mut self) -> &mut VStore {
        &mut self.values
    }
    fn sets(&self) -> &SetStore {
        &self.sets
    }
    fn dtn(&mut self) -> &mut DtnStore {
        &mut self.dtn
    }
}

impl SimApps for LayerApps {
    type Src = ValueSource<VStore>;
}
