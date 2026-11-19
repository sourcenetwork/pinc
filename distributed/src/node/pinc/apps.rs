//! The host stores of the layers above broadcast for a PINC node program: the values it serves and fetches, the sets
//! it reconciles, and the bundle store of delay-tolerant delivery (see [`super::dtn`]), on when a scenario asks.
//!
//! A served value is generated from its seed at the offset asked, with the tree outboard built once when it is
//! provided; a fetched value is written into one buffer the size of the value, and its verified ranges are kept in the
//! library's own set. Both are behind one `Rc`, because the node and the responses it builds read the same store, on one
//! thread.
//!
//! Invariants: a byte is reported verified only after the fetch checked it against the root and committed it; a value is
//! served only if it was provided here; a set's items are strictly increasing.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use pinc_crypto::Software;
use pinc_dag::ranges::VerifiedRanges;
use pinc_dag::tree::OutboardBuilder;
use pinc_node::{Apps, Enabled, SetsApp};
use pinc_reconcile::{Fingerprint, ItemIndex, Limits, MemError, MemIndex};
use pinc_values::store::{StoreError, ValueRead, ValueStore, verified_after};

use super::dtn::DtnStore;
use crate::node::data::Content;

/// One value this node serves.
struct Served {
    content: Content,
    outboard: Vec<u8>,
}

/// One value this node is fetching.
#[derive(Default)]
struct Fetched {
    data: Vec<u8>,
    verified: VerifiedRanges<64>,
}

#[derive(Default)]
struct State {
    served: BTreeMap<[u8; 32], Served>,
    fetched: BTreeMap<[u8; 32], Fetched>,
}

/// The value store of a node: cheap to clone, one state behind it.
#[derive(Clone, Default)]
pub struct VStore(Rc<RefCell<State>>);

impl VStore {
    /// Make `content` available: build its outboard and return its root.
    ///
    /// # Errors
    /// The tree could not be built for this length.
    pub fn provide(&self, content: &Content) -> Result<[u8; 32], String> {
        const LOG: u32 = 4;
        let tree_err = |_| "the value's tree could not be built".to_owned();
        let mut b = OutboardBuilder::new(content.len(), LOG).map_err(tree_err)?;
        let size = usize::try_from(b.layout().outboard_size()).map_err(|_| "the value is too large".to_owned())?;
        let mut out = vec![0u8; size];
        let mut buf = vec![0u8; 1 << 20];
        let mut off = 0;
        while off < content.len() {
            let n = content.fill(off, &mut buf);
            let Some(chunk) = buf.get(..n) else { break };
            b.update(chunk, &mut out).map_err(tree_err)?;
            off += n as u64;
        }
        let root = b.finish(&mut out).map_err(tree_err)?;
        self.0.borrow_mut().served.insert(
            root,
            Served {
                content: content.clone(),
                outboard: out,
            },
        );
        Ok(root)
    }

    /// Whether `root` is fully verified here, with `len` bytes.
    pub fn complete(&self, root: &[u8; 32], len: u64) -> bool {
        self.0
            .borrow()
            .fetched
            .get(root)
            .is_some_and(|f| f.verified.contains_range(0..len))
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

    /// Forget a fetched value.
    pub fn forget(&self, root: &[u8; 32]) {
        self.0.borrow_mut().fetched.remove(root);
    }
}

impl ValueRead for VStore {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        self.0.borrow().served.get(root).map(|p| p.content.len())
    }

    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        self.0
            .borrow()
            .served
            .get(root)
            .map_or(0, |p| p.content.fill(offset, dst))
    }

    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let s = self.0.borrow();
        let Some(p) = s.served.get(root) else { return 0 };
        let off = usize::try_from(offset).unwrap_or(usize::MAX);
        let Some(src) = p.outboard.get(off..) else { return 0 };
        let n = dst.len().min(src.len());
        if let (Some(d), Some(s)) = (dst.get_mut(..n), src.get(..n)) {
            d.copy_from_slice(s);
        }
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
        let off = usize::try_from(offset).map_err(|_| StoreError::Full)?;
        let end = off.checked_add(data.len()).ok_or(StoreError::Full)?;
        if f.data.len() < end {
            f.data.resize(end, 0);
        }
        f.data.get_mut(off..end).ok_or(StoreError::Full)?.copy_from_slice(data);
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
pub struct RcIndex(Rc<MemIndex>);

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

/// The sets of a node, by name.
#[derive(Clone, Default)]
pub struct SetStore {
    sets: BTreeMap<Vec<u8>, Rc<MemIndex>>,
}

impl SetStore {
    /// Hold `items` (any order) under `name`.
    ///
    /// # Errors
    /// The index could not be built.
    pub fn insert(&mut self, name: &[u8], mut items: Vec<[u8; 32]>) -> Result<(), String> {
        items.sort_unstable();
        items.dedup();
        let ix = MemIndex::from_sorted(items.iter().map(<[u8; 32]>::as_slice))
            .map_err(|_| "the set could not be indexed".to_owned())?;
        self.sets.insert(name.to_vec(), Rc::new(ix));
        Ok(())
    }
}

impl SetsApp for SetStore {
    type Index<'a> = RcIndex;
    fn limits(&self) -> Limits {
        Limits::default()
    }
    fn index(&self, set_ref: &[u8]) -> Option<RcIndex> {
        self.sets.get(set_ref).map(|i| RcIndex(Rc::clone(i)))
    }
}

/// The three stores a node runs with: values, sets, and bundles (off unless the scenario turns it on).
#[derive(Default)]
pub struct VApps {
    /// The values.
    pub values: VStore,
    /// The sets.
    pub sets: SetStore,
    /// The bundles.
    pub dtn: DtnStore,
}

impl Apps<Software> for VApps {
    type Values = VStore;
    type Sets = SetStore;
    type Dtn = DtnStore;

    fn enabled(&self) -> Enabled {
        Enabled {
            values: true,
            sets: true,
            dtn: self.dtn.is_on(),
        }
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
