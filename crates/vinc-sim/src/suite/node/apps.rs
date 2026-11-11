//! The host stores of a suite node's layers above broadcast: the value store, the sets to reconcile, and no bundle
//! store (the suite carries no delay-tolerant workload).
//!
//! Invariants: the stores are shared with the layers of the application through clones that point at the same
//! state, so what the node fetched is what the application sees held; a set never changes during a run.

use std::collections::BTreeMap;
use std::rc::Rc;

use vinc_node::{Apps, Enabled, NoDtn, SetsApp};
use vinc_reconcile::{Fingerprint, ItemIndex, MemError, MemIndex};

use super::values::VStore;
use crate::suite::crypto::Tracked;
use crate::suite::world::model::World;

/// A set's index, shared by reference.
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

/// The sets of one node by name.
#[derive(Clone, Default)]
pub struct SetStore(BTreeMap<Vec<u8>, Rc<MemIndex>>);

impl SetStore {
    /// The sets node `idx` holds in `world`.
    ///
    /// # Errors
    /// [`MemError`] if a set of the world is not sorted.
    pub fn of(world: &World, idx: usize) -> Result<Self, MemError> {
        let mut sets = BTreeMap::new();
        for ((node, name), items) in &world.sets {
            if *node == idx {
                let ix = MemIndex::from_sorted(items.iter().map(<[u8; 40]>::as_slice))?;
                sets.insert(name.clone(), Rc::new(ix));
            }
        }
        Ok(Self(sets))
    }
}

impl SetsApp for SetStore {
    type Index<'a> = RcIndex;
    fn index(&self, set_ref: &[u8]) -> Option<RcIndex> {
        self.0.get(set_ref).map(|i| RcIndex(Rc::clone(i)))
    }
}

/// The `Apps` of a suite node: values and sets on, bundles off.
pub(super) struct SuiteApps {
    values: VStore,
    sets: SetStore,
    dtn: NoDtn,
}

impl SuiteApps {
    /// The apps over a node's stores.
    pub(super) fn new(values: VStore, sets: SetStore) -> Self {
        Self {
            values,
            sets,
            dtn: NoDtn,
        }
    }
}

impl Apps<Tracked> for SuiteApps {
    type Values = VStore;
    type Sets = SetStore;
    type Dtn = NoDtn;

    fn enabled(&self) -> Enabled {
        Enabled {
            values: true,
            sets: true,
            dtn: false,
        }
    }
    fn values(&mut self) -> &mut VStore {
        &mut self.values
    }
    fn sets(&self) -> &SetStore {
        &self.sets
    }
    fn dtn(&mut self) -> &mut NoDtn {
        &mut self.dtn
    }
}
