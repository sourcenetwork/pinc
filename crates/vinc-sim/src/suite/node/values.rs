//! The values of a run and the stores that serve and fetch them.
//!
//! A world value is a body of the registry's self-identifying payload, so a plaintext copy on the wire is seen by the
//! security verdict. [`Value`] holds what a provider serves: the body, generated on demand from the registry, and its
//! BLAKE3 tree. A value is hashed whole unless every fetch of it asks for ranges and it is large, in which case the
//! tree is sparse: only the groups some fetch can ask for are hashed, and every other subtree has a keyed
//! placeholder chaining value, so a terabyte value costs a few thousand compressions instead of a terabyte of
//! hashing. A fetch authenticates the groups it asks for against the root exactly as it would against a whole tree;
//! a group outside the planned ranges would fail verification, which is loud, never a pass.
//!
//! [`VStore`] is the value store of one node: what it serves, and the verified ranges of what it fetched. Fetched
//! bytes are checked against the expected body and then dropped (nothing reads them back), so a node holds no value
//! bytes.
//!
//! Invariants: the verified set only grows; every commit is recorded once for the recorder; a sparse tree and a
//! whole tree over the same touched groups give the same pairs; the store keeps no bytes of a value.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::ops::Range;
use std::rc::Rc;

use blake3::hazmat::{HasherExt, Mode, merge_subtrees_non_root, merge_subtrees_root};
use vinc_dag::ranges::VerifiedRanges;
use vinc_dag::tree::{Cv, OutboardBuilder, PARENT_LEN};
use vinc_values::store::{StoreError, ValueRead, ValueStore, verified_after};

use super::SetupError;
use crate::suite::crypto::{MsgId, PayloadKind, Registry};
use crate::suite::proto::ValueIds;
use crate::suite::world::model::{IntentKind, World};

/// The group size log of every tree: 16 KiB groups.
const GROUP_LOG: u32 = 4;
/// The bytes of one group.
const GROUP: u64 = 1024 << GROUP_LOG;
/// A value at most this long is always hashed whole.
const WHOLE_LIMIT: u64 = 256 << 20;
/// The most groups a sparse tree touches.
const TOUCHED_LIMIT: u64 = 1 << 16;
/// The bytes generated and hashed per step of a whole tree.
const STEP: usize = 1 << 20;
/// The intervals of verified bytes a store keeps per value.
const INTERVALS: usize = 64;

/// The tree of a value.
enum Tree {
    /// Every group hashed; the outboard in memory.
    Whole(Vec<u8>),
    /// Only `touched` groups hashed.
    Sparse(Sparse),
}

/// The sparse tree: placeholders everywhere but over the touched groups.
struct Sparse {
    groups: u64,
    /// Sorted group indices that hold real bytes.
    touched: Vec<u64>,
    key: [u8; 32],
    memo: RefCell<BTreeMap<(u64, u64), Cv>>,
}

/// One value of the world, as a provider serves it.
pub struct Value {
    /// The registry id of the body.
    pub id: MsgId,
    /// The length in bytes.
    pub len: u64,
    /// The root of its tree.
    pub root: Cv,
    reg: &'static Registry,
    tree: Tree,
}

/// The largest power of two strictly below `m` (at least 2).
fn split_of(m: u64) -> u64 {
    1 << (m - 1).ilog2()
}

impl Sparse {
    fn has_touched(&self, lo: u64, hi: u64) -> bool {
        self.touched.partition_point(|g| *g < lo) < self.touched.partition_point(|g| *g < hi)
    }

    fn placeholder(&self, lo: u64, hi: u64) -> Cv {
        let mut b = [0u8; 16];
        b[..8].copy_from_slice(&lo.to_le_bytes());
        b[8..].copy_from_slice(&hi.to_le_bytes());
        *blake3::keyed_hash(&self.key, &b).as_bytes()
    }

    /// The chaining value of the subtree over groups `lo..hi`, which is not the whole tree.
    fn cv(&self, v: &Value, lo: u64, hi: u64) -> Cv {
        if !self.has_touched(lo, hi) {
            return self.placeholder(lo, hi);
        }
        if let Some(c) = self.memo.borrow().get(&(lo, hi)) {
            return *c;
        }
        let c = if hi - lo == 1 {
            v.group_cv(lo)
        } else {
            let mid = lo + split_of(hi - lo);
            merge_subtrees_non_root(&self.cv(v, lo, mid), &self.cv(v, mid, hi), Mode::Hash)
        };
        self.memo.borrow_mut().insert((lo, hi), c);
        c
    }
}

/// The node `p` places after the root in pre-order, as the group interval it spans, in a tree of `n >= 2` groups.
fn node_at(n: u64, mut p: u64) -> (u64, u64) {
    let (mut lo, mut hi) = (0, n);
    while p > 0 {
        p -= 1;
        let split = split_of(hi - lo);
        if p < split - 1 {
            hi = lo + split;
        } else {
            p -= split - 1;
            lo += split;
        }
    }
    (lo, hi)
}

impl Value {
    fn groups(len: u64) -> u64 {
        len.div_ceil(GROUP)
    }

    /// A value hashed whole.
    fn whole(reg: &'static Registry, id: MsgId, len: u64) -> Result<Self, SetupError> {
        let mut b = OutboardBuilder::new(len, GROUP_LOG).map_err(|_| SetupError::Value)?;
        let size = usize::try_from(b.layout().outboard_size()).map_err(|_| SetupError::Value)?;
        let mut out = vec![0u8; size];
        let mut buf = vec![0u8; STEP];
        let mut off = 0u64;
        while off < len {
            let n = usize::try_from(len - off).map_or(STEP, |r| r.min(STEP));
            let chunk = buf.get_mut(..n).ok_or(SetupError::Value)?;
            reg.fill(id, off, chunk).map_err(|_| SetupError::Value)?;
            b.update(chunk, &mut out).map_err(|_| SetupError::Value)?;
            off += n as u64;
        }
        let root = b.finish(&mut out).map_err(|_| SetupError::Value)?;
        Ok(Self {
            id,
            len,
            root,
            reg,
            tree: Tree::Whole(out),
        })
    }

    /// A value hashed over `touched` groups only (sorted, with the first and last group among them).
    fn sparse(reg: &'static Registry, id: MsgId, len: u64, touched: Vec<u64>) -> Result<Self, SetupError> {
        let groups = Self::groups(len);
        let mut head = [0u8; 64];
        reg.fill(id, 0, &mut head).map_err(|_| SetupError::Value)?;
        let key = *blake3::hash(&head).as_bytes();
        let mut v = Self {
            id,
            len,
            root: [0; 32],
            reg,
            tree: Tree::Sparse(Sparse {
                groups,
                touched,
                key,
                memo: RefCell::default(),
            }),
        };
        let Tree::Sparse(s) = &v.tree else {
            return Err(SetupError::Value);
        };
        let mid = split_of(groups);
        v.root = *merge_subtrees_root(&s.cv(&v, 0, mid), &s.cv(&v, mid, groups), Mode::Hash).as_bytes();
        Ok(v)
    }

    /// The chaining value of group `g`, hashed from its body (the tree has more than one group).
    fn group_cv(&self, g: u64) -> Cv {
        let start = g * GROUP;
        let n = usize::try_from(self.len.saturating_sub(start).min(GROUP)).unwrap_or(0);
        let mut buf = vec![0u8; n];
        // The range is inside the body by construction; a refusal leaves zeros, which the fetch would reject.
        let _ = self.reg.fill(self.id, start, &mut buf);
        let mut h = blake3::Hasher::new();
        h.set_input_offset(start);
        h.update(&buf);
        h.finalize_non_root()
    }

    /// Copy body bytes at `off` into `dst`; returns how many.
    pub fn read_at(&self, off: u64, dst: &mut [u8]) -> usize {
        let n = usize::try_from(self.len.saturating_sub(off)).map_or(dst.len(), |r| r.min(dst.len()));
        let Some(d) = dst.get_mut(..n) else { return 0 };
        if self.reg.fill(self.id, off, d).is_ok() { n } else { 0 }
    }

    /// Copy outboard bytes at `off` into `dst`; returns how many.
    pub fn read_outboard(&self, off: u64, dst: &mut [u8]) -> usize {
        match &self.tree {
            Tree::Whole(out) => {
                let start = usize::try_from(off).unwrap_or(usize::MAX).min(out.len());
                let n = (out.len() - start).min(dst.len());
                if let (Some(d), Some(s)) = (dst.get_mut(..n), out.get(start..start + n)) {
                    d.copy_from_slice(s);
                }
                n
            }
            Tree::Sparse(s) => {
                let total = (s.groups - 1) * PARENT_LEN as u64;
                let end = off.saturating_add(dst.len() as u64).min(total);
                let mut pos = off;
                while pos < end {
                    let (lo, hi) = node_at(s.groups, pos / PARENT_LEN as u64);
                    let mid = lo + split_of(hi - lo);
                    let mut pair = [0u8; PARENT_LEN];
                    pair[..32].copy_from_slice(&s.cv(self, lo, mid));
                    pair[32..].copy_from_slice(&s.cv(self, mid, hi));
                    let within = (pos % PARENT_LEN as u64) as usize;
                    let take = (PARENT_LEN - within).min(usize::try_from(end - pos).unwrap_or(PARENT_LEN));
                    let at = (pos - off) as usize;
                    if let (Some(d), Some(p)) = (dst.get_mut(at..at + take), pair.get(within..within + take)) {
                        d.copy_from_slice(p);
                    }
                    pos += take as u64;
                }
                usize::try_from(end.saturating_sub(off)).unwrap_or(0)
            }
        }
    }
}

/// The values of a world: their ids by name and the built values by id.
pub struct Catalog {
    /// The world's value names and the ids of their bodies.
    pub ids: Rc<ValueIds>,
    values: BTreeMap<u64, Rc<Value>>,
}

/// The groups the fetches of `name` can touch, or `None` when some fetch asks for the whole value.
fn touched_groups(world: &World, name: &str, len: u64) -> Option<Vec<u64>> {
    let groups = Value::groups(len);
    let mut set = std::collections::BTreeSet::from([0, groups.saturating_sub(1)]);
    for it in world
        .intents
        .iter()
        .filter(|i| i.kind == IntentKind::Fetch && i.value.as_deref() == Some(name))
    {
        if it.ranges.is_empty() {
            return None;
        }
        for &(off, n) in &it.ranges {
            if n == 0 {
                continue;
            }
            let (a, b) = (off / GROUP, (off + n - 1) / GROUP);
            if b - a + 1 > TOUCHED_LIMIT {
                return None;
            }
            set.extend(a..=b.min(groups.saturating_sub(1)));
        }
    }
    (set.len() as u64 <= TOUCHED_LIMIT).then(|| set.into_iter().collect())
}

impl Catalog {
    /// The values of `world` in sorted name order, created by their first provider.
    ///
    /// # Errors
    /// [`SetupError::Value`] if a tree cannot be built.
    pub fn build(world: &World, reg: &'static Registry) -> Result<Self, SetupError> {
        let mut ids = ValueIds::new();
        let mut values = BTreeMap::new();
        for (name, &len) in &world.values {
            let creator = world
                .provides
                .iter()
                .find(|(_, names)| names.contains(name))
                .map_or(0, |(n, _)| *n);
            let id = reg.new_msg(creator, PayloadKind::Value, len);
            let v = match touched_groups(world, name, len).filter(|_| len > WHOLE_LIMIT && Value::groups(len) > 1) {
                Some(t) => Value::sparse(reg, id, len, t)?,
                None => Value::whole(reg, id, len)?,
            };
            ids.insert(name.clone(), id);
            values.insert(id.0, Rc::new(v));
        }
        Ok(Self {
            ids: Rc::new(ids),
            values,
        })
    }

    /// The value with body `id`.
    pub fn get(&self, id: MsgId) -> Option<&Rc<Value>> {
        self.values.get(&id.0)
    }

    /// Every value.
    pub fn all(&self) -> impl Iterator<Item = &Rc<Value>> {
        self.values.values()
    }
}

/// A write to a store the recorder wants to know about.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Commit {
    /// The value.
    pub id: MsgId,
    /// The first byte.
    pub off: u64,
    /// The number of bytes.
    pub len: u64,
    /// Of those, the bytes not verified before.
    pub new: u64,
}

#[derive(Default)]
struct VState {
    /// The values this node serves, by root.
    served: BTreeMap<Cv, Rc<Value>>,
    /// Every value of the world, by root: what a fetched byte is checked against.
    known: BTreeMap<Cv, Rc<Value>>,
    fetched: BTreeMap<Cv, VerifiedRanges<INTERVALS>>,
    commits: Vec<Commit>,
    bad: u64,
}

/// The value store of one node: cheap to clone, one state behind it.
#[derive(Clone, Default)]
pub struct VStore(Rc<RefCell<VState>>);

impl VStore {
    /// A store that knows `catalog` and serves the values named `provides`.
    pub fn new(catalog: &Catalog, provides: &[String]) -> Self {
        let mut st = VState::default();
        for v in catalog.all() {
            st.known.insert(v.root, Rc::clone(v));
        }
        for name in provides {
            if let Some(v) = catalog.ids.get(name).and_then(|id| catalog.get(*id)) {
                st.served.insert(v.root, Rc::clone(v));
            }
        }
        Self(Rc::new(RefCell::new(st)))
    }

    /// The roots this store serves.
    pub fn served_roots(&self) -> Vec<Cv> {
        self.0.borrow().served.keys().copied().collect()
    }

    /// Forget everything fetched (a restart that keeps no state).
    pub fn forget(&self) {
        self.0.borrow_mut().fetched.clear();
    }

    /// Whether bytes `off..off + len` of `id` are verified in this store.
    pub fn holds(&self, root: &Cv, off: u64, len: u64) -> bool {
        self.0
            .borrow()
            .fetched
            .get(root)
            .is_some_and(|r| r.contains_range(off..off.saturating_add(len)))
    }

    /// The bytes verified in one run from `off` of `root`.
    pub fn contiguous_from(&self, root: &Cv, off: u64) -> u64 {
        self.0
            .borrow()
            .fetched
            .get(root)
            .and_then(|r| verified_after(r, off))
            .filter(|r| r.start <= off)
            .map_or(0, |r| r.end - off)
    }

    /// The commits since the last call.
    pub fn take_commits(&self) -> Vec<Commit> {
        std::mem::take(&mut self.0.borrow_mut().commits)
    }

    /// How many writes carried bytes that are not the value's body.
    pub fn bad_writes(&self) -> u64 {
        self.0.borrow().bad
    }
}

impl ValueRead for VStore {
    fn servable_len(&self, root: &[u8; 32]) -> Option<u64> {
        self.0.borrow().served.get(root).map(|v| v.len)
    }

    fn read_at(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let v = self.0.borrow().served.get(root).cloned();
        v.map_or(0, |v| v.read_at(offset, dst))
    }

    fn read_outboard(&self, root: &[u8; 32], offset: u64, dst: &mut [u8]) -> usize {
        let v = self.0.borrow().served.get(root).cloned();
        v.map_or(0, |v| v.read_outboard(offset, dst))
    }
}

impl ValueStore for VStore {
    fn verified_from(&self, root: &[u8; 32], from: u64) -> Option<Range<u64>> {
        self.0.borrow().fetched.get(root).and_then(|r| verified_after(r, from))
    }

    fn write_at(&mut self, root: &[u8; 32], offset: u64, data: &[u8]) -> Result<(), StoreError> {
        let known = self.0.borrow().known.get(root).cloned();
        let mut same = false;
        if let Some(v) = known {
            let mut expect = vec![0u8; data.len()];
            same = v.read_at(offset, &mut expect) == data.len() && expect == data;
        }
        if !same {
            self.0.borrow_mut().bad += 1;
        }
        Ok(())
    }

    fn commit(&mut self, root: &[u8; 32], range: Range<u64>) -> Result<(), StoreError> {
        let mut st = self.0.borrow_mut();
        let id = st.known.get(root).map(|v| v.id);
        let set = st.fetched.entry(*root).or_default();
        let before = set.covered_len();
        set.insert(range.clone())?;
        let new = set.covered_len() - before;
        if let Some(id) = id {
            st.commits.push(Commit {
                id,
                off: range.start,
                len: range.end - range.start,
                new,
            });
        }
        Ok(())
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::many_single_char_names)]
mod tests {
    use super::*;

    fn reg() -> &'static Registry {
        Registry::leak(7)
    }

    /// A sparse tree over every group is the whole tree: same root, same pairs.
    #[test]
    fn a_sparse_tree_over_every_group_is_the_whole_tree() {
        let r = reg();
        for len in [GROUP * 2, GROUP * 5 + 17, GROUP * 8, GROUP * 13 - 1] {
            let id = r.new_msg(0, PayloadKind::Value, len);
            let whole = Value::whole(r, id, len).unwrap();
            let all: Vec<u64> = (0..Value::groups(len)).collect();
            let sparse = Value::sparse(r, id, len, all).unwrap();
            assert_eq!(whole.root, sparse.root, "len {len}");
            let size = (Value::groups(len) - 1) * PARENT_LEN as u64;
            let (mut a, mut b) = (vec![0u8; size as usize], vec![0u8; size as usize]);
            assert_eq!(whole.read_outboard(0, &mut a), a.len());
            assert_eq!(sparse.read_outboard(0, &mut b), b.len());
            assert_eq!(a, b, "len {len}");
            // an unaligned window reads the same bytes, or what is left of the outboard when it is shorter
            let (mut c, mut d) = ([0u8; 100], [0u8; 100]);
            let want = 100.min(a.len().saturating_sub(70));
            assert_eq!(whole.read_outboard(70, &mut c), want, "len {len}");
            assert_eq!(sparse.read_outboard(70, &mut d), want, "len {len}");
            assert_eq!(c, d, "len {len}");
        }
    }

    /// A range of a sparse value is proved by its tree and verifies against its root, at both ends of the value.
    #[test]
    fn a_range_of_a_sparse_value_verifies_against_its_root() {
        use vinc_dag::tree::{Layout, RangeEncoder, RangeVerifier, Step};
        let r = reg();
        let len = GROUP * 300 + 77;
        let id = r.new_msg(0, PayloadKind::Value, len);
        let touched = [0, 150, 151, 152, 299, 300].to_vec();
        let v = Value::sparse(r, id, len, touched).unwrap();
        let layout = Layout::new(len, GROUP_LOG).unwrap();
        for range in [150 * GROUP + 5..152 * GROUP + 100, 0..10, len - 50..len] {
            let mut stream = Vec::new();
            for step in RangeEncoder::new(layout, &range).unwrap() {
                match step.unwrap() {
                    Step::Parent { outboard_offset } => {
                        let mut b = [0u8; PARENT_LEN];
                        assert_eq!(v.read_outboard(outboard_offset, &mut b), PARENT_LEN);
                        stream.extend_from_slice(&b);
                    }
                    Step::Group { offset, len } => {
                        let mut b = vec![0u8; len as usize];
                        assert_eq!(v.read_at(offset, &mut b), b.len());
                        stream.extend_from_slice(&b);
                    }
                }
            }
            let mut ver = RangeVerifier::<16384>::new(v.root, len, &range).unwrap();
            let mut rest = stream.as_slice();
            let mut got = 0u64;
            while !rest.is_empty() {
                let fed = ver.feed(rest).unwrap();
                got += fed.verified.map_or(0, |g| g.data.len() as u64);
                rest = &rest[fed.consumed..];
            }
            assert!(ver.is_complete());
            assert!(got >= range.end - range.start);
        }
    }

    /// The store keeps ranges, counts new bytes once and forgets on request.
    #[test]
    fn the_store_counts_new_bytes_once() {
        let cat = Catalog {
            ids: Rc::default(),
            values: BTreeMap::new(),
        };
        let mut s = VStore::new(&cat, &[]);
        let root = [9u8; 32];
        s.commit(&root, 0..100).unwrap();
        s.commit(&root, 50..150).unwrap();
        assert!(s.holds(&root, 0, 150));
        assert_eq!(s.contiguous_from(&root, 10), 140);
        assert_eq!(s.verified_from(&root, 150), None);
        s.forget();
        assert!(!s.holds(&root, 0, 1));
    }
}
