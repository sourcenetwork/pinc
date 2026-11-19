//! The ledger of a run: provenance terms of secrets, the side tables the verdicts read, and the subscription to the
//! key derivations.
//!
//! Invariants: a term only refers to terms registered before it, so a single pass in id order evaluates what any
//! adversary knows; a secret is identified by its bytes and the first registration of a byte string wins (equal
//! bytes are equal values, so two derivations of one value agree); lookups use hash maps but no output depends on
//! their iteration order.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{BuildHasherDefault, Hasher};

use pinc_crypto::trace::{Derivation, Sink, set_sink};

use super::costs::{Work, WorkSlot};
use super::payload::MsgMeta;
use super::verdict::{Compromise, NonceReuse, PlaintextSeen};

/// The index of a [`Term`] in the ledger.
pub type TermId = u32;

/// Where a secret came from, as the reference harness's term algebra names it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    /// A fresh secret nothing else was derived into (a randomness seed).
    Rand(u64),
    /// An X25519 private key.
    XSk(u64),
    /// An ML-KEM-768 decapsulation key (its seed).
    KemSk(u64),
    /// The X25519 shared secret of two private keys (sorted by id).
    Dh(TermId, TermId),
    /// A shared secret with a public key nobody in the run owns: the adversary chose it.
    DhAdv,
    /// The shared secret of the encapsulation `ct` to the key of decapsulation key `owner`.
    KemSs {
        /// The ciphertext's ledger number.
        ct: u64,
        /// The decapsulation key that can open it.
        owner: TermId,
    },
    /// An encapsulation to a key nobody in the run owns: the adversary holds the secret.
    KemAdv,
    /// The implicit-rejection secret of decapsulating a ciphertext that was not made for the key.
    KemRej(TermId, u64),
    /// A key derived from the secret `inputs` (public inputs are not listed), under `label`.
    Hkdf {
        /// The secret terms it was derived from, sorted and unique.
        inputs: Vec<TermId>,
        /// The derivation label (`extract` for a chain step).
        label: Box<str>,
    },
    /// A secret whose derivation the ledger did not see: its provenance is unknown.
    Unknown(u64),
}

/// A key that protected application payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayloadKey {
    /// The key's term.
    pub term: TermId,
    /// Virtual time of the first payload it sealed.
    pub first_ns: u64,
    /// The node that sealed it.
    pub node: usize,
}

/// A hasher for keys that are already uniform random 64-bit values.
#[derive(Default)]
pub(super) struct Passthrough(u64);

impl Hasher for Passthrough {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0 << 8) | u64::from(*b);
        }
    }
    fn write_u64(&mut self, n: u64) {
        self.0 = n;
    }
}

pub(super) type FastMap<K, V> = HashMap<K, V, BuildHasherDefault<Passthrough>>;

/// Everything the ledger knows.
#[derive(Default)]
pub(super) struct State {
    pub(super) msgs: Vec<MsgMeta>,
    pub(super) terms: Vec<Term>,
    secrets: HashMap<Box<[u8]>, TermId>,
    lens: BTreeSet<usize>,
    pub(super) pk_owner: HashMap<[u8; 32], TermId>,
    pub(super) ek_owner: HashMap<[u8; 32], TermId>,
    pub(super) ct_reg: HashMap<[u8; 32], ([u8; 32], TermId)>,
    pub(super) uid: u64,
    // vertexia: one fingerprint per seal; ceiling is memory linear in packets sealed (16 B each), upgrade path is a
    // per-key high-water mark while packet numbers stay monotone.
    pub(super) nonce_use: FastMap<u64, u64>,
    pub(super) nonce_reuse: Vec<NonceReuse>,
    // vertexia: one entry per seal (12 B), the same ceiling and upgrade path as `nonce_use`.
    pub(super) tags: FastMap<u64, u32>,
    /// One bit per 24-bit tag prefix: a datagram scan skips the map lookup at almost every offset.
    pub(super) tag_bits: Vec<u64>,
    pub(super) payload_keys: BTreeMap<TermId, PayloadKey>,
    pub(super) key_seals: FastMap<u64, u64>,
    pub(super) compromises: Vec<Compromise>,
    pub(super) plaintext: Option<PlaintextSeen>,
    pub(super) work: Vec<WorkSlot>,
}

/// The number of bits of the tag prefix filter.
pub(super) const TAG_FILTER_BITS: u32 = 20;

impl State {
    pub(super) fn note_tag(&mut self, key: u64, maker: u32) {
        if self.tag_bits.is_empty() {
            self.tag_bits = vec![0; 1 << (TAG_FILTER_BITS - 6)];
        }
        let bit = key & ((1 << TAG_FILTER_BITS) - 1);
        self.tag_bits[(bit >> 6) as usize] |= 1 << (bit & 63);
        self.tags.insert(key, maker);
    }

    /// The node that made the tag whose first eight bytes are `key`, if any.
    pub(super) fn tag_maker(&self, key: u64) -> Option<u32> {
        let bit = key & ((1 << TAG_FILTER_BITS) - 1);
        if self
            .tag_bits
            .get((bit >> 6) as usize)
            .is_none_or(|w| w & (1 << (bit & 63)) == 0)
        {
            return None;
        }
        self.tags.get(&key).copied()
    }

    pub(super) fn fresh(&mut self) -> u64 {
        self.uid += 1;
        self.uid
    }

    pub(super) fn push(&mut self, term: Term) -> TermId {
        self.terms.push(term);
        (self.terms.len() - 1) as TermId
    }

    pub(super) fn lookup(&self, bytes: &[u8]) -> Option<TermId> {
        self.secrets.get(bytes).copied()
    }

    /// Register `bytes` as the value of `term` unless it is already registered; return the term that holds it.
    pub(super) fn bind(&mut self, bytes: &[u8], term: Term) -> TermId {
        if let Some(t) = self.lookup(bytes) {
            return t;
        }
        let id = self.push(term);
        self.secrets.insert(bytes.into(), id);
        self.lens.insert(bytes.len());
        id
    }

    /// Register `bytes` as another value of the existing term `id` unless it is already registered.
    pub(super) fn alias(&mut self, bytes: &[u8], id: TermId) {
        if self.lookup(bytes).is_none() {
            self.secrets.insert(bytes.into(), id);
            self.lens.insert(bytes.len());
        }
    }

    /// The registered secrets of length `len` that occur in `data` at any offset.
    pub(super) fn windows(&self, data: &[u8], len: usize, out: &mut BTreeSet<TermId>) {
        if len == 0 || data.len() < len {
            return;
        }
        out.extend(data.windows(len).filter_map(|w| self.secrets.get(w).copied()));
    }

    /// The registered secrets of every registered length that occur in `data`.
    pub(super) fn scan_all(&self, data: &[u8]) -> BTreeSet<TermId> {
        let mut out = BTreeSet::new();
        for &len in &self.lens {
            self.windows(data, len, &mut out);
        }
        out
    }

    /// Register the output of a derivation from `inputs`; no input means the derivation is not understood.
    pub(super) fn bind_derived(&mut self, out: &[u8], inputs: BTreeSet<TermId>, label: &str) -> TermId {
        if let Some(t) = self.lookup(out) {
            return t;
        }
        let term = if inputs.is_empty() {
            Term::Unknown(self.fresh())
        } else {
            Term::Hkdf {
                inputs: inputs.into_iter().collect(),
                label: label.into(),
            }
        };
        self.bind(out, term)
    }

    pub(super) fn work_mut(&mut self, node: usize) -> &mut Work {
        if self.work.len() <= node {
            self.work.resize_with(node + 1, WorkSlot::default);
        }
        &mut self.work[node].work
    }
}

/// The ledger of one run; see the module docs of [`crate::suite::crypto`].
pub struct Registry {
    pub(super) seed: u64,
    /// Virtual time in nanoseconds, set by the runner before it drives a node; the ledger stamps first uses with it.
    pub now: Cell<u64>,
    current: Cell<usize>,
    pub(super) st: RefCell<State>,
}

impl Registry {
    /// An empty ledger whose generated payload depends on `seed`.
    pub fn new(seed: u64) -> Self {
        Self {
            seed,
            now: Cell::new(0),
            current: Cell::new(0),
            st: RefCell::new(State::default()),
        }
    }

    /// An empty ledger that lives for the rest of the process, as a [`super::Tracked`] provider needs.
    pub fn leak(seed: u64) -> &'static Self {
        Box::leak(Box::new(Self::new(seed)))
    }

    /// Free everything the ledger recorded. The ledger itself lives on (a [`super::Tracked`] provider borrows it for
    /// good), so a run that is over empties it instead of leaking what it learned.
    pub fn clear(&self) {
        self.st.take();
        self.now.set(0);
        self.current.set(0);
    }

    /// Subscribe this ledger to the key derivations made on the current thread. Call it once per thread before any
    /// node runs; a derivation is attributed to the node last entered with [`Registry::enter`].
    pub fn install(&'static self) {
        set_sink(Some(self));
    }

    /// Stop observing derivations on the current thread.
    pub fn uninstall() {
        set_sink(None);
    }

    /// Say which node the following derivations belong to (the runner calls it before each endpoint call; every
    /// [`super::Tracked`] primitive sets it too).
    pub fn enter(&self, node: usize) {
        self.current.set(node);
    }

    /// The term of a secret, or `None` if no primitive or derivation produced it.
    pub fn term_of(&self, secret: &[u8]) -> Option<TermId> {
        self.st.borrow().lookup(secret)
    }

    /// The term with this id.
    pub fn term(&self, id: TermId) -> Option<Term> {
        self.st.borrow().terms.get(id as usize).cloned()
    }

    /// Whether a term depends on a secret whose derivation was not observed.
    pub fn is_unknown(&self, id: TermId) -> bool {
        self.unknown_flags().get(id as usize).copied().unwrap_or(false)
    }

    /// The keys that sealed payload so far, in term order.
    pub fn payload_keys(&self) -> Vec<PayloadKey> {
        self.st.borrow().payload_keys.values().cloned().collect()
    }

    /// Per term: does it depend on a secret of unknown provenance? One pass, inputs come before outputs.
    pub(super) fn unknown_flags(&self) -> Vec<bool> {
        let st = self.st.borrow();
        let mut flags = vec![false; st.terms.len()];
        for (i, t) in st.terms.iter().enumerate() {
            flags[i] = match t {
                Term::Unknown(_) => true,
                Term::Hkdf { inputs, .. } => inputs.iter().any(|&j| flags[j as usize]),
                _ => false,
            };
        }
        flags
    }

    /// Charge a signature over `msg_len` bytes to `node` (signing goes through the keystore, not the provider).
    pub fn note_sign(&self, node: usize, msg_len: usize) {
        let mut st = self.st.borrow_mut();
        let w = st.work_mut(node);
        w.sign += 1;
        w.hash_bytes += msg_len as u64;
    }

    /// Charge a signature verification over `msg_len` bytes to `node`.
    pub fn note_verify(&self, node: usize, msg_len: usize) {
        let mut st = self.st.borrow_mut();
        let w = st.work_mut(node);
        w.verify += 1;
        w.hash_bytes += msg_len as u64;
    }
}

impl Sink for Registry {
    fn derived(&self, d: &Derivation<'_>) {
        let node = self.current.get();
        let mut st = self.st.borrow_mut();
        let mut inputs = BTreeSet::new();
        match d {
            Derivation::Extract { salt, ikm, out } => {
                if let Some(t) = st.lookup(&salt[..]) {
                    inputs.insert(t);
                }
                st.windows(ikm, 32, &mut inputs);
                st.bind_derived(&out[..], inputs, "extract");
                let w = st.work_mut(node);
                w.mac += 1;
                w.hash_bytes += ikm.len() as u64;
            }
            Derivation::Expand { prk, label, ctx, out } => {
                // An expansion of a key the ledger never saw is unknown, whatever its context holds.
                if let Some(t) = st.lookup(&prk[..]) {
                    inputs.insert(t);
                    st.windows(ctx, 32, &mut inputs);
                }
                st.bind_derived(out, inputs, label);
                st.work_mut(node).hkdf += 1;
            }
        }
    }
}
