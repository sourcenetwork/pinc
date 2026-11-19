//! The records that let the delay-tolerant layer resume after a restart.
//!
//! The host keeps complete bundles in its store; the node adds one small record per bundle it looks after, through
//! [`DtnApp::save_record`](crate::DtnApp::save_record): a held bundle (its signed head, the copies this node still
//! holds, and whether custody is owed to a previous holder), a partial bundle (its head, then the runs of verified
//! symbols, each with its bytes) or the memory that a bundle was delivered here. [`Node::dtn_restore`] reads them
//! back after a restart and rebuilds the forwarder, the ledger and the custody book from them.
//!
//! A partial bundle's record is written once with its head and grows by
//! [`DtnApp::append_record`](crate::DtnApp::append_record): every [`SAVE_BYTES`] (256 KiB) of verified bytes, when
//! a transfer of it is refused and when its session ends, the runs verified since the last save are appended, so a reception writes each byte once
//! and a crash loses at most the symbols since then, which the holder sends again. A run carries no count, so a
//! record holds any number of them.
//!
//! Invariants: a record is written only for state the node holds; a record that cannot be read back whole is dropped,
//! never half applied, except that a partial record's torn last run (a crash during an append) is left out and the
//! runs before it kept; the ledger is charged for every restored bundle before it is held, so a restart never lets
//! the node hold more than its budget; the copies restored are those the node held when it last wrote the record, so
//! a copy handed on before a crash is not counted twice.

#![allow(
    clippy::many_single_char_names,
    reason = "d, p, c and r are the layer's state, a part, the cursor over a record and a run, as in the modules around"
)]

use alloc::collections::BTreeSet;
use alloc::vec::Vec;

use pinc_crypto::{IdentityAlg, NodeId as FullId};
use pinc_dtn::custody::Incoming;
use pinc_dtn::forward::{Held, Input};
use pinc_dtn::head::{BundleId, SignedHead};
use pinc_dtn::held::HeldSet;
use pinc_dtn::store::{Class, Key, Space};

use crate::apps::{Apps, DtnApp, ServeSource};
use crate::config::{Nanos, Store};
use crate::dtn::{Partial, no_symbols, partial_charge};
use crate::ep::Ep;
use crate::node::Node;

/// The version of the record format.
const VERSION: u8 = 2;
const HELD: u8 = 0;
const PARTIAL: u8 = 1;
const RECEIVED: u8 = 2;
/// Verified bytes of a partial bundle between two saves.
pub(crate) const SAVE_BYTES: u64 = 256 << 10;

/// What [`Node::dtn_restore`] found.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DtnRestored {
    /// Bundles held again, with their copies and custody.
    pub held: usize,
    /// Partial bundles resumed.
    pub partial: usize,
    /// Memories of bundles delivered here.
    pub received: usize,
    /// Records dropped: unreadable, expired, without their bundle in the store, or without room.
    pub dropped: usize,
}

/// A reader over a record.
struct Cur<'a>(&'a [u8]);

impl<'a> Cur<'a> {
    fn take(&mut self, n: usize) -> Option<&'a [u8]> {
        let (a, b) = (self.0.get(..n)?, self.0.get(n..)?);
        self.0 = b;
        Some(a)
    }

    fn u8(&mut self) -> Option<u8> {
        self.take(1)?.first().copied()
    }

    fn u16(&mut self) -> Option<u16> {
        self.take(2)?.try_into().ok().map(u16::from_be_bytes)
    }

    fn u64(&mut self) -> Option<u64> {
        self.take(8)?.try_into().ok().map(u64::from_be_bytes)
    }

    fn node(&mut self) -> Option<FullId> {
        let alg = IdentityAlg::from_tag(self.u8()?)?;
        let bytes: [u8; 32] = self.take(32)?.try_into().ok()?;
        Some(FullId { alg, bytes })
    }
}

fn put_node(out: &mut Vec<u8>, n: &FullId) {
    out.push(n.alg.tag());
    out.extend_from_slice(&n.bytes);
}

fn put_head(out: &mut Vec<u8>, signed: &SignedHead) -> bool {
    let Ok(len) = u16::try_from(signed.encoded_len()) else {
        return false;
    };
    out.extend_from_slice(&len.to_be_bytes());
    let at = out.len();
    out.resize(at + usize::from(len), 0);
    out.get_mut(at..).is_some_and(|dst| signed.encode(dst).is_ok())
}

fn take_head(c: &mut Cur<'_>) -> Option<SignedHead> {
    let len = usize::from(c.u16()?);
    SignedHead::decode(c.take(len)?).ok().filter(|s| s.verify().is_ok())
}

/// A record as read back, before any check against the node's state.
#[allow(clippy::large_enum_variant, reason = "read once and consumed at once")]
pub(crate) enum Record<'a> {
    /// The memory that a bundle was delivered here, until `expires` (wall milliseconds).
    Received {
        /// When the memory ends.
        expires: u64,
    },
    /// A held bundle: the copies this node holds, the custody it owes and to whom, the bytes charged, its head.
    Held {
        /// The copies held.
        copies: u16,
        /// Whether custody is owed to a previous holder.
        custody: bool,
        /// The previous holder (this node when no custody is owed).
        prev: FullId,
        /// The bytes charged to the ledger.
        bytes: u64,
        /// The signed head.
        signed: SignedHead,
    },
    /// A partial bundle: its head and its runs, not yet read.
    Partial {
        /// The signed head.
        signed: SignedHead,
        /// The runs, as [`check_runs`] and [`take_runs`] read them.
        runs: &'a [u8],
    },
}

/// Read a record whole: `None` for another version or kind, a byte short or too many, a custody byte other than 0
/// or 1, an unknown algorithm, or a head that does not decode and verify. A partial record's runs are read by
/// [`check_runs`] and [`take_runs`].
pub(crate) fn read_record(rec: &[u8]) -> Option<Record<'_>> {
    let mut c = Cur(rec);
    if c.u8()? != VERSION {
        return None;
    }
    match c.u8()? {
        RECEIVED => {
            let expires = c.u64()?;
            c.0.is_empty().then_some(Record::Received { expires })
        }
        HELD => {
            let copies = c.u16()?;
            let custody = match c.u8()? {
                0 => false,
                1 => true,
                _ => return None,
            };
            let prev = c.node()?;
            let bytes = c.u64()?;
            let signed = take_head(&mut c)?;
            c.0.is_empty().then_some(Record::Held {
                copies,
                custody,
                prev,
                bytes,
                signed,
            })
        }
        PARTIAL => {
            let signed = take_head(&mut c)?;
            Some(Record::Partial { signed, runs: c.0 })
        }
        _ => None,
    }
}

/// The record of a bundle delivered here.
pub(crate) fn received_record(expires: u64) -> Vec<u8> {
    let mut rec = Vec::with_capacity(10);
    rec.extend_from_slice(&[VERSION, RECEIVED]);
    rec.extend_from_slice(&expires.to_be_bytes());
    rec
}

/// The record of a held bundle; `None` when its head does not fit the length field.
pub(crate) fn held_record(
    copies: u16,
    custody: bool,
    prev: &FullId,
    bytes: u64,
    signed: &SignedHead,
) -> Option<Vec<u8>> {
    let mut rec = Vec::with_capacity(signed.encoded_len() + 64);
    rec.extend_from_slice(&[VERSION, HELD]);
    rec.extend_from_slice(&copies.to_be_bytes());
    rec.push(u8::from(custody));
    put_node(&mut rec, prev);
    rec.extend_from_slice(&bytes.to_be_bytes());
    put_head(&mut rec, signed).then_some(rec)
}

/// The start of a partial bundle's record, with room for `cap` bytes; `None` when its head does not fit.
pub(crate) fn partial_head(signed: &SignedHead, cap: usize) -> Option<Vec<u8>> {
    let mut rec = Vec::with_capacity(cap);
    rec.extend_from_slice(&[VERSION, PARTIAL]);
    put_head(&mut rec, signed).then_some(rec)
}

/// Append the run `a..b` and its bytes.
pub(crate) fn put_run(out: &mut Vec<u8>, a: u64, b: u64, bytes: &[u8]) {
    out.extend_from_slice(&a.to_be_bytes());
    out.extend_from_slice(&b.to_be_bytes());
    out.extend_from_slice(bytes);
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: pinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: ServeSource<A::Values>,
{
    /// Write the record of a held bundle: its head, the copies this node holds and the custody it owes.
    pub(crate) fn dtn_save_held(&mut self, id: &BundleId) {
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        let (Some(signed), Some(copies)) = (d.heads.get(id), d.fwd.copies_held(id)) else {
            return;
        };
        let bytes = d.led.get(&id.store_key()).map_or(0, |e| e.bytes);
        let (custody, prev) = d.book.owed_to(id).map_or((false, self.ident), |p| (true, p));
        if let Some(rec) = held_record(copies, custody, &prev, bytes, signed) {
            self.apps.dtn().save_record(id, &rec);
        }
    }

    /// Write the memory that `id` was delivered here, until `expires`.
    pub(crate) fn dtn_save_received(&mut self, id: &BundleId, expires: u64) {
        self.apps.dtn().save_record(id, &received_record(expires));
    }

    /// Save the runs of a partial bundle verified since its last save: the first save writes the record with the
    /// head, every later one appends.
    pub(crate) fn dtn_save_partial(&mut self, id: &BundleId) {
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        let Some(p) = d.partials.get_mut(id).filter(|p| !p.unsaved.is_empty()) else {
            return;
        };
        let runs = p.unsaved.len() * 16;
        let cap = usize::try_from(p.unsaved_bytes).unwrap_or(0) + runs + 64;
        let mut rec = if p.recorded {
            Vec::with_capacity(cap)
        } else {
            let Some(r) = partial_head(&p.signed, cap) else {
                return;
            };
            r
        };
        for r in &p.unsaved {
            let (Ok(a), Ok(b)) = (usize::try_from(r.start), usize::try_from(r.end)) else {
                return;
            };
            let Some(bytes) = p.sealed.get(a..b) else { return };
            put_run(&mut rec, r.start, r.end, bytes);
        }
        p.unsaved.clear();
        p.unsaved_bytes = 0;
        if p.recorded {
            self.apps.dtn().append_record(id, &rec);
        } else {
            p.recorded = true;
            self.apps.dtn().save_record(id, &rec);
        }
    }

    /// Save every partial bundle that has grown since its last record.
    pub(crate) fn dtn_save_grown(&mut self) {
        let grown: Vec<BundleId> = self
            .dtn
            .as_deref()
            .map(|d| {
                d.partials
                    .iter()
                    .filter(|(_, p)| !p.unsaved.is_empty())
                    .map(|(id, _)| *id)
                    .collect()
            })
            .unwrap_or_default();
        for id in grown {
            self.dtn_save_partial(&id);
        }
    }

    /// Resume after a restart from the records the host kept: held bundles with their copies and custody, partial
    /// bundles with their verified symbols, and the memory of what was delivered here. Call it once, before any
    /// other input, with the host's store and records as they were. A record that cannot be applied is dropped and
    /// counted. The records to drop are dropped after the walk, so the host's order never shifts under it.
    pub fn dtn_restore(&mut self, now: Nanos) -> DtnRestored {
        self.begin(now);
        let mut out = DtnRestored::default();
        if self.dtn.is_none() {
            return out;
        }
        let mut n = 0;
        let mut unreadable = Vec::new();
        // Bundles evicted to make room: their records are not visited and are dropped with the others.
        let mut evicted = BTreeSet::new();
        while let Some((id, rec)) = self.apps.dtn().record_at(n).map(|(i, r)| (i, r.to_vec())) {
            n += 1;
            if evicted.contains(&id) {
                continue;
            }
            if self.restore_one(&id, &rec, &mut out, &mut evicted).is_none() {
                out.dropped += 1;
                unreadable.push(id);
            }
        }
        for id in unreadable.iter().chain(&evicted) {
            self.apps.dtn().drop_record(id);
        }
        self.dtn_contacts_changed();
        self.settle(now);
        out
    }

    /// Apply one record, only once the whole of it is known to be readable: nothing is admitted or evicted for a
    /// record that is then refused.
    fn restore_one(
        &mut self,
        id: &BundleId,
        rec: &[u8],
        out: &mut DtnRestored,
        gone: &mut BTreeSet<BundleId>,
    ) -> Option<()> {
        let wall = self.io.wall_ms();
        let record = read_record(rec)?;
        let d = self.dtn.as_deref_mut()?;
        match record {
            Record::Received { expires } => {
                if expires <= wall {
                    return None;
                }
                d.received.insert(*id, expires);
                out.received += 1;
            }
            Record::Held {
                copies,
                custody,
                prev,
                bytes,
                signed,
            } => {
                let h = *signed.head();
                if h.id != *id || h.is_expired(wall) || copies == 0 || self.apps.dtn().get(id).is_none() {
                    return None;
                }
                let expires = h.expires_at();
                let mut evicted: Vec<Key> = Vec::new();
                let kept = if custody {
                    d.book
                        .accept(
                            &mut d.led,
                            Incoming {
                                bundle: *id,
                                bytes,
                                expires,
                                previous: prev,
                                offer: 0,
                            },
                            wall,
                            |e| {
                                evicted.push(e.key);
                            },
                        )
                        .is_ok()
                } else {
                    d.led
                        .admit(id.store_key(), bytes, Class::Transit, expires, wall, |e| {
                            evicted.push(e.key);
                        })
                        .is_ok()
                };
                let app = self.apps.dtn();
                for k in evicted.iter().filter(|k| k.space == Space::DTN && k.id != id.0) {
                    let gone_id = BundleId(k.id);
                    d.forget_keeping_record(app, wall, &gone_id);
                    gone.insert(gone_id);
                }
                if !kept {
                    return None;
                }
                let hold = Held {
                    id: *id,
                    destination: h.destination,
                    expires,
                    copies,
                };
                if d.fwd.step(wall, Input::Hold(hold)).is_err() {
                    let _ = d.book.delivered(&mut d.led, id);
                    d.led.release(&id.store_key());
                    return None;
                }
                d.heads.insert(*id, signed);
                out.held += 1;
            }
            Record::Partial { signed, runs } => {
                let h = *signed.head();
                if h.id != *id || h.is_expired(wall) {
                    return None;
                }
                let layout = h.layout().ok()?;
                let total = layout.total_len();
                let sealed_len = usize::try_from(total).ok()?;
                let outboard_len = usize::try_from(layout.outboard_len().ok()?).ok()?;
                let charge = partial_charge(&layout)?;
                // The runs are checked whole before the charge can evict anything.
                check_runs(&mut Cur(runs), total, layout.slice_len())?;
                // Charged before any buffer of it exists, as on an offer.
                let mut evicted: Vec<Key> = Vec::new();
                let admitted = d
                    .led
                    .admit(id.store_key(), charge, Class::Transit, h.expires_at(), wall, |e| {
                        evicted.push(e.key);
                    });
                let app = self.apps.dtn();
                for k in evicted.iter().filter(|k| k.space == Space::DTN) {
                    let gone_id = BundleId(k.id);
                    d.forget_keeping_record(app, wall, &gone_id);
                    gone.insert(gone_id);
                }
                admitted.ok()?;
                let mut c = Cur(runs);
                let taken = take_runs(&mut c, total, sealed_len, &layout);
                let Some((sealed, have)) = taken else {
                    let _ = d.led.release(&id.store_key());
                    return None;
                };
                let outboard = alloc::vec![0; outboard_len];
                d.partials
                    .insert(*id, Partial::new(signed, sealed, outboard, have, true));
                out.partial += 1;
                // A torn run is cut off the host's record, so the next append follows a whole run.
                if !c.0.is_empty() {
                    let whole = rec.get(..rec.len() - c.0.len())?;
                    self.apps.dtn().save_record(id, whole);
                }
            }
        }
        Some(())
    }
}

/// Whether the runs left in a partial record are whole, as [`take_runs`] reads them, without holding any of them.
fn check_runs(c: &mut Cur<'_>, total: u64, slice_len: u64) -> Option<()> {
    while !c.0.is_empty() {
        let (Some(a), Some(b)) = (c.u64(), c.u64()) else {
            return Some(());
        };
        if a >= b || b > total || !a.is_multiple_of(slice_len) || !b.is_multiple_of(slice_len) {
            return None;
        }
        if c.take(usize::try_from(b - a).ok()?).is_none() {
            return Some(());
        }
    }
    Some(())
}

/// The runs of a partial record into a buffer of `sealed_len` bytes and its held set. A run cut short at the end (a
/// crash during an append) is left out; any other bad run drops the record.
fn take_runs(
    c: &mut Cur<'_>,
    total: u64,
    sealed_len: usize,
    layout: &pinc_dtn::layout::SliceLayout,
) -> Option<(Vec<u8>, crate::dtn::Symbols)> {
    let mut sealed = alloc::vec![0u8; sealed_len];
    let mut have = no_symbols(layout)?;
    while !c.0.is_empty() {
        let at = c.0;
        let (Some(a), Some(b)) = (c.u64(), c.u64()) else {
            c.0 = at;
            break;
        };
        if a >= b || b > total {
            return None;
        }
        let Some(bytes) = c.take(usize::try_from(b - a).ok()?) else {
            c.0 = at;
            break;
        };
        sealed
            .get_mut(usize::try_from(a).ok()?..usize::try_from(b).ok()?)?
            .copy_from_slice(bytes);
        have.insert(a..b).ok()?;
    }
    Some((sealed, have))
}

/// A probe of the resume records, for the trace check (cargo feature `trace`): the node's own writers and readers.
#[cfg(feature = "trace")]
#[doc(hidden)]
pub mod probe {
    use alloc::vec::Vec;

    use pinc_crypto::{IdentityAlg, NodeId as FullId};
    use pinc_dtn::head::SignedHead;

    /// A record as read back.
    pub enum Read {
        /// A bundle delivered here, remembered until `expires`.
        Received {
            /// When the memory ends (wall milliseconds).
            expires: u64,
        },
        /// A held bundle.
        Held {
            /// The copies held.
            copies: u16,
            /// Whether custody is owed.
            custody: bool,
            /// The algorithm tag of the previous holder.
            alg: u8,
            /// The key bytes of the previous holder.
            key: [u8; 32],
            /// The bytes charged.
            bytes: u64,
            /// The signed head.
            signed: SignedHead,
        },
        /// A partial bundle.
        Partial {
            /// The signed head.
            signed: SignedHead,
            /// The runs part, unread.
            runs: Vec<u8>,
        },
    }

    /// The record of a bundle delivered here.
    #[must_use]
    pub fn received(expires: u64) -> Vec<u8> {
        super::received_record(expires)
    }

    /// The record of a held bundle; `None` when its head does not fit.
    #[must_use]
    pub fn held(
        copies: u16,
        custody: bool,
        alg: IdentityAlg,
        key: [u8; 32],
        bytes: u64,
        signed: &SignedHead,
    ) -> Option<Vec<u8>> {
        super::held_record(copies, custody, &FullId { alg, bytes: key }, bytes, signed)
    }

    /// The first save of a partial bundle: its head and these runs.
    #[must_use]
    pub fn partial(signed: &SignedHead, runs: &[(u64, u64, &[u8])]) -> Option<Vec<u8>> {
        let mut rec = super::partial_head(signed, 0)?;
        for &(a, b, bytes) in runs {
            super::put_run(&mut rec, a, b, bytes);
        }
        Some(rec)
    }

    /// A later save of a partial bundle: these runs, appended.
    #[must_use]
    pub fn append(runs: &[(u64, u64, &[u8])]) -> Vec<u8> {
        let mut rec = Vec::new();
        for &(a, b, bytes) in runs {
            super::put_run(&mut rec, a, b, bytes);
        }
        rec
    }

    /// Read a record whole.
    #[must_use]
    pub fn read(rec: &[u8]) -> Option<Read> {
        Some(match super::read_record(rec)? {
            super::Record::Received { expires } => Read::Received { expires },
            super::Record::Held {
                copies,
                custody,
                prev,
                bytes,
                signed,
            } => Read::Held {
                copies,
                custody,
                alg: prev.alg.tag(),
                key: prev.bytes,
                bytes,
                signed,
            },
            super::Record::Partial { signed, runs } => Read::Partial {
                signed,
                runs: runs.to_vec(),
            },
        })
    }

    /// The bundle's total length and slice length, from its head.
    #[must_use]
    pub fn layout(signed: &SignedHead) -> Option<(u64, u64)> {
        let l = signed.head().layout().ok()?;
        Some((l.total_len(), l.slice_len()))
    }

    /// `check_runs` over `runs`.
    #[must_use]
    pub fn check_runs(runs: &[u8], total: u64, slice_len: u64) -> bool {
        super::check_runs(&mut super::Cur(runs), total, slice_len).is_some()
    }

    /// `take_runs` over `runs` for the bundle of `signed`: the buffer, the slices held after it (0-based) and the
    /// length of the torn tail left.
    #[must_use]
    pub fn take_runs(signed: &SignedHead, runs: &[u8]) -> Option<(Vec<u8>, Vec<u64>, usize)> {
        let layout = signed.head().layout().ok()?;
        let total = layout.total_len();
        let mut c = super::Cur(runs);
        let (sealed, have) = super::take_runs(&mut c, total, usize::try_from(total).ok()?, &layout)?;
        let held = (0..total / layout.slice_len()).filter(|&i| have.holds(i)).collect();
        Some((sealed, held, c.0.len()))
    }
}
