//! The records that let the delay-tolerant layer resume after a restart.
//!
//! The host keeps complete bundles in its store; the node adds one small record per bundle it looks after, through
//! [`DtnApp::save_record`](crate::DtnApp::save_record): a held bundle (its signed head, the copies this node still
//! holds, and whether custody is owed to a previous holder), a partial bundle (its head, the symbols verified so far
//! and where the next ask starts) or the memory that a bundle was delivered here. [`Node::dtn_restore`] reads them
//! back after a restart and rebuilds the forwarder, the ledger and the custody book from them.
//!
//! Invariants: a record is written only for state the node holds; a record that cannot be read back whole is dropped,
//! never half applied; the ledger is charged for every restored bundle before it is held, so a restart never lets the
//! node hold more than its budget; the copies restored are those the node held when it last wrote the record, so a
//! copy handed on before a crash is not counted twice. A partial bundle is saved every [`SAVE_BYTES`] (256 KiB) of verified bytes
//! and when its session ends, so a crash loses at most the symbols since then, which the holder sends again.

#![allow(
    clippy::many_single_char_names,
    reason = "d, p, c and r are the layer's state, a part, the cursor over a record and a run, as in the modules around"
)]

use alloc::vec::Vec;

use vinc_crypto::{IdentityAlg, NodeId as FullId};
use vinc_dag::ranges::VerifiedRanges;
use vinc_dtn::custody::Incoming;
use vinc_dtn::forward::{Held, Input};
use vinc_dtn::head::{BundleId, SignedHead};
use vinc_dtn::store::{Class, Key, Space};

use crate::apps::{Apps, DtnApp, ServeSource};
use crate::config::{Nanos, Store};
use crate::dtn::{Dtn, Partial};
use crate::ep::Ep;
use crate::node::Node;

/// The version of the record format.
const VERSION: u8 = 1;
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

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
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
        let mut rec = Vec::with_capacity(signed.encoded_len() + 64);
        rec.extend_from_slice(&[VERSION, HELD]);
        rec.extend_from_slice(&copies.to_be_bytes());
        let (custody, prev) = d.book.owed_to(id).map_or((0, self.ident), |p| (1, p));
        rec.push(custody);
        put_node(&mut rec, &prev);
        rec.extend_from_slice(&bytes.to_be_bytes());
        if put_head(&mut rec, signed) {
            self.apps.dtn().save_record(id, &rec);
        }
    }

    /// Write the memory that `id` was delivered here, until `expires`.
    pub(crate) fn dtn_save_received(&mut self, id: &BundleId, expires: u64) {
        let mut rec = Vec::with_capacity(10);
        rec.extend_from_slice(&[VERSION, RECEIVED]);
        rec.extend_from_slice(&expires.to_be_bytes());
        self.apps.dtn().save_record(id, &rec);
    }

    /// Write the record of a partial bundle: its head, the cursor and the verified symbols.
    pub(crate) fn dtn_save_partial(&mut self, id: &BundleId) {
        let Some(d) = self.dtn.as_deref_mut() else {
            return;
        };
        let Some(p) = d.partials.get(id) else {
            return;
        };
        let ranges: Vec<core::ops::Range<u64>> = p.have.iter().collect();
        let Ok(n) = u16::try_from(ranges.len()) else {
            return;
        };
        let mut rec =
            Vec::with_capacity(usize::try_from(p.have.covered_len()).unwrap_or(0) + 64 + p.signed.encoded_len());
        rec.extend_from_slice(&[VERSION, PARTIAL]);
        if !put_head(&mut rec, &p.signed) {
            return;
        }
        rec.extend_from_slice(&p.cursor.to_be_bytes());
        rec.extend_from_slice(&n.to_be_bytes());
        for r in &ranges {
            rec.extend_from_slice(&r.start.to_be_bytes());
            rec.extend_from_slice(&r.end.to_be_bytes());
        }
        for r in &ranges {
            let (Ok(a), Ok(b)) = (usize::try_from(r.start), usize::try_from(r.end)) else {
                return;
            };
            let Some(bytes) = p.sealed.get(a..b) else { return };
            rec.extend_from_slice(bytes);
        }
        let covered = p.have.covered_len();
        d.saved.insert(*id, covered);
        self.apps.dtn().save_record(id, &rec);
    }

    /// Save every partial bundle that has grown since its last record.
    pub(crate) fn dtn_save_grown(&mut self) {
        let grown: Vec<BundleId> = self
            .dtn
            .as_deref()
            .map(|d| {
                d.partials
                    .iter()
                    .filter(|(id, p)| p.have.covered_len() > d.saved.get(id).copied().unwrap_or(0))
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
    /// counted.
    pub fn dtn_restore(&mut self, now: Nanos) -> DtnRestored {
        self.begin(now);
        let mut out = DtnRestored::default();
        if self.dtn.is_none() {
            return out;
        }
        let mut n = 0;
        while let Some((id, rec)) = self.apps.dtn().record_at(n).map(|(i, r)| (i, r.to_vec())) {
            n += 1;
            if self.restore_one(&id, &rec, &mut out).is_none() {
                out.dropped += 1;
                self.apps.dtn().drop_record(&id);
            }
        }
        self.dtn_contacts_changed();
        self.settle(now);
        out
    }

    fn restore_one(&mut self, id: &BundleId, rec: &[u8], out: &mut DtnRestored) -> Option<()> {
        let wall = self.io.wall_ms();
        let mut c = Cur(rec);
        if c.u8()? != VERSION {
            return None;
        }
        let kind = c.u8()?;
        let d = self.dtn.as_deref_mut()?;
        match kind {
            RECEIVED => {
                let expires = c.u64()?;
                if expires <= wall {
                    return None;
                }
                d.received.insert(*id, expires);
                out.received += 1;
            }
            HELD => {
                let copies = c.u16()?;
                let custody = c.u8()? == 1;
                let prev = c.node()?;
                let bytes = c.u64()?;
                let signed = take_head(&mut c)?;
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
                    d.forget(app, wall, &BundleId(k.id));
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
            PARTIAL => {
                let signed = take_head(&mut c)?;
                let h = *signed.head();
                let cursor = c.u64()?;
                let count = usize::from(c.u16()?);
                if h.id != *id || h.is_expired(wall) {
                    return None;
                }
                let layout = h.layout().ok()?;
                let total = layout.total_len();
                let sealed_len = usize::try_from(total).ok()?;
                let outboard_len = usize::try_from(layout.outboard_len().ok()?).ok()?;
                let mut ranges = Vec::with_capacity(count);
                for _ in 0..count {
                    let (a, b) = (c.u64()?, c.u64()?);
                    if a >= b || b > total {
                        return None;
                    }
                    ranges.push(a..b);
                }
                let mut sealed = alloc::vec![0u8; sealed_len];
                let mut have = VerifiedRanges::new();
                for r in &ranges {
                    let bytes = c.take(usize::try_from(r.end - r.start).ok()?)?;
                    sealed
                        .get_mut(usize::try_from(r.start).ok()?..usize::try_from(r.end).ok()?)?
                        .copy_from_slice(bytes);
                    have.insert(r.clone()).ok()?;
                }
                let mut evicted: Vec<Key> = Vec::new();
                let admitted = d
                    .led
                    .admit(id.store_key(), total, Class::Transit, h.expires_at(), wall, |e| {
                        evicted.push(e.key);
                    });
                let app = self.apps.dtn();
                for k in evicted.iter().filter(|k| k.space == Space::DTN) {
                    d.forget(app, wall, &BundleId(k.id));
                }
                admitted.ok()?;
                let covered = have.covered_len();
                d.partials.insert(
                    *id,
                    Partial {
                        signed,
                        sealed,
                        outboard: alloc::vec![0; outboard_len],
                        have,
                        cursor,
                    },
                );
                d.saved.insert(*id, covered);
                out.partial += 1;
            }
            _ => return None,
        }
        Some(())
    }
}

impl Dtn {
    /// Forget the saved-progress mark of a bundle.
    pub(crate) fn unmark(&mut self, id: &BundleId) {
        self.saved.remove(id);
    }
}
