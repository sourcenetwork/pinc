//! What the relay keeps across a restart, and the work of keeping it: the records of the store and the packets held
//! for sleeping members.
//!
//! Every change the machine reports (a record stored, a packet held or handed over) marks a node; the run loop takes
//! one job at a time and writes it through the [`Store`](super::super::store::Store). A record the machine dropped by
//! lifetime is removed from the store; a record and a packet come back with the time they arrived, so what is left of
//! their lifetime is the same after a restart.
//!
//! A write that fails or is dropped with its run is marked again, and tried again after `RETRY_NS`; a failure of the
//! store is counted and reported, and a mark the table has no room for counts as one.
//!
//! Invariants: the nodes marked are at most twice the record table and four times the mailbox member table; a packet
//! is written with its arrival time and restored oldest first; nothing past its lifetime is restored.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use pinc_connect::carrier::NODE_ID_LEN;
use pinc_connect::carrier::frame::MAX_PACKET_LEN;
use pinc_connect::record::Record;
use pinc_connect::relay::rule::{RECORD_TTL_NS, SWEEP_NS};
use pinc_crypto::{IdentityAlg, NodeId};

use super::Core;
use crate::relay::access::Access;
use crate::relay::limits::MAILBOX_MEMBERS;
use crate::relay::store::{Kept, node_key};
use pinc_keystore::KeyStore;

/// The nodes whose state is waiting to be written to the store.
#[derive(Debug, Default)]
pub(super) struct Keep {
    /// Records stored and not yet written: at most the record table, and at most one more table between two sweeps.
    records: BTreeMap<[u8; 33], NodeId>,
    /// Records the store holds and the machine may have dropped: at most twice the record table.
    held: BTreeMap<[u8; 33], NodeId>,
    /// Records to remove from the store.
    removed: Vec<NodeId>,
    /// Members whose held packets changed.
    mail: Vec<NodeId>,
    /// When `held` is next checked against the machine's records; `None` before the first check.
    next_sweep: Option<u64>,
    /// Not before this time is a failed write tried again; zero when none failed.
    retry_at: u64,
    /// Restoring: the machine reports what it restores, which is already in the store.
    restoring: bool,
}

/// How long after a failed write the next is tried.
const RETRY_NS: u64 = 1_000_000_000;

/// What a write is about, kept while it is out so a failure or a dropped run can mark the node again.
#[derive(Debug, Clone, Copy)]
pub(crate) enum Mark {
    /// A record was kept.
    Put(NodeId),
    /// A record was forgotten.
    Remove(NodeId),
    /// The packets held for a member were kept.
    Mail(NodeId),
}

/// One write to the store.
#[derive(Debug)]
pub(crate) enum Job {
    /// Keep a record and the time it was received.
    Put(NodeId, Vec<u8>, u64),
    /// Forget a record.
    Remove(NodeId),
    /// Keep the packets held for a member (empty: none are held).
    Mail(NodeId, Vec<u8>),
}

impl Job {
    /// The mark that gives this write back.
    pub(crate) fn mark(&self) -> Mark {
        match *self {
            Self::Put(n, ..) => Mark::Put(n),
            Self::Remove(n) => Mark::Remove(n),
            Self::Mail(n, _) => Mark::Mail(n),
        }
    }
}

/// Append one packet to a member's blob: source, flag, arrival, length, body.
pub(super) fn encode(out: &mut Vec<u8>, src: &NodeId, flag: u8, at: u64, body: &[u8]) {
    out.push(src.alg.tag());
    out.extend_from_slice(&src.bytes);
    out.push(flag);
    out.extend_from_slice(&at.to_be_bytes());
    out.extend_from_slice(&u16::try_from(body.len()).unwrap_or(0).to_be_bytes());
    out.extend_from_slice(body);
}

/// The packets of a blob, oldest first, up to the first one that does not parse.
fn decode(mut blob: &[u8]) -> impl Iterator<Item = (NodeId, u8, u64, &[u8])> {
    core::iter::from_fn(move || {
        let (head, rest) = blob.split_at_checked(NODE_ID_LEN + 1 + 8 + 2)?;
        let (&tag, head) = head.split_first()?;
        let (bytes, head) = head.split_first_chunk::<32>()?;
        let (&flag, head) = head.split_first()?;
        let (at, head) = head.split_first_chunk::<8>()?;
        let len = usize::from(u16::from_be_bytes(*head.first_chunk::<2>()?));
        let (body, rest) = rest.split_at_checked(len)?;
        blob = rest;
        let src = NodeId {
            alg: IdentityAlg::from_tag(tag)?,
            bytes: *bytes,
        };
        Some((src, flag, u64::from_be_bytes(*at), body))
    })
}

impl<S, K: KeyStore, A: Access> Core<S, K, A> {
    /// A record was stored: write it, and remember the store has it.
    pub(super) fn note_record(&mut self, node: NodeId) {
        if self.keep.restoring {
            return;
        }
        let key = node_key(&node);
        self.keep.records.insert(key, node);
        self.keep.held.insert(key, node);
    }

    /// A packet was held for `node` or handed to it: write what is held. A mark the table has no room for leaves the
    /// store behind: it is counted as a failed write.
    pub(super) fn note_mail(&mut self, node: NodeId) {
        if self.keep.restoring || self.keep.mail.contains(&node) {
            return;
        }
        if self.keep.mail.len() < 4 * MAILBOX_MEMBERS {
            self.keep.mail.push(node);
        } else {
            self.store_failed();
        }
    }

    /// The machine ran its timers: a record it dropped by lifetime is removed from the store. The records the store
    /// holds are checked once per sweep of the machine, whatever the count of records did.
    pub(super) fn note_sweep(&mut self, now: u64) {
        if self.keep.next_sweep.is_some_and(|at| now < at) {
            return;
        }
        self.keep.next_sweep = Some(now.saturating_add(SWEEP_NS));
        let Self { sm, keep, .. } = self;
        let Keep {
            held, records, removed, ..
        } = keep;
        held.retain(|key, node| {
            let alive = sm.record_received(node).is_some();
            if !alive {
                records.remove(key);
                removed.push(*node);
            }
            alive
        });
    }

    /// A write that was taken did not finish: mark its node again.
    pub(crate) fn requeue(&mut self, mark: Mark) {
        match mark {
            Mark::Put(n) => self.note_record(n),
            Mark::Remove(n) => {
                if !self.keep.removed.contains(&n) {
                    self.keep.removed.push(n);
                }
            }
            Mark::Mail(n) => self.note_mail(n),
        }
    }

    /// The store refused a write at `now`: the next one waits for [`RETRY_NS`].
    pub(crate) const fn retry_after(&mut self, now: u64) {
        self.keep.retry_at = now.saturating_add(RETRY_NS);
    }

    /// When a write held back by a failure may be tried again, or the end of time.
    pub(super) const fn keep_wake(&self) -> u64 {
        if self.keep.retry_at > self.last_now {
            self.keep.retry_at
        } else {
            u64::MAX
        }
    }

    /// The next write to the store, if any.
    pub(crate) fn next_job(&mut self) -> Option<Job> {
        if self.last_now < self.keep.retry_at {
            return None;
        }
        if let Some(n) = self.keep.removed.pop() {
            return Some(Job::Remove(n));
        }
        while let Some((_, n)) = self.keep.records.pop_first() {
            if let Some(received) = self.sm.record_received(&n)
                && let Some(rec) = self.sm.lookup(received, &n)
            {
                return Some(Job::Put(n, rec.to_vec(), received));
            }
        }
        let n = self.keep.mail.pop()?;
        let mut blob = Vec::new();
        let mut buf = [0u8; MAX_PACKET_LEN];
        let mut i = 0;
        while let Some((d, at)) = self.sm.held_packet(&n, i, &mut buf) {
            encode(&mut blob, &d.src, d.flag, at, buf.get(..d.len).unwrap_or_default());
            i += 1;
        }
        Some(Job::Mail(n, blob))
    }

    /// Put back what the store kept. A record or packet past its lifetime is not restored, and a record is removed from
    /// the store; a record that does not verify is removed too. A record whose bytes do not parse names no node: it is
    /// counted as a store error and left for the store to drop.
    pub(crate) fn restore(&mut self, now: u64, kept: &Kept) {
        self.keep.restoring = true;
        for r in &kept.records {
            let node = Record::parse(&r.bytes).ok().map(|p| p.node);
            let live = now.saturating_sub(r.received) < RECORD_TTL_NS;
            let ok = live && self.sm.restore_record(r.received, &r.bytes, &mut self.fx).is_ok();
            self.flush();
            match (ok, node) {
                (true, Some(n)) => {
                    self.keep.held.insert(node_key(&n), n);
                }
                (false, Some(n)) => self.keep.removed.push(n),
                (_, None) => self.counters.store_errors += 1,
            }
        }
        for (node, blob) in &kept.mailboxes {
            let mut dropped = false;
            for (src, flag, at, body) in decode(blob) {
                dropped |= self.sm.restore_held(now, at, node, &src, flag, body).is_err();
            }
            if dropped || decode(blob).next().is_none() {
                self.keep.mail.push(*node);
            }
        }
        self.keep.restoring = false;
    }
}

#[cfg(test)]
#[allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::panic,
    reason = "tests assert"
)]
mod tests {
    use alloc::rc::Rc;
    use alloc::vec;
    use core::cell::RefCell;
    use core::net::SocketAddr;

    use pinc_connect::record::{self, Reach, RecordFields};
    use pinc_crypto::Keypair;
    use pinc_keystore::SoftwareStore;

    use super::*;
    use crate::keys::Identity;
    use crate::relay::access::AllowAll;
    use crate::relay::limits::Limits;
    use crate::relay::store::KeptRecord;

    const T0: u64 = 1_000_000_000_000;
    const SEC: u64 = 1_000_000_000;

    fn core() -> Core<(), SoftwareStore, AllowAll> {
        let identity = Rc::new(RefCell::new(Identity::from_seed_with(&[7; 32], &[0; 32]).unwrap()));
        let local: SocketAddr = "192.0.2.1:4000".parse().unwrap();
        Core::new(identity, AllowAll, &[], Limits::default(), Some(local), T0).unwrap()
    }

    fn signed(tag: u8, home: NodeId) -> (NodeId, Vec<u8>) {
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[tag; 32]).unwrap();
        let mut out = vec![0u8; record::MAX_RECORD_LEN];
        let n = record::sign(
            &kp,
            &RecordFields {
                home,
                seq: 1,
                reach: Reach::UdpBlocked,
                addrs: &[],
                hints: &[],
            },
            &mut out,
        )
        .unwrap();
        out.truncate(n);
        (kp.node_id(), out)
    }

    /// A record that expires in the same sweep another arrives in leaves the store, though the count did not fall.
    #[test]
    fn a_record_that_expires_as_another_arrives_is_removed_from_the_store() {
        let mut core = core();
        let home = core.node_id();
        let (a, rec_a) = signed(1, home);
        let (b, rec_b) = signed(2, home);
        let kept = Kept {
            records: vec![KeptRecord {
                bytes: rec_a,
                received: T0,
            }],
            mailboxes: vec![],
        };
        core.restore(T0 + SEC, &kept);
        assert!(core.next_job().is_none(), "a restored record is in the store already");
        let at = T0 + RECORD_TTL_NS;
        core.sm.restore_record(at, &rec_b, &mut core.fx).unwrap();
        core.note_record(b);
        core.on_timeout(at + SEC);
        assert_eq!(core.sm.record_received(&a), None);
        let Some(Job::Remove(gone)) = core.next_job() else {
            panic!("the expired record stays in the store");
        };
        assert_eq!(gone, a);
    }

    /// A mark the table has no room for is a store that is behind, and is counted like a failed write.
    #[test]
    fn a_mailbox_mark_past_the_table_is_counted() {
        let mut core = core();
        for i in 0..=u16::try_from(4 * MAILBOX_MEMBERS).unwrap() {
            let mut bytes = [0u8; 32];
            bytes[..2].copy_from_slice(&i.to_be_bytes());
            core.note_mail(NodeId {
                alg: IdentityAlg::Ed25519,
                bytes,
            });
        }
        assert_eq!(core.counters.store_errors, 1, "the lost mark was not counted");
    }
}
