//! What the relay keeps across a restart, and the work of keeping it: the records of the store and the packets held
//! for sleeping members.
//!
//! Every change the machine reports (a record stored, a packet held or handed over) marks a node; the run loop takes
//! one job at a time and writes it through the [`Store`](super::super::store::Store). A record the machine dropped by
//! lifetime is removed from the store; a record and a packet come back with the time they arrived, so what is left of
//! their lifetime is the same after a restart.
//!
//! A write that fails or is dropped with its run is marked again, and a failed one is tried again after `RETRY_NS`,
//! behind the marks not tried yet and up to `MAX_TRIES` times; a failure of the store is counted and reported, a write
//! given up counts once more, and so does a mark the table has no room for.
//!
//! Invariants: the nodes marked are at most twice the record table for records kept, twice for records removed, and
//! four times the mailbox member table; a packet is written with its arrival time and restored oldest first; nothing
//! past its lifetime is restored. A wall clock that goes back across a restart lengthens what the store kept by up to
//! the step back: the node cannot know it.

use alloc::collections::{BTreeMap, VecDeque};
use alloc::vec::Vec;

use pinc_connect::carrier::NODE_ID_LEN;
use pinc_connect::carrier::frame::MAX_PACKET_LEN;
use pinc_connect::record::Record;
use pinc_connect::relay::rule::{RECORD_TTL_NS, SWEEP_NS};
use pinc_crypto::{IdentityAlg, NodeId};

use super::Core;
use crate::relay::access::Access;
use crate::relay::limits::{MAILBOX_MEMBERS, RECORDS};
use crate::relay::store::{Kept, node_key};
use pinc_keystore::KeyStore;

/// The nodes whose state is waiting to be written to the store.
#[derive(Debug, Default)]
pub(super) struct Keep {
    /// Records stored and not yet written: at most the record table, and at most one more table between two sweeps.
    records: BTreeMap<[u8; 33], NodeId>,
    /// Records the store holds and the machine may have dropped: at most twice the record table.
    held: BTreeMap<[u8; 33], NodeId>,
    /// Records to remove from the store: at most twice the record table, a mark past it is lost and counted.
    removed: BTreeMap<[u8; 33], NodeId>,
    /// Members whose held packets changed.
    mail: Vec<NodeId>,
    /// When `held` is next checked against the machine's records; `None` before the first check.
    next_sweep: Option<u64>,
    /// Not before this time is a failed write tried again; zero when none failed.
    retry_at: u64,
    /// Writes that failed, oldest first, with the tries so far: served after every mark not yet tried, at most
    /// [`FAILED`].
    failed: VecDeque<(Mark, u8)>,
    /// The tries so far of the write taken last: zero for a mark not tried before.
    tries: u8,
    /// Restoring: the machine reports what it restores, which is already in the store.
    restoring: bool,
}

impl Keep {
    /// Mark `node` to be removed from the store; false if the table is full and the mark is lost (the record stays in
    /// the store, which drops it at the next start, when it is past its lifetime).
    fn mark_removed(removed: &mut BTreeMap<[u8; 33], NodeId>, node: NodeId) -> bool {
        let key = node_key(&node);
        if removed.len() >= 2 * RECORDS && !removed.contains_key(&key) {
            return false;
        }
        removed.insert(key, node);
        true
    }
}

/// How long after a failed write the next is tried.
const RETRY_NS: u64 = 1_000_000_000;

/// How many times a write is tried before it is given up and counted: with [`RETRY_NS`] that is about eight seconds,
/// long enough for a store that stumbled and not so long that a write the store will never take keeps being served.
/// What was given up is written again the next time its node changes, and the store drops a record past its lifetime
/// at the next start.
const MAX_TRIES: u8 = 8;

/// How many failed writes wait to be tried again; one past it is given up and counted like one tried [`MAX_TRIES`]
/// times.
const FAILED: usize = 64;

/// What a write is about, kept while it is out so a failure or a dropped run can mark the node again.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        self.push_mail(node);
    }

    /// Mark `node` for a mailbox write; a mark past the table is counted as a failed write.
    fn push_mail(&mut self, node: NodeId) {
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
        let mut lost = false;
        let Keep {
            held, records, removed, ..
        } = keep;
        held.retain(|key, node| {
            let alive = sm.record_received(node).is_some();
            if !alive {
                records.remove(key);
                lost |= !Keep::mark_removed(removed, *node);
            }
            alive
        });
        // one count and one event per sweep, not one per mark
        if lost {
            self.store_failed();
        }
    }

    /// A write that was taken did not finish with the run: mark its node again, behind the ones not tried if it had
    /// failed before.
    pub(crate) fn requeue(&mut self, mark: Mark) {
        let tries = core::mem::take(&mut self.keep.tries);
        if tries > 0 && self.keep.failed.len() < FAILED {
            self.keep.failed.push_front((mark, tries));
            return;
        }
        match mark {
            // `held` already has the node unless a sweep took it out: it is not put back for a record that is gone
            Mark::Put(n) => {
                self.keep.records.insert(node_key(&n), n);
            }
            Mark::Remove(n) => {
                if !Keep::mark_removed(&mut self.keep.removed, n) {
                    self.store_failed();
                }
            }
            Mark::Mail(n) => self.note_mail(n),
        }
    }

    /// The store refused a write at `now`: it is counted, tried again after [`RETRY_NS`] behind the marks not tried
    /// yet, and given up (counted once more) after [`MAX_TRIES`] tries.
    pub(crate) fn write_failed(&mut self, mark: Mark, now: u64) {
        let tries = core::mem::take(&mut self.keep.tries).saturating_add(1);
        self.keep.retry_at = now.saturating_add(RETRY_NS);
        self.store_failed();
        if tries >= MAX_TRIES || self.keep.failed.len() >= FAILED {
            self.store_failed();
        } else if !self.keep.failed.iter().any(|(m, _)| *m == mark) {
            self.keep.failed.push_back((mark, tries));
        }
    }

    /// When a write held back by a failure may be tried again, or the end of time.
    pub(super) const fn keep_wake(&self) -> u64 {
        if self.keep.retry_at > self.last_now {
            self.keep.retry_at
        } else {
            u64::MAX
        }
    }

    /// The next write to the store, if any: a mark not tried yet first, then the oldest failed one.
    pub(crate) fn next_job(&mut self) -> Option<Job> {
        if self.last_now < self.keep.retry_at {
            return None;
        }
        self.keep.tries = 0;
        if let Some((_, n)) = self.keep.removed.pop_first() {
            return Some(Job::Remove(n));
        }
        while let Some((_, n)) = self.keep.records.pop_first() {
            if let Some(job) = self.put_job(n) {
                return Some(job);
            }
        }
        if let Some(n) = self.keep.mail.pop() {
            return Some(self.mail_job(n));
        }
        while let Some((mark, tries)) = self.keep.failed.pop_front() {
            let job = match mark {
                Mark::Put(n) => self.put_job(n),
                // a record that came back since is written over, not removed
                Mark::Remove(n) => self.sm.record_received(&n).is_none().then_some(Job::Remove(n)),
                Mark::Mail(n) => Some(self.mail_job(n)),
            };
            if job.is_some() {
                self.keep.tries = tries;
                return job;
            }
        }
        None
    }

    /// The write of the record held for `n`, if the machine still holds it.
    fn put_job(&self, n: NodeId) -> Option<Job> {
        let received = self.sm.record_received(&n)?;
        let rec = self.sm.lookup(received, &n)?;
        Some(Job::Put(n, rec.to_vec(), received))
    }

    /// The write of the packets held for `n` now.
    fn mail_job(&self, n: NodeId) -> Job {
        let mut blob = Vec::new();
        let mut buf = [0u8; MAX_PACKET_LEN];
        let mut i = 0;
        while let Some((d, at)) = self.sm.held_packet(&n, i, &mut buf) {
            encode(&mut blob, &d.src, d.flag, at, buf.get(..d.len).unwrap_or_default());
            i += 1;
        }
        Job::Mail(n, blob)
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
                (false, Some(n)) => {
                    if !Keep::mark_removed(&mut self.keep.removed, n) {
                        self.store_failed();
                    }
                }
                (_, None) => self.counters.store_errors += 1,
            }
        }
        for (node, blob) in &kept.mailboxes {
            let mut dropped = false;
            for (src, flag, at, body) in decode(blob) {
                dropped |= self.sm.restore_held(now, at, node, &src, flag, body).is_err();
            }
            if dropped || decode(blob).next().is_none() {
                self.push_mail(*node);
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

    fn nid(i: u16) -> NodeId {
        let mut bytes = [0u8; 32];
        bytes[..2].copy_from_slice(&i.to_be_bytes());
        NodeId {
            alg: IdentityAlg::Ed25519,
            bytes,
        }
    }

    fn signed(tag: u16, home: NodeId) -> (NodeId, Vec<u8>) {
        let mut seed = [1u8; 32];
        seed[..2].copy_from_slice(&tag.to_be_bytes());
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap();
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

    /// A store that holds more mailboxes than the table has room for does not make the marks pass it, and the marks lost
    /// are counted.
    #[test]
    fn the_restore_marks_mailboxes_up_to_the_table_and_counts_the_rest() {
        let mut core = core();
        let over = 4 * MAILBOX_MEMBERS + 3;
        let kept = Kept {
            records: vec![],
            mailboxes: (0..over)
                .map(|i| (nid(u16::try_from(i).unwrap()), Vec::new()))
                .collect(),
        };
        core.restore(T0, &kept);
        assert_eq!(core.keep.mail.len(), 4 * MAILBOX_MEMBERS, "the marks passed the table");
        assert_eq!(core.counters.store_errors, 3, "the marks lost were not counted");
    }

    /// The records to remove from the store never pass twice the record table, and the ones lost are counted.
    #[test]
    fn removals_past_the_table_are_counted_and_not_kept() {
        let mut core = core();
        for i in 0..=u16::try_from(2 * RECORDS).unwrap() {
            core.requeue(Mark::Remove(nid(i)));
        }
        assert!(
            core.keep.removed.len() <= 2 * RECORDS,
            "{} removals kept",
            core.keep.removed.len()
        );
        assert_eq!(core.counters.store_errors, 1, "the lost removal was not counted");
    }

    /// A store that fails every write does not let the removals pile up as records expire.
    #[test]
    fn removals_stay_bounded_while_the_store_fails() {
        let mut core = core();
        let home = core.node_id();
        let table = u16::try_from(RECORDS).unwrap();
        for round in 0..3u16 {
            let at = T0 + (u64::from(round) + 1) * 2 * RECORD_TTL_NS;
            for i in 0..table {
                let (n, rec) = signed(round * table + i, home);
                core.sm.restore_record(at, &rec, &mut core.fx).unwrap();
                core.note_record(n);
            }
            core.on_timeout(at + RECORD_TTL_NS + SEC);
            if let Some(job) = core.next_job() {
                core.requeue(job.mark());
            }
            assert!(
                core.keep.removed.len() <= 2 * RECORDS,
                "{} removals kept",
                core.keep.removed.len()
            );
        }
        assert!(core.counters.store_errors >= 1, "the lost removals were not counted");
    }
}
