//! What the relay keeps across a restart, and the work of keeping it: the records of the store, the packets held for
//! sleeping members and their sleep marks.
//!
//! Every change the machine reports (a record stored, a packet held or handed over) marks a node; the run loop takes
//! one job at a time and writes it through the [`Store`](super::super::store::Store). A record the machine dropped by
//! lifetime is removed from the store; a record and a packet come back with the time they arrived, so what is left of
//! their lifetime is the same after a restart.
//!
//! A member's blob is its packets, then an optional trailer of 18 bytes: a zero byte (no [`IdentityAlg`] tag, and too
//! short for a packet head, so a reader of the old form stops there and keeps the packets), the version 1, the time its
//! sleep notice was taken and the notice's clock. A mark comes back with its time and ends when it would have, with
//! the packets held under it; a blob with no trailer (the old form) restores its packets, which derive the mark from
//! the oldest of them, and is written again with it; a remainder that is neither (a newer version, a torn trailer or a
//! torn packet) keeps what parsed before it and is counted in the store errors once.
//!
//! A write that fails or is dropped with its run is marked again, and a failed one is tried again after `RETRY_NS`,
//! behind the marks not tried yet and up to `MAX_TRIES` times; a failure of the store is counted and reported, a write
//! given up counts once more, and so does a mark the table has no room for. A removal the store keeps refusing is given
//! up the same way and left for the next start, where [`Core::restore`] marks every record the machine did not take
//! for removal; so while removals are refused the store may hold more records than the table, by at most the removals
//! owed or given up, and each of them is counted.
//!
//! Invariants: the nodes marked are at most twice the record table for records kept, twice for records removed, and
//! the carrier table and the mailbox member table together (every member that can hold a mark or mail once); a packet
//! is written with its arrival time and restored oldest first; nothing past its lifetime is restored. A wall clock that goes back across a restart lengthens what the store kept by up to
//! the step back: the node cannot know it.

use alloc::collections::{BTreeMap, VecDeque};
use alloc::vec::Vec;

use pinc_connect::carrier::NODE_ID_LEN;
use pinc_connect::carrier::frame::MAX_PACKET_LEN;
use pinc_connect::record::Record;
use pinc_connect::relay::Reject;
use pinc_connect::relay::rule::{RECORD_TTL_NS, SWEEP_NS};
use pinc_crypto::{IdentityAlg, NodeId};

use super::Core;
use crate::relay::access::Access;
use crate::relay::limits::{CARRIERS, MAILBOX_MEMBERS, RECORDS};
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
    /// Members whose held packets changed, oldest first: at most the carrier table and the mailbox member table
    /// together, each member once.
    mail: VecDeque<NodeId>,
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
    /// What the write out now is about; a failure or the end of the run marks it again.
    writing: Option<Mark>,
    /// [`Core::restore_once`] ran: the machine holds what the store kept.
    restored: bool,
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

/// The first byte of the trailer of a blob: no [`IdentityAlg`] tag, so it never starts a packet.
const TRAILER: u8 = 0;
/// The version of the trailer.
const TRAILER_V1: u8 = 1;

/// Append the sleep mark of a member to its blob: the trailer byte, the version, the time the notice was taken and its
/// clock. A reader of the old form stops at it (18 bytes are no packet head) and keeps the packets before it.
pub(super) fn encode_mark(out: &mut Vec<u8>, at: u64, ts_ms: u64) {
    out.extend_from_slice(&[TRAILER, TRAILER_V1]);
    out.extend_from_slice(&at.to_be_bytes());
    out.extend_from_slice(&ts_ms.to_be_bytes());
}

/// The mark of a trailer: its time and the notice's clock, if `rest` is exactly a version 1 trailer.
fn decode_mark(rest: &[u8]) -> Option<(u64, u64)> {
    let body = rest.strip_prefix(&[TRAILER, TRAILER_V1])?;
    let (at, ts) = body.split_first_chunk::<8>()?;
    let ts = <[u8; 8]>::try_from(ts).ok()?;
    Some((u64::from_be_bytes(*at), u64::from_be_bytes(ts)))
}

/// The packets of a blob, oldest first, up to the first one that does not parse; what is left is [`Packets::rest`].
struct Packets<'a>(&'a [u8]);

impl<'a> Packets<'a> {
    /// What the packets did not take: empty, a trailer, or bytes that parse as neither.
    const fn rest(&self) -> &'a [u8] {
        self.0
    }
}

impl<'a> Iterator for Packets<'a> {
    type Item = (NodeId, u8, u64, &'a [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        let (head, rest) = self.0.split_at_checked(NODE_ID_LEN + 1 + 8 + 2)?;
        let (&tag, head) = head.split_first()?;
        let (bytes, head) = head.split_first_chunk::<32>()?;
        let (&flag, head) = head.split_first()?;
        let (at, head) = head.split_first_chunk::<8>()?;
        let len = usize::from(u16::from_be_bytes(*head.first_chunk::<2>()?));
        let (body, rest) = rest.split_at_checked(len)?;
        let src = NodeId {
            alg: IdentityAlg::from_tag(tag)?,
            bytes: *bytes,
        };
        self.0 = rest;
        Some((src, flag, u64::from_be_bytes(*at), body))
    }
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
        // vertexia: a node whose write is already queued keeps its older place, so its new mark can be written before
        // the removal of the mark it evicted; a stop between the two leaves one mark too many, which the restore drops
        // and counts (no mail is lost). Moving the node behind the removal would close it.
        if self.keep.restoring || self.keep.mail.contains(&node) {
            return;
        }
        self.push_mail(node);
    }

    /// Mark `node` for a mailbox write; a mark past the table is counted as a failed write.
    fn push_mail(&mut self, node: NodeId) {
        // every member that can hold a mark or mail fits once
        if self.keep.mail.len() < CARRIERS + MAILBOX_MEMBERS {
            self.keep.mail.push_back(node);
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

    /// The write out now, if any, is given back: the run that held it is gone.
    pub(crate) fn end_run(&mut self) {
        if let Some(mark) = self.keep.writing.take() {
            self.requeue(mark);
        }
    }

    /// The write taken last finished, `ok` if the store kept it; a failure is handled by [`Core::write_failed`] at the
    /// core's clock as of its last call.
    pub(crate) fn written(&mut self, ok: bool) {
        let mark = self.keep.writing.take();
        if !ok {
            match mark {
                Some(mark) => self.write_failed(mark, self.now_hint()),
                None => self.store_failed(),
            }
        }
    }

    /// The next write to the store, if one is due and none is out.
    pub(crate) fn next_write(&mut self) -> Option<Job> {
        if self.keep.writing.is_some() {
            return None;
        }
        let job = self.next_job()?;
        self.keep.writing = Some(job.mark());
        Some(job)
    }

    /// Whether [`Core::restore_once`] ran.
    pub(crate) const fn restored(&self) -> bool {
        self.keep.restored
    }

    /// [`Core::restore`] unless it ran already: a second run of the same core restores nothing.
    pub(crate) fn restore_once(&mut self, now: u64, kept: &Kept) {
        if self.keep.restored {
            return;
        }
        self.keep.restored = true;
        self.restore(now, kept);
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
        if let Some(n) = self.keep.mail.pop_front() {
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

    /// The write of the packets held for `n` now, and its sleep mark behind them: a member with a mark and no mail
    /// writes the trailer alone, one with neither writes nothing.
    fn mail_job(&self, n: NodeId) -> Job {
        let mut blob = Vec::new();
        let mut buf = [0u8; MAX_PACKET_LEN];
        let mut i = 0;
        while let Some((d, at)) = self.sm.held_packet(&n, i, &mut buf) {
            encode(&mut blob, &d.src, d.flag, at, buf.get(..d.len).unwrap_or_default());
            i += 1;
        }
        if let Some((at, ts_ms)) = self.sm.sleeper(&n) {
            encode_mark(&mut blob, at, ts_ms);
        }
        Job::Mail(n, blob)
    }

    /// Put back what the store kept. The machine takes the records in the order given until its table is full; a record
    /// it does not take (past its lifetime, not verifying, or no room) is marked for removal. A record or packet past its lifetime is not restored, and a record is removed from
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
        // members with packets first, then the bare marks: no restore evicts, so when the store holds more marks than
        // the table the ones that keep mail are the ones that fit, whatever the store's order
        for with_mail in [true, false] {
            for (node, blob) in &kept.mailboxes {
                if Packets(blob).next().is_some() == with_mail {
                    self.restore_mailbox(now, node, blob);
                }
            }
        }
        self.keep.restoring = false;
    }

    /// Put back the packets and the mark of one member's blob; called with `restoring` set.
    fn restore_mailbox(&mut self, now: u64, node: &NodeId, blob: &[u8]) {
        let mut packets = Packets(blob);
        let count = packets.by_ref().count();
        let rest = packets.rest();
        // a kept mark first: one that ended takes the blob's packets with it (they were held under it)
        let kept_mark = decode_mark(rest);
        if kept_mark.is_none() && !rest.is_empty() {
            // a newer version of the trailer, a torn trailer or a torn packet: what parsed is kept
            self.counters.store_errors += 1;
        }
        let mark = kept_mark.map(|(at, ts_ms)| self.sm.restore_sleep(now, node, at, ts_ms));
        let ended = mark == Some(Err(Reject::MailboxRefused));
        // the mark table has no room: the member keeps no mark and so no mail, the loss is counted once and the
        // write below makes the store drop what it kept
        let mut full = mark == Some(Err(Reject::SessionsFull));
        let marked = mark == Some(Ok(()));
        let mut dropped = ended || full;
        let mut restored = false;
        if !ended && !full {
            for (src, flag, at, body) in Packets(blob) {
                match self.sm.restore_held(now, at, node, &src, flag, body) {
                    Ok(()) => restored = true,
                    Err(e) => {
                        dropped = true;
                        full |= e == Reject::SessionsFull;
                    }
                }
            }
        }
        if full {
            self.counters.store_errors += 1;
        }
        // written again: a packet refused, nothing kept, packets with no kept mark (the old form or a torn trailer, so
        // the mark derived from them is written), or a mark moved back to the clock (the store keeps no time ahead
        // of it)
        let clamped = marked && kept_mark.is_some_and(|(at, _)| at > now);
        if dropped || (count == 0 && !marked) || (restored && !marked) || clamped {
            self.push_mail(*node);
        }
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
        for i in 0..=u16::try_from(CARRIERS + MAILBOX_MEMBERS).unwrap() {
            let mut bytes = [0u8; 32];
            bytes[..2].copy_from_slice(&i.to_be_bytes());
            core.note_mail(NodeId {
                alg: IdentityAlg::Ed25519,
                bytes,
            });
        }
        assert_eq!(core.counters.store_errors, 1, "the lost mark was not counted");
    }

    /// A store that holds more mailboxes than the table has room for does not make the marks pass it, and the marks
    /// lost are counted.
    #[test]
    fn the_restore_marks_mailboxes_up_to_the_table_and_counts_the_rest() {
        let mut core = core();
        let over = CARRIERS + MAILBOX_MEMBERS + 3;
        let kept = Kept {
            records: vec![],
            mailboxes: (0..over)
                .map(|i| (nid(u16::try_from(i).unwrap()), Vec::new()))
                .collect(),
        };
        core.restore(T0, &kept);
        assert_eq!(
            core.keep.mail.len(),
            CARRIERS + MAILBOX_MEMBERS,
            "the marks passed the table"
        );
        assert_eq!(core.counters.store_errors, 3, "the marks lost were not counted");
    }

    fn packet_blob(src: &NodeId, at: u64) -> Vec<u8> {
        let mut blob = Vec::new();
        encode(&mut blob, src, 3, at, b"held");
        blob
    }

    fn kept_mail(m: NodeId, blob: Vec<u8>) -> Kept {
        Kept {
            records: vec![],
            mailboxes: vec![(m, blob)],
        }
    }

    /// A blob with a trailer comes back as it was written: the packet, the mark with its own time, no write owed.
    #[test]
    fn a_blob_with_a_mark_round_trips() {
        let mut core = core();
        let (m, src) = (nid(1), nid(2));
        let (at, ts) = (T0 - 5 * SEC, 77);
        let mut blob = packet_blob(&src, T0 - SEC);
        encode_mark(&mut blob, at, ts);
        core.restore(T0, &kept_mail(m, blob.clone()));
        assert_eq!(core.sm.mailbox_pending(&m).0, 1);
        assert_eq!(core.sm.sleeper(&m), Some((at, ts)));
        assert!(core.next_job().is_none(), "a blob taken whole queues no write");
        core.note_mail(m);
        let Some(Job::Mail(n, again)) = core.next_job() else {
            panic!("no write");
        };
        assert_eq!((n, again), (m, blob));
        // a mark with no mail is the trailer alone
        let k = nid(3);
        let mut only = Vec::new();
        encode_mark(&mut only, at, ts);
        assert_eq!(only.len(), 18);
        core.restore(T0, &kept_mail(k, only.clone()));
        assert_eq!(core.sm.sleeper(&k), Some((at, ts)));
        assert!(core.next_job().is_none());
        core.note_mail(k);
        assert!(matches!(core.next_job(), Some(Job::Mail(n, b)) if n == k && b == only));
    }

    /// The old form restores its packets, derives the mark from the oldest and queues one write that carries it.
    #[test]
    fn an_old_form_blob_derives_its_mark_and_is_written_once() {
        let mut core = core();
        let (m, src) = (nid(1), nid(2));
        let mut blob = packet_blob(&src, T0 - 2 * SEC);
        blob.extend(packet_blob(&src, T0 - SEC));
        core.restore(T0, &kept_mail(m, blob));
        assert_eq!(core.sm.mailbox_pending(&m).0, 2);
        assert_eq!(core.sm.sleeper(&m), Some((T0 - 2 * SEC, u64::MAX)));
        let Some(Job::Mail(n, b)) = core.next_job() else {
            panic!("the upgrade write was not queued");
        };
        let mut want = packet_blob(&src, T0 - 2 * SEC);
        want.extend(packet_blob(&src, T0 - SEC));
        encode_mark(&mut want, T0 - 2 * SEC, u64::MAX);
        assert_eq!((n, b), (m, want));
        assert!(core.next_job().is_none(), "one write for the old blob");
        assert_eq!(core.counters.store_errors, 0);
    }

    /// A kept mark that ended takes the packets of its blob with it, and the blob is written empty.
    #[test]
    fn an_ended_kept_mark_drops_the_packets_and_forgets_the_blob() {
        let mut core = core();
        let (m, src) = (nid(1), nid(2));
        let day = Limits::default().mailbox_max_age_ns;
        let now = T0 + day;
        let mut blob = packet_blob(&src, now - SEC);
        encode_mark(&mut blob, T0, 9);
        core.restore(now, &kept_mail(m, blob));
        assert_eq!(core.sm.mailbox_pending(&m).0, 0);
        assert_eq!(core.sm.sleeper(&m), None);
        assert!(matches!(core.next_job(), Some(Job::Mail(n, b)) if n == m && b.is_empty()));
        assert_eq!(core.counters.store_errors, 0);
    }

    /// A remainder that is no trailer (a newer version, a torn trailer, a torn packet) is counted once, and the packets
    /// before it are restored with a derived mark.
    #[test]
    fn a_garbled_remainder_is_counted_once_and_the_packets_before_it_are_kept() {
        let src = nid(2);
        let junk: [&[u8]; 3] = [&[0, 2, 1, 2, 3], &[0, 1, 1, 2, 3], &[1, 9, 9, 9]];
        for (i, tail) in junk.iter().enumerate() {
            let mut core = core();
            let m = nid(10 + u16::try_from(i).unwrap());
            let mut blob = packet_blob(&src, T0 - SEC);
            blob.extend_from_slice(tail);
            core.restore(T0, &kept_mail(m, blob));
            assert_eq!(core.counters.store_errors, 1, "remainder {i}");
            assert_eq!(core.sm.mailbox_pending(&m).0, 1, "remainder {i}");
            assert_eq!(core.sm.sleeper(&m), Some((T0 - SEC, u64::MAX)), "remainder {i}");
            assert!(
                matches!(core.next_job(), Some(Job::Mail(..))),
                "rewritten clean, remainder {i}"
            );
        }
    }

    /// A mark write the store refuses is tried again after the wait and counted; the blob it writes is the mark alone.
    #[test]
    fn a_failed_mark_write_is_retried_and_counted() {
        let mut core = core();
        let m = nid(1);
        core.sm.restore_sleep(T0, &m, T0, 5).unwrap();
        core.note_mail(m);
        core.on_timeout(T0);
        let Some(job) = core.next_write() else {
            panic!("no write");
        };
        let Job::Mail(_, first) = &job else {
            panic!("not a mail write");
        };
        assert_eq!(first.len(), 18);
        core.written(false);
        assert_eq!(core.counters.store_errors, 1);
        assert!(core.next_write().is_none(), "not before the wait");
        core.on_timeout(T0 + RETRY_NS + SEC);
        assert!(matches!(core.next_write(), Some(Job::Mail(n, b)) if n == m && b.len() == 18));
    }

    /// An accepted notice and the return of the member each queue one write; a copy of the notice queues none.
    #[test]
    fn a_notice_and_a_return_queue_one_write_each_and_a_copy_none() {
        use pinc_connect::relay::sleep;

        let mut core = core();
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[5; 32]).unwrap();
        let m = kp.node_id();
        let now = T0 + SEC;
        core.sm.carrier_opened(now, m, &mut core.fx).unwrap();
        core.flush();
        assert!(core.next_job().is_none());
        let mut buf = [0u8; sleep::MAX_LEN];
        let n = sleep::sign(&kp, &core.node_id(), now / 1_000_000, &mut buf).unwrap();
        core.sm.sleep_notice(now, &buf[..n], None, &mut core.fx).unwrap();
        core.flush();
        assert!(matches!(core.next_job(), Some(Job::Mail(n, b)) if n == m && b.len() == 18));
        assert!(core.next_job().is_none());
        core.sm.sleep_notice(now + SEC, &buf[..n], None, &mut core.fx).unwrap();
        core.flush();
        assert!(core.next_job().is_none(), "a copy writes nothing");
        core.sm.member_returned(now + 2 * SEC, &m, &mut core.fx);
        core.flush();
        assert!(matches!(core.next_job(), Some(Job::Mail(n, b)) if n == m && b.is_empty()));
        assert!(core.next_job().is_none());
    }

    /// N sleeping clients cost N store writes (one 18-byte mark each), a repeat of every notice costs none, and the
    /// return of all N costs N more.
    #[test]
    fn n_sleeping_clients_cost_n_writes_and_their_copies_none() {
        use pinc_connect::relay::sleep;

        let mut core = core();
        let now = T0 + SEC;
        let kps: Vec<_> = (1..=8u8)
            .map(|i| Keypair::from_seed(IdentityAlg::Ed25519, &[i + 40; 32]).unwrap())
            .collect();
        let mut writes = 0;
        for kp in &kps {
            core.sm.carrier_opened(now, kp.node_id(), &mut core.fx).unwrap();
            let mut buf = [0u8; sleep::MAX_LEN];
            let n = sleep::sign(kp, &core.node_id(), now / 1_000_000, &mut buf).unwrap();
            core.sm.sleep_notice(now, &buf[..n], None, &mut core.fx).unwrap();
            core.flush();
            while core.next_job().is_some() {
                writes += 1;
            }
            // the copies come after the first write was drained: a copy that traced again would queue another
            let mut copies = 0;
            for _ in 0..2 {
                core.sm.sleep_notice(now, &buf[..n], None, &mut core.fx).unwrap();
            }
            core.flush();
            while core.next_job().is_some() {
                copies += 1;
            }
            assert_eq!(copies, 0, "a copy of a notice wrote the store");
        }
        assert_eq!(writes, kps.len());
        for kp in &kps {
            core.sm.member_returned(now + SEC, &kp.node_id(), &mut core.fx);
        }
        core.flush();
        while core.next_job().is_some() {
            writes += 1;
        }
        assert_eq!(writes, 2 * kps.len());
    }

    type Disk = BTreeMap<[u8; 33], (NodeId, Vec<u8>)>;

    /// The store as the writes leave it: the last blob written per member, an empty one removing the member.
    fn apply(store: &mut Disk, core: &mut Core<(), SoftwareStore, AllowAll>) {
        while let Some(Job::Mail(n, blob)) = core.next_job() {
            if blob.is_empty() {
                store.remove(&node_key(&n));
            } else {
                store.insert(node_key(&n), (n, blob));
            }
        }
    }

    fn kept_of(store: &Disk) -> Kept {
        Kept {
            records: vec![],
            mailboxes: store.values().cloned().collect(),
        }
    }

    /// A mark a new notice evicts leaves the store with it: after a restart the member is not asleep.
    #[test]
    fn an_evicted_mark_does_not_come_back_after_a_restart() {
        let mut core = core();
        let mut store = BTreeMap::new();
        let now = T0 + 2000 * SEC;
        let mut only = Vec::new();
        for i in 0..CARRIERS {
            only.clear();
            encode_mark(&mut only, T0 + u64::try_from(i).unwrap() * SEC, 1);
            store.insert(
                node_key(&nid(u16::try_from(i).unwrap())),
                (nid(u16::try_from(i).unwrap()), only.clone()),
            );
        }
        core.restore(now, &kept_of(&store));
        assert!(core.next_job().is_none(), "marks taken whole queue no write");
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[5; 32]).unwrap();
        core.sm.carrier_opened(now, kp.node_id(), &mut core.fx).unwrap();
        core.flush();
        let mut buf = [0u8; pinc_connect::relay::sleep::MAX_LEN];
        let n = pinc_connect::relay::sleep::sign(&kp, &core.node_id(), now / 1_000_000, &mut buf).unwrap();
        core.sm.sleep_notice(now, &buf[..n], None, &mut core.fx).unwrap();
        core.flush();
        assert_eq!(core.sm.stats().marks_evicted, 1);
        apply(&mut store, &mut core);
        assert!(
            !store.contains_key(&node_key(&nid(0))),
            "the evicted mark is still in the store"
        );
        assert!(store.contains_key(&node_key(&kp.node_id())));
        let mut again = self::core();
        again.restore(now, &kept_of(&store));
        assert_eq!(again.sm.sleeper(&nid(0)), None);
        assert!(again.sm.sleeper(&nid(1)).is_some() && again.sm.sleeper(&kp.node_id()).is_some());
        assert_eq!(again.counters.store_errors, 0);
    }

    /// A store with more live marks than the table has room for keeps the members that hold mail before the bare
    /// marks, whatever the store's order: the bare marks left out are counted once each, and once the writes are done
    /// the store keeps exactly the marks the table holds.
    #[test]
    fn a_store_with_more_marks_than_the_table_keeps_the_members_with_mail() {
        let mut core = core();
        let mut store = BTreeMap::new();
        let src = nid(60_000);
        let mut with_mail = packet_blob(&src, T0 - SEC);
        with_mail.extend(packet_blob(&src, T0));
        let extra = 2;
        let last = nid(u16::try_from(CARRIERS + 1).unwrap());
        for i in 0..CARRIERS + extra {
            let m = nid(u16::try_from(i).unwrap());
            let mut blob = Vec::new();
            if m == last {
                blob.clone_from(&with_mail);
            } else {
                encode_mark(&mut blob, T0 - SEC, 1);
            }
            store.insert(node_key(&m), (m, blob));
        }
        // the member with mail comes last in the store's order, and the bare marks fill the rest of the table
        core.restore(T0, &kept_of(&store));
        assert_eq!(core.counters.store_errors, 2, "each bare mark left out is counted once");
        let held = (0..CARRIERS + extra)
            .filter(|i| core.sm.sleeper(&nid(u16::try_from(*i).unwrap())).is_some())
            .count();
        assert_eq!(held, CARRIERS);
        assert_eq!(
            core.sm.mailbox_pending(&last).0,
            2,
            "the member with mail lost its packets"
        );
        assert!(core.sm.sleeper(&last).is_some(), "the member with mail lost its mark");
        apply(&mut store, &mut core);
        assert_eq!(store.len(), CARRIERS, "the store keeps what the table does not hold");
        assert!(store.contains_key(&node_key(&last)));
        let mut again = self::core();
        again.restore(T0, &kept_of(&store));
        assert_eq!(again.counters.store_errors, 0);
        assert_eq!(again.sm.mailbox_pending(&last).0, 2);
        assert!(again.next_job().is_none());
    }

    /// A mark the restore moved back to the clock is written again: the store does not keep a time ahead of it.
    #[test]
    fn a_mark_the_restore_clamped_is_written_back() {
        let mut core = core();
        let (m, src) = (nid(1), nid(2));
        let (ahead, ts) = (T0 + 5 * SEC, 77);
        let mut blob = packet_blob(&src, T0);
        encode_mark(&mut blob, ahead, ts);
        core.restore(T0, &kept_mail(m, blob));
        assert_eq!(core.sm.sleeper(&m), Some((T0, ts)));
        let Some(Job::Mail(n, written)) = core.next_job() else {
            panic!("the clamped mark was not written back");
        };
        assert_eq!(n, m);
        let mut tail = Vec::new();
        encode_mark(&mut tail, T0, ts);
        assert!(
            written.ends_with(&tail),
            "the store keeps the mark's time ahead of the clock"
        );
        assert!(core.next_job().is_none(), "one write");
    }

    /// N members' writes go out in the order they were marked, oldest first.
    #[test]
    fn mailbox_writes_go_out_in_the_order_they_were_queued() {
        let mut core = core();
        let members: Vec<NodeId> = (0..9).map(nid).collect();
        for m in &members {
            core.sm.restore_sleep(T0, m, T0, 5).unwrap();
            core.note_mail(*m);
        }
        let mut out = Vec::new();
        while let Some(Job::Mail(n, _)) = core.next_job() {
            out.push(n);
        }
        assert_eq!(out, members);
    }

    /// A notice that evicts the oldest mark of a full table writes the evicted member's removal before its own mark,
    /// so a crash between the two leaves the store no more live marks than the table holds.
    #[test]
    fn an_eviction_is_written_before_the_mark_that_caused_it() {
        let mut core = core();
        let mut store = BTreeMap::new();
        let now = T0 + 2000 * SEC;
        let mut only = Vec::new();
        for i in 0..CARRIERS {
            only.clear();
            encode_mark(&mut only, T0 + u64::try_from(i).unwrap() * SEC, 1);
            let m = nid(u16::try_from(i).unwrap());
            store.insert(node_key(&m), (m, only.clone()));
        }
        core.restore(now, &kept_of(&store));
        let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[5; 32]).unwrap();
        core.sm.carrier_opened(now, kp.node_id(), &mut core.fx).unwrap();
        core.flush();
        let mut buf = [0u8; pinc_connect::relay::sleep::MAX_LEN];
        let n = pinc_connect::relay::sleep::sign(&kp, &core.node_id(), now / 1_000_000, &mut buf).unwrap();
        core.sm.sleep_notice(now, &buf[..n], None, &mut core.fx).unwrap();
        core.flush();
        assert_eq!(core.sm.stats().marks_evicted, 1);
        let Some(Job::Mail(first, blob)) = core.next_job() else {
            panic!("no write");
        };
        assert_eq!(
            (first, blob.is_empty()),
            (nid(0), true),
            "the evicted member's delete goes first"
        );
        assert!(matches!(core.next_job(), Some(Job::Mail(n, b)) if n == kp.node_id() && b.len() == 18));
        // the crash: only the first write reached the store
        store.remove(&node_key(&first));
        let mut again = self::core();
        again.restore(now, &kept_of(&store));
        assert_eq!(
            again.counters.store_errors, 0,
            "the store held more marks than the table"
        );
        assert_eq!(store.len(), CARRIERS - 1);
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

    /// The machine takes the first `RECORDS` records the store gives (its table refuses the next ones, it evicts none),
    /// so `held` is exactly the machine's records and each other record of the store is owed a removal.
    #[test]
    fn a_store_that_kept_more_records_than_the_table_is_restored_within_the_table() {
        let mut core = core();
        let home = core.node_id();
        let extra = 40;
        let mut kept = Kept::default();
        let mut nodes = Vec::new();
        for i in 0..u16::try_from(RECORDS + extra).unwrap() {
            let (n, rec) = signed(i, home);
            nodes.push(n);
            kept.records.push(KeptRecord {
                bytes: rec,
                received: T0,
            });
        }
        core.restore(T0, &kept);
        assert_eq!(
            core.sm.record_count(),
            RECORDS,
            "the machine passed or missed its table"
        );
        assert_eq!(core.keep.held.len(), RECORDS);
        assert_eq!(core.keep.removed.len(), extra);
        assert!(
            core.keep.records.is_empty(),
            "a restored record is marked to be written"
        );
        assert!(core.keep.failed.len() <= FAILED);
        assert_eq!(
            core.counters.store_errors, 0,
            "the marks had room and nothing was counted"
        );
        for (i, n) in nodes.iter().enumerate() {
            let key = node_key(n);
            assert_eq!(
                core.sm.record_received(n).is_some(),
                i < RECORDS,
                "record {i} held wrongly"
            );
            assert_eq!(
                core.keep.held.contains_key(&key),
                i < RECORDS,
                "record {i} kept wrongly"
            );
            assert_eq!(
                core.keep.removed.contains_key(&key),
                i >= RECORDS,
                "record {i} owed wrongly"
            );
        }
    }

    /// A removal the store refuses `MAX_TRIES` times is given up and counted once per try and once more, and the retry
    /// is offered behind a record marked meanwhile.
    #[test]
    fn a_removal_the_store_refuses_is_given_up_after_its_tries_and_counted() {
        let mut core = core();
        let home = core.node_id();
        let (gone, _) = signed(1, home);
        let (other, rec) = signed(2, home);
        assert!(Keep::mark_removed(&mut core.keep.removed, gone));
        let errs = core.counters.store_errors;
        let mut now = T0;
        core.on_timeout(now);
        assert!(matches!(core.next_job(), Some(Job::Remove(n)) if n == gone));
        for tried in 1..=MAX_TRIES {
            core.write_failed(Mark::Remove(gone), now);
            now += RETRY_NS;
            core.on_timeout(now);
            if tried == 1 {
                core.sm.restore_record(now, &rec, &mut core.fx).unwrap();
                core.flush();
                assert!(
                    matches!(core.next_job(), Some(Job::Put(n, ..)) if n == other),
                    "the retry was offered before a mark not tried yet"
                );
            }
            if tried < MAX_TRIES {
                assert!(
                    matches!(core.next_job(), Some(Job::Remove(n)) if n == gone),
                    "try {tried}"
                );
            }
        }
        assert!(core.next_job().is_none(), "the removal is still offered");
        assert!(core.keep.failed.is_empty() && core.keep.removed.is_empty());
        assert_eq!(core.counters.store_errors - errs, u64::from(MAX_TRIES) + 1);
    }
}
