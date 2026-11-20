//! What the relay keeps across a restart, and the work of keeping it: the records of the store and the packets held
//! for sleeping members.
//!
//! Every change the machine reports (a record stored, a packet held or handed over) marks a node; the run loop takes
//! one job at a time and writes it through the [`Store`](super::super::store::Store). A record the machine dropped by
//! lifetime is removed from the store; a record and a packet come back with the time they arrived, so what is left of
//! their lifetime is the same after a restart.
//!
//! Invariants: the nodes marked are bounded by the record table and the mailbox member table; a packet is written
//! with its arrival time and restored oldest first; nothing past its lifetime is restored.

use alloc::vec::Vec;

use pinc_connect::carrier::NODE_ID_LEN;
use pinc_connect::carrier::frame::MAX_PACKET_LEN;
use pinc_connect::record::Record;
use pinc_connect::relay::rule::RECORD_TTL_NS;
use pinc_crypto::{IdentityAlg, NodeId};

use super::Core;
use crate::relay::access::Access;
use crate::relay::limits::MAILBOX_MEMBERS;
use crate::relay::store::Kept;
use pinc_keystore::KeyStore;

/// The nodes whose state is waiting to be written to the store.
#[derive(Debug, Default)]
pub(super) struct Keep {
    /// Records stored and not yet written.
    records: Vec<NodeId>,
    /// Records the store holds and the machine may have dropped.
    held: Vec<NodeId>,
    /// Records to remove from the store.
    removed: Vec<NodeId>,
    /// Members whose held packets changed.
    mail: Vec<NodeId>,
    /// The records the machine held at the last sweep.
    count: usize,
    /// Restoring: the machine reports what it restores, which is already in the store.
    restoring: bool,
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
        if !self.keep.records.contains(&node) {
            self.keep.records.push(node);
        }
        if !self.keep.held.contains(&node) {
            self.keep.held.push(node);
        }
    }

    /// A packet was held for `node` or handed to it: write what is held.
    pub(super) fn note_mail(&mut self, node: NodeId) {
        if !self.keep.restoring && !self.keep.mail.contains(&node) && self.keep.mail.len() < 4 * MAILBOX_MEMBERS {
            self.keep.mail.push(node);
        }
    }

    /// The machine ran its timers: a record it dropped by lifetime is removed from the store.
    pub(super) fn note_sweep(&mut self) {
        let count = self.sm.record_count();
        if count >= self.keep.count {
            self.keep.count = count;
            return;
        }
        self.keep.count = count;
        let Self { sm, keep, .. } = self;
        let (alive, gone): (Vec<NodeId>, Vec<NodeId>) =
            keep.held.drain(..).partition(|n| sm.record_received(n).is_some());
        keep.held = alive;
        for n in gone {
            keep.records.retain(|r| *r != n);
            keep.removed.push(n);
        }
    }

    /// The next write to the store, if any.
    pub(crate) fn next_job(&mut self) -> Option<Job> {
        if let Some(n) = self.keep.removed.pop() {
            return Some(Job::Remove(n));
        }
        while let Some(n) = self.keep.records.pop() {
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
                (true, Some(n)) => self.keep.held.push(n),
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
        self.keep.count = self.sm.record_count();
        self.keep.restoring = false;
    }
}
