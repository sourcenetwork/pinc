//! The record store and the relay rules around it (rendezvous, CMP-CON-04).
//!
//! A record reaches the store in three ways: a node publishes its own on its carrier, a peer relay replicates one over
//! an authenticated session, or the relay installs its own. Each way checks the signature and the key to node id
//! binding first, so the store holds only records that verified, byte for byte as published. A higher sequence number
//! replaces a lower one; a lower or conflicting one is refused. The relay's own record is sent to every peer relay
//! again every [`super::rule::RECORD_REPUBLISH_NS`], and a record not refreshed within [`super::rule::RECORD_TTL_NS`]
//! is dropped by the sweep.
//!
//! Invariants: the store never holds more than `R` records; a slot holds the record bytes inline; a replica is never
//! replicated again; a lookup answers only with a fresh stored record, and the node that asked verifies the
//! signature itself ([`crate::record::Record::parse_verified`]), so a relay is not trusted to vouch for a record.

use vinc_crypto::NodeId;

use super::table::Table;
use super::{Effect, RecordOrigin, Reject, Relay, Sink, Trace, rule};
use crate::carrier::frame::{DnsAnswer, Frame};
use crate::record::{MAX_RECORD_LEN, Record};

// vertexia: fixed slots of MAX_RECORD_LEN, an arena sized by the bytes actually held if memory per record matters
// (an Ed25519 record fills about a tenth of its slot)
pub(crate) struct Stored {
    pub(crate) seq: u64,
    pub(crate) received: u64,
    pub(crate) home: NodeId,
    len: usize,
    bytes: [u8; MAX_RECORD_LEN],
}

impl Stored {
    pub(crate) fn bytes(&self) -> &[u8] {
        self.bytes.get(..self.len).unwrap_or_default()
    }
}

impl core::fmt::Debug for Stored {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Stored").field("seq", &self.seq).finish_non_exhaustive()
    }
}

/// A bounded table of verified records.
#[derive(Debug)]
pub struct RecordStore<const R: usize> {
    table: Table<Stored, R>,
}

enum Accepted {
    Stored,
    Refreshed,
}

impl<const R: usize> RecordStore<R> {
    pub(crate) fn new(seed: u64) -> Self {
        Self {
            table: Table::new(seed),
        }
    }

    pub(crate) const fn len(&self) -> usize {
        self.table.len()
    }

    pub(crate) fn get(&self, node: &NodeId) -> Option<&Stored> {
        self.table.get(node)
    }

    fn accept(&mut self, now: u64, rec: &Record<'_>, bytes: &[u8]) -> Result<Accepted, Reject> {
        if let Some(s) = self.table.get_mut(&rec.node) {
            if rec.seq < s.seq || (rec.seq == s.seq && s.bytes() != bytes) {
                return Err(Reject::StaleRecord);
            }
            if rec.seq == s.seq {
                s.received = now;
                return Ok(Accepted::Refreshed);
            }
        }
        let mut stored = Stored {
            seq: rec.seq,
            received: now,
            home: rec.home,
            len: bytes.len(),
            bytes: [0; MAX_RECORD_LEN],
        };
        stored
            .bytes
            .get_mut(..bytes.len())
            .ok_or(Reject::BadRecord(crate::record::RecordError::Trailing))?
            .copy_from_slice(bytes);
        self.table
            .insert(rec.node, stored)
            .map(|_| Accepted::Stored)
            .map_err(|_| Reject::StoreFull)
    }

    pub(crate) fn sweep(&mut self, now: u64) {
        self.table
            .retain(|_, s| now.saturating_sub(s.received) < rule::RECORD_TTL_NS);
    }
}

impl<const C: usize, const R: usize, const MN: usize, const MB: usize> Relay<C, R, MN, MB> {
    fn store<S: Sink>(
        &mut self,
        now: u64,
        bytes: &[u8],
        origin: RecordOrigin,
        owner: Option<&NodeId>,
        sink: &mut S,
    ) -> Result<(), Reject> {
        let rec = Record::parse_verified(bytes).map_err(|e| self.reject(sink, Reject::BadRecord(e), owner.copied()))?;
        if owner.is_some_and(|o| *o != rec.node) {
            return Err(self.reject(sink, Reject::WrongOwner, owner.copied()));
        }
        match self.records.accept(now, &rec, bytes) {
            Ok(Accepted::Stored) => {
                self.stats.records += 1;
                sink.emit(Effect::Trace(Trace::RecordStored {
                    node: rec.node,
                    seq: rec.seq,
                    origin,
                }));
            }
            Ok(Accepted::Refreshed) => {}
            Err(why) => return Err(self.reject(sink, why, Some(rec.node))),
        }
        Ok(())
    }

    fn replicate<S: Sink>(&self, bytes: &[u8], sink: &mut S) -> usize {
        let mut n = 0;
        for peer in self.peers.iter().flatten() {
            sink.emit(Effect::PeerRelay {
                to: *peer,
                frame: Frame::Sync { record: bytes },
            });
            n += 1;
        }
        n
    }

    /// A node published its record on its carrier: verify it, store it and replicate it to every peer relay.
    ///
    /// # Errors
    /// [`Reject::BadRecord`], [`Reject::WrongOwner`], [`Reject::StaleRecord`] or [`Reject::StoreFull`].
    pub(crate) fn publish<S: Sink>(
        &mut self,
        now: u64,
        node: &NodeId,
        bytes: &[u8],
        sink: &mut S,
    ) -> Result<(), Reject> {
        self.store(now, bytes, RecordOrigin::Publish, Some(node), sink)?;
        self.replicate(bytes, sink);
        Ok(())
    }

    /// A peer relay replicated a record: verify it and store it. It is not replicated again.
    pub(crate) fn replica<S: Sink>(&mut self, now: u64, bytes: &[u8], sink: &mut S) -> Result<(), Reject> {
        self.store(now, bytes, RecordOrigin::Replica, None, sink)
    }

    /// Install a record this relay stored before a restart, received at `received`: it ends
    /// [`super::rule::RECORD_TTL_NS`] after that, not after the restart. It is verified like a replica and not
    /// replicated again. The host does not restore a record that has expired.
    ///
    /// # Errors
    /// [`Reject::BadRecord`], [`Reject::StaleRecord`] or [`Reject::StoreFull`].
    pub fn restore_record<S: Sink>(&mut self, received: u64, bytes: &[u8], sink: &mut S) -> Result<(), Reject> {
        self.replica(received, bytes, sink)
    }

    /// Install this relay's own signed record, send it to every peer relay and arm the republish timer.
    ///
    /// # Errors
    /// [`Reject::WrongOwner`] if the record is not this relay's, otherwise as for a published record.
    pub fn set_own_record<S: Sink>(&mut self, now: u64, bytes: &[u8], sink: &mut S) -> Result<(), Reject> {
        let me = self.cfg.me;
        self.store(now, bytes, RecordOrigin::Own, Some(&me), sink)?;
        self.replicate(bytes, sink);
        self.next_publish = now.saturating_add(rule::RECORD_REPUBLISH_NS);
        Ok(())
    }

    pub(crate) fn republish_due<S: Sink>(&mut self, now: u64, sink: &mut S) {
        if self.next_publish == 0 || now < self.next_publish {
            return;
        }
        self.next_publish = now.saturating_add(rule::RECORD_REPUBLISH_NS);
        let me = self.cfg.me;
        let Some(s) = self.records.table.get_mut(&me) else {
            return;
        };
        s.received = now;
        let mut peers = 0;
        for peer in self.peers.iter().flatten() {
            sink.emit(Effect::PeerRelay {
                to: *peer,
                frame: Frame::Sync { record: s.bytes() },
            });
            peers += 1;
        }
        sink.emit(Effect::Trace(Trace::Republished { peers }));
    }

    /// The nodes whose record is stored.
    pub fn record_nodes(&self) -> impl Iterator<Item = NodeId> + '_ {
        self.records.table.iter().map(|(k, _)| *k)
    }

    /// Send the stored record of `node` to the peer relay `to` as a replica, if the record is homed at this relay and
    /// `to` is an authenticated peer. A host calls it for [`Relay::record_nodes`] when a session with a peer relay
    /// comes up, so a relay that joined late or restarted learns the records it missed; a record homed elsewhere is
    /// that relay's to send. Returns whether a frame was emitted.
    pub fn sync_record<S: Sink>(&self, to: &NodeId, node: &NodeId, sink: &mut S) -> bool {
        let me = self.cfg.me;
        let Some(s) = self.records.get(node).filter(|s| s.home == me && self.is_peer(to)) else {
            return false;
        };
        sink.emit(Effect::PeerRelay {
            to: *to,
            frame: Frame::Sync { record: s.bytes() },
        });
        true
    }

    /// The stored record of `peer` if it is fresh.
    pub fn lookup(&self, now: u64, peer: &NodeId) -> Option<&[u8]> {
        self.records
            .get(peer)
            .filter(|s| now.saturating_sub(s.received) < rule::RECORD_TTL_NS)
            .map(Stored::bytes)
    }

    /// The answer to a lookup of `peer`; a record longer than `max` is [`DnsAnswer::TooLarge`].
    pub(crate) fn answer<S: Sink>(&mut self, now: u64, peer: &NodeId, max: usize, sink: &mut S) -> DnsAnswer<'_> {
        self.stats.lookups += 1;
        let found = self.lookup(now, peer).is_some();
        sink.emit(Effect::Trace(Trace::LookupServed { peer: *peer, found }));
        match self.lookup(now, peer) {
            None => DnsAnswer::Absent,
            Some(rec) if rec.len() > max => DnsAnswer::TooLarge,
            Some(rec) => DnsAnswer::Record(rec),
        }
    }
}
