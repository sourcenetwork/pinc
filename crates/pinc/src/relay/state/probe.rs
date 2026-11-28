//! A relay core with no carriers, for the trace test of what a node that carries the relay role keeps across a restart.
//!
//! Everything here calls the machine and the core the way `keep.rs` does and reads what they hold; nothing changes the
//! behaviour of either. Invariant: the probe is the only way the trace test reaches the core's private state.

use alloc::rc::Rc;
use alloc::vec::Vec;
use core::cell::RefCell;

use pinc_connect::carrier::frame::MAX_PACKET_LEN;
use pinc_connect::record::Record;
use pinc_crypto::NodeId;
use pinc_keystore::SoftwareStore;

use super::Core;
use crate::keys::Identity;
use crate::relay::access::AllowAll;
use crate::relay::limits::Limits;
use crate::relay::store::Kept;

/// A relay core with no carriers, for the trace test of what the role keeps.
pub struct KeepProbe {
    core: Core<(), SoftwareStore, AllowAll>,
}

/// A store write the core asks for.
pub enum KeepJob {
    /// Keep a record and the time it was received.
    Put {
        /// The publisher.
        node: NodeId,
        /// The signed record.
        record: Vec<u8>,
        /// When it was received.
        received: u64,
    },
    /// Forget a record.
    Remove(NodeId),
    /// Keep the packets held for a member (empty: none are held).
    Mail {
        /// The member.
        node: NodeId,
        /// The encoded packets.
        blob: Vec<u8>,
    },
}

impl KeepProbe {
    /// A core with a hub, a record lifetime of four units of 1.35e12 ns and a mailbox age of three, started at `now`.
    ///
    /// # Errors
    /// The core's own errors.
    pub fn new(now: u64) -> crate::Result<Self> {
        let identity = Rc::new(RefCell::new(Identity::from_seed_with(&[7; 32], &[0; 32])?));
        let limits = Limits {
            mailbox_max_age_ns: 4_050_000_000_000,
            ..Limits::default()
        };
        let tunnel = "192.0.2.1:4000".parse().ok();
        Ok(Self {
            core: Core::new(identity, AllowAll, &[], limits, tunnel, now)?,
        })
    }

    /// The node id of the core.
    pub fn node_id(&self) -> NodeId {
        self.core.identity.borrow().node_id()
    }

    /// A record published at `now`: the machine call `restore` makes for a kept record, received at `now`. Whether the
    /// machine took it.
    pub fn publish(&mut self, now: u64, record: &[u8]) -> bool {
        let ok = {
            let Core { sm, fx, .. } = &mut self.core;
            sm.restore_record(now, record, fx).is_ok()
        };
        self.core.flush();
        ok
    }

    /// A packet held for `node` at `now`. Whether the machine took it.
    pub fn hold(&mut self, now: u64, node: &NodeId, src: &NodeId, flag: u8, body: &[u8]) -> bool {
        let ok = self.core.sm.restore_held(now, now, node, src, flag, body).is_ok();
        if ok {
            self.core.note_mail(*node);
        }
        self.core.flush();
        ok
    }

    /// The member's direct session was heard at `now`.
    pub fn heard(&mut self, now: u64, node: &NodeId) {
        self.core.on_heard(now, Some(*node));
    }

    /// Run the timers at `now`.
    pub fn tick(&mut self, now: u64) {
        self.core.on_timeout(now);
    }

    /// The next write the core asks for; none while one is out.
    pub fn next_job(&mut self) -> Option<KeepJob> {
        Some(match self.core.next_write()? {
            super::Job::Put(node, record, received) => KeepJob::Put { node, record, received },
            super::Job::Remove(n) => KeepJob::Remove(n),
            super::Job::Mail(node, blob) => KeepJob::Mail { node, blob },
        })
    }

    /// Put back what the store kept, at `now`; nothing once it ran, as in [`crate::relay::Part::restore`].
    pub fn restore(&mut self, now: u64, kept: &Kept) {
        self.core.restore_once(now, kept);
    }

    /// Whether [`KeepProbe::restore`] ran.
    pub fn restored(&self) -> bool {
        self.core.restored()
    }

    /// The write taken last finished, `ok` if the store kept it, as in [`crate::relay::Part::store_written`].
    pub fn written(&mut self, ok: bool) {
        self.core.written(ok);
    }

    /// The run ends: the write out is given back, as in [`crate::relay::Part::end`].
    pub fn end(&mut self) {
        self.core.end_run();
    }

    /// The sequence number and the time received of the record held for `node`, whether or not past its lifetime.
    pub fn record(&self, node: &NodeId) -> Option<(u64, u64)> {
        let received = self.core.sm.record_received(node)?;
        let bytes = self.core.sm.lookup(received, node)?;
        Some((Record::parse(bytes).ok()?.seq, received))
    }

    /// The packets held for `node`, oldest first: the time each arrived and its body.
    pub fn held(&self, node: &NodeId) -> Vec<(u64, Vec<u8>)> {
        let mut buf = [0u8; MAX_PACKET_LEN];
        let mut out = Vec::new();
        let mut i = 0;
        while let Some((d, at)) = self.core.sm.held_packet(node, i, &mut buf) {
            out.push((at, buf.get(..d.len).unwrap_or_default().to_vec()));
            i += 1;
        }
        out
    }

    /// The time the sleep mark of `node` was set and the clock of the notice that set it, if it has one.
    pub fn sleeper(&self, node: &NodeId) -> Option<(u64, u64)> {
        self.core.sm.sleeper(node)
    }

    /// How many records the machine holds.
    pub fn record_count(&self) -> usize {
        self.core.sm.record_count()
    }

    /// The store errors counted.
    pub fn store_errors(&self) -> u64 {
        self.core.counters.store_errors
    }

    /// The datagrams and hub packets dropped.
    pub fn dropped(&self) -> u64 {
        self.core.counters.datagrams_dropped + self.core.counters.hub_dropped
    }
}
