//! The host of a membership world node: records everything the machines ask of the session, broadcast and local
//! layers.
//!
//! Included by `membership_world.rs`; not a test target itself.
#![allow(
    dead_code,
    unreachable_pub,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

use std::collections::{BTreeMap, BTreeSet};

use vinc_membership::session::StoreError;
use vinc_membership::{Broadcast, Carrier, CloseReason, Evidence, Local, NodeId, Route, Session};

pub const MS: u64 = 1_000_000;
pub const SEC: u64 = 1_000_000_000;

pub fn id(i: usize) -> NodeId {
    [u8::try_from(i + 1).unwrap(); 32]
}

/// What the machines asked of the broadcast layer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Bc {
    Frame(NodeId, u8, Vec<u8>, Vec<u8>),
    Hold(NodeId),
    Restore(NodeId),
    Release(NodeId),
    Resub(NodeId),
    Primary(Option<NodeId>, NodeId),
}

#[derive(Debug, Default)]
pub struct Host {
    pub me: NodeId,
    pub out: Vec<(NodeId, Route, Vec<u8>)>,
    pub sessions: BTreeSet<NodeId>,
    pub ev: BTreeMap<NodeId, Evidence>,
    pub carriers: BTreeMap<NodeId, Carrier>,
    pub bc: Vec<Bc>,
    pub closed: Vec<(NodeId, CloseReason)>,
    pub version: u16,
    pub ticket: u8,
    pub reflexive: bool,
    pub persistent: bool,
    pub sealed: Option<u64>,
    pub fail_seal: bool,
    pub fail_unseal: bool,
    /// The transport's give-up bound per peer; a peer not listed has the default.
    pub gu: BTreeMap<NodeId, u64>,
    /// Every `send` the machine made, with whether a session took it (for the proof traces).
    pub sent_log: Vec<(NodeId, Route, Vec<u8>, bool)>,
}

impl Session for Host {
    fn send(&mut self, peer: &NodeId, route: Route, frame: &[u8]) -> bool {
        let ok = self.sessions.contains(peer);
        self.sent_log.push((*peer, route, frame.to_vec(), ok));
        if !ok {
            return false;
        }
        self.out.push((*peer, route, frame.to_vec()));
        true
    }
    fn evidence(&self, peer: &NodeId) -> Option<Evidence> {
        self.ev.get(peer).copied()
    }
    fn carrier(&self, member: &NodeId) -> Carrier {
        self.carriers.get(member).copied().unwrap_or_default()
    }
    fn give_up(&self, peer: &NodeId) -> u64 {
        self.gu
            .get(peer)
            .copied()
            .unwrap_or(vinc_membership::consts::HEAL_SILENCE)
    }
    fn close(&mut self, peer: &NodeId, reason: CloseReason) {
        self.closed.push((*peer, reason));
    }
}

impl Broadcast for Host {
    fn floor(&mut self, member: &NodeId, out: &mut [u8]) -> usize {
        out[..9].copy_from_slice(&[0xF1, member[0], 0, 0, 0, 0, 0, 0, 1]);
        9
    }
    fn frame(&mut self, from: &NodeId, ty: u8, topic: &[u8], rest: &[u8]) {
        self.bc.push(Bc::Frame(*from, ty, topic.to_vec(), rest.to_vec()));
    }
    fn hold(&mut self, member: &NodeId) {
        self.bc.push(Bc::Hold(*member));
    }
    fn restore(&mut self, member: &NodeId) {
        self.bc.push(Bc::Restore(*member));
    }
    fn release(&mut self, member: &NodeId) {
        self.bc.push(Bc::Release(*member));
    }
    fn resubscribe(&mut self, hub: &NodeId) {
        self.bc.push(Bc::Resub(*hub));
    }
    fn primary_changed(&mut self, old: Option<&NodeId>, new: &NodeId) {
        self.bc.push(Bc::Primary(old.copied(), *new));
    }
}

impl Local for Host {
    fn version(&self) -> u16 {
        self.version
    }
    fn reflexive_known(&self) -> bool {
        self.reflexive
    }
    fn address_hash(&self, moves: u8) -> [u8; 8] {
        [self.ticket, moves, 0, 0, 0, 0, 0, 7]
    }
    fn persistent(&self) -> bool {
        self.persistent
    }
    fn unseal_counter(&mut self) -> Result<Option<u64>, StoreError> {
        if self.fail_unseal {
            return Err(StoreError);
        }
        Ok(self.sealed)
    }
    fn seal_counter(&mut self, epoch: u64) -> Result<(), StoreError> {
        if self.fail_seal {
            return Err(StoreError);
        }
        self.sealed = Some(epoch);
        Ok(())
    }
}
