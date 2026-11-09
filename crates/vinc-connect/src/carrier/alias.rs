//! The 1-byte node aliases of one carrier direction (`RELAY_ALIAS`, at most [`ALIAS_MAX`]).
//!
//! On one ordered, reliable carrier a 33-byte node id is sent once together with a 1-byte alias, and the alias alone
//! afterwards. Invariants: an alias is below [`ALIAS_MAX`]; the sender assigns aliases `0, 1, 2, ...` in first-use
//! order and clears the whole table when a 33rd node would need one (so a receiver that learns aliases from the
//! stream stays in step); a receiver overwrites the slot named by a new-alias frame.

use vinc_crypto::NodeId;

use super::frame::Frame;

/// The most aliases one carrier direction holds.
pub const ALIAS_MAX: usize = 32;

/// How an outbound node resolved against the table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Assigned {
    /// The node already has this alias: send the alias form.
    Known(u8),
    /// The node just received this alias: send the node id together with it.
    New(u8),
}

/// Aliases of one direction of one carrier.
#[derive(Debug, Clone)]
pub struct AliasTable {
    slots: [Option<NodeId>; ALIAS_MAX],
    len: usize,
}

impl Default for AliasTable {
    fn default() -> Self {
        Self::new()
    }
}

impl AliasTable {
    /// An empty table.
    pub const fn new() -> Self {
        Self {
            slots: [None; ALIAS_MAX],
            len: 0,
        }
    }

    /// Forget every alias.
    pub const fn clear(&mut self) {
        self.slots = [None; ALIAS_MAX];
        self.len = 0;
    }

    /// Sender side: the alias for `node`, assigning the next one on first use.
    pub fn assign(&mut self, node: &NodeId) -> Assigned {
        if let Some(a) = self.slots.iter().take(self.len).position(|s| s.as_ref() == Some(node)) {
            return Assigned::Known(u8::try_from(a).unwrap_or(0));
        }
        if self.len >= ALIAS_MAX {
            self.clear();
        }
        let alias = u8::try_from(self.len).unwrap_or(0);
        if let Some(slot) = self.slots.get_mut(self.len) {
            *slot = Some(*node);
        }
        self.len += 1;
        Assigned::New(alias)
    }

    /// Receiver side: remember that `alias` names `node`. An alias of [`ALIAS_MAX`] or more is ignored (the codec
    /// never produces one).
    pub fn learn(&mut self, alias: u8, node: NodeId) {
        if let Some(slot) = self.slots.get_mut(usize::from(alias)) {
            *slot = Some(node);
        }
    }

    /// Receiver side: the node an alias names.
    pub fn resolve(&self, alias: u8) -> Option<NodeId> {
        self.slots.get(usize::from(alias)).copied().flatten()
    }

    /// The frame that sends `packet` toward `dst` from a node, in alias form where possible (client to relay).
    pub fn send_frame<'a>(&mut self, dst: &NodeId, flag: u8, packet: &'a [u8]) -> Frame<'a> {
        match self.assign(dst) {
            Assigned::Known(alias) => Frame::SendAlias { alias, flag, packet },
            Assigned::New(alias) => Frame::SendNew {
                dst: *dst,
                alias,
                flag,
                packet,
            },
        }
    }

    /// The frame that delivers `packet` from `src` to a node, in alias form where possible (relay to client).
    pub fn recv_frame<'a>(&mut self, src: &NodeId, flag: u8, packet: &'a [u8]) -> Frame<'a> {
        match self.assign(src) {
            Assigned::Known(alias) => Frame::RecvAlias { alias, flag, packet },
            Assigned::New(alias) => Frame::RecvNew {
                src: *src,
                alias,
                flag,
                packet,
            },
        }
    }
}
