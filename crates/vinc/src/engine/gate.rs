//! The access hook and the bar of revoked peers.
//!
//! The host's hook sits behind the bar: a revoked peer is refused whatever the hook would say. The handles and the core
//! share one [`Gate`]; the bar is borrowed only for a lookup or an update and never while the hook runs, so asking it
//! never depends on what the endpoint is doing.

use std::rc::Rc;

use vinc_crypto::NodeId;

/// Which way a connection was made, as the access hook is told.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Direction {
    /// A peer dialed this node.
    Inbound,
    /// This node dialed the peer.
    Outbound,
    /// A broadcast layer asks to take the peer as a neighbour or to reach it.
    Gossip,
}

/// The access hook: whether a peer may connect or be a neighbour. The endpoint asks it while it handles an event, in a
/// short section on the thread that drives it, so it must not block and must not call back into the endpoint. It
/// holds no endpoint state: [`Endpoint::admit`](crate::Endpoint::admit) asks the same hook at any time.
pub trait Admit {
    /// Whether `peer` may use `alpn` in `dir`.
    fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool;
}

impl<T: Admit + ?Sized> Admit for Rc<T> {
    fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        (**self).admit(peer, alpn, dir)
    }
}

/// The close code of a session whose peer is not admitted.
pub const DENIED: u64 = 3;
/// The most peers that can be revoked at once.
pub const REVOKED_MAX: usize = 4096;

/// The host's access hook behind the bar of revoked peers. The handles and the core share it; the bar is borrowed only
/// for a lookup or an update and never while the hook runs, so asking it never depends on what the endpoint is doing.
pub(crate) struct Gate<A> {
    hook: A,
    revoked: core::cell::RefCell<rapidhash::RapidHashSet<NodeId>>,
}

impl<A: Admit> Gate<A> {
    pub(crate) fn new(hook: A) -> Self {
        Self {
            hook,
            revoked: core::cell::RefCell::new(rapidhash::RapidHashSet::default()),
        }
    }

    /// Whether `peer` is barred.
    pub(crate) fn is_revoked(&self, peer: &NodeId) -> bool {
        self.revoked.try_borrow().is_ok_and(|r| r.contains(peer))
    }

    /// Whether `peer` may use `alpn` in `dir`: never while it is revoked, else what the host's hook says.
    pub(crate) fn admit(&self, peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        !self.is_revoked(peer) && self.hook.admit(peer, alpn, dir)
    }

    /// Bar `peer`; false when the table is full and it is not in it.
    pub(crate) fn bar(&self, peer: &NodeId) -> bool {
        let Ok(mut r) = self.revoked.try_borrow_mut() else {
            return false;
        };
        r.contains(peer) || (r.len() < REVOKED_MAX && r.insert(*peer))
    }

    /// Lift the bar on `peer`; whether it was barred.
    pub(crate) fn lift(&self, peer: &NodeId) -> bool {
        self.revoked.try_borrow_mut().is_ok_and(|mut r| r.remove(peer))
    }
}

/// The access hook that admits everyone.
#[derive(Debug, Clone, Copy, Default)]
pub struct AllowAll;

impl Admit for AllowAll {
    fn admit(&self, _peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        true
    }
}
