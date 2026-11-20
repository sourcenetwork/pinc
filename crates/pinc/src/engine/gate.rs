//! The access hook and the bar of revoked peers.
//!
//! The host's hook sits behind the bar: a revoked peer is refused whatever the hook would say. The handles and the core
//! share one [`Gate`]; the bar is borrowed only for a lookup or an update and never while the hook runs, so asking it
//! never depends on what the endpoint is doing.

use alloc::rc::Rc;

use pinc_crypto::NodeId;
use pinc_security::Alpn;

use crate::maps::{self, Keys, Map, Set};

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

/// The direction a session of `alpn` is asked about: the hub protocol is [`Direction::Gossip`], any other is
/// [`Direction::Outbound`] when this node dialed it and [`Direction::Inbound`] when the peer did.
pub(super) fn direction(alpn: &[u8], dialing: bool) -> Direction {
    if alpn == pinc_node::HUB_ALPN {
        Direction::Gossip
    } else if dialing {
        Direction::Outbound
    } else {
        Direction::Inbound
    }
}

/// The access hook: whether a peer may connect or be a neighbour. The endpoint asks it while it handles an event, in a
/// short section on the thread that drives it, so it must not block and must not call back into the endpoint. It
/// holds no endpoint state: [`Endpoint::admit`](crate::Endpoint::admit) asks the same hook at any time.
///
/// It is asked for the protocol and direction of each session, once for a peer while its answer stands: a later
/// session of the same protocol and direction, within 30 seconds, is taken up on that answer, and any other is asked
/// when it comes up. A refused session is closed with [`DENIED`] before anything of it reaches the application. The
/// endpoint also keeps one answer per peer; when the hook refuses the question that raised it, it is asked about the
/// peer's other sessions and dials and about every served protocol in both directions, and the peer stays reachable
/// while one is allowed. A refusal kept for a peer does not fail a later dial the hook allows: the hook is asked for
/// that dial. The hook must give the same answer to the same question while nothing it decides on has changed, as an
/// answer is used for at most 30 seconds before it is asked again.
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
    revoked: core::cell::RefCell<Set<NodeId>>,
}

impl<A: Admit> Gate<A> {
    pub(crate) fn new(hook: A, keys: Keys) -> Self {
        Self {
            hook,
            revoked: core::cell::RefCell::new(maps::set(keys)),
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

/// The most peers [`Known`] holds.
const KNOWN_MAX: usize = 1024;

/// The question the hook last answered with an allow for the endpoint's per-peer check, per peer, and until when. A
/// session of exactly that protocol and direction is taken up without asking the hook again, so a hook is asked once
/// per question while the endpoint's own answer stands, not once per session. The table is bounded, and losing an
/// entry is always safe: it costs one more call of the hook.
pub(crate) struct Known(Map<[u8; 32], (Alpn, Direction, u64)>);

impl Known {
    pub(crate) fn new(keys: Keys) -> Self {
        Self(maps::map(keys))
    }

    /// Whether the answer remembered for `node` is an allow for this `alpn` and `dir` that has not run out at `now`.
    pub(crate) fn covers(&self, now: u64, node: &NodeId, alpn: Alpn, dir: Direction) -> bool {
        self.0
            .get(&node.bytes)
            .is_some_and(|&(a, d, until)| a == alpn && d == dir && now < until)
    }

    /// Remember an allow of `alpn` and `dir` for `node` for as long as the endpoint keeps its own answer.
    pub(crate) fn remember(&mut self, now: u64, node: &NodeId, alpn: Alpn, dir: Direction) {
        if self.0.len() >= KNOWN_MAX && !self.0.contains_key(&node.bytes) {
            self.0.retain(|_, &mut (_, _, until)| now < until);
            if self.0.len() >= KNOWN_MAX {
                self.0.clear();
            }
        }
        let until = now.saturating_add(pinc_core::ACP_TTL);
        self.0.insert(node.bytes, (alpn, dir, until));
    }

    /// The allow remembered for `node` that has not run out at `now`, as a probe reads it.
    #[cfg(feature = "trace")]
    pub(crate) fn peek(&self, now: u64, node: &NodeId) -> Option<(Alpn, Direction)> {
        self.0
            .get(&node.bytes)
            .filter(|&&(_, _, until)| now < until)
            .map(|&(a, d, _)| (a, d))
    }

    /// Drop what is remembered for `node`.
    pub(crate) fn forget(&mut self, node: &[u8; 32]) {
        self.0.remove(node);
    }
}
