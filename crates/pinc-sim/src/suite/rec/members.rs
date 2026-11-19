//! Membership events and the access-control oracle of the recorder.
//!
//! The recorder keeps what every node reported about the membership (for G-AWARE and L5) and the oracle's answers
//! to access checks (for G-ACP). Invariant: the oracle decides at request time from the denied set and the recorded
//! revocations only, and every answer about a known principal is logged so a delivery can later be checked against
//! the answer the receiving node actually got.

use super::{Rec, idx_py, int};
use crate::reference::Py;

/// The kind of a membership event, in the reference's names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum MemberKind {
    /// `MemberJoined`.
    Joined,
    /// `MemberLeft`.
    Left,
    /// `MemberSuspected`.
    Suspected,
    /// `MemberConfirmedDown`.
    ConfirmedDown,
    /// `MemberRevoked`.
    Revoked,
    /// `AddressChanged`.
    AddressChanged,
    /// `StackChanged`.
    StackChanged,
}

/// A core event as the recorder sees it; `member` is a node index already resolved by the caller (`None` when the
/// id is unknown).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MemberEvent {
    /// A new view with this epoch.
    ViewChanged {
        /// The epoch.
        epoch: u64,
    },
    /// A member joined.
    Joined(Option<usize>),
    /// A member left.
    Left(Option<usize>),
    /// A member is suspected.
    Suspected(Option<usize>),
    /// A member is confirmed down.
    ConfirmedDown(Option<usize>),
    /// A member was revoked.
    Revoked(Option<usize>),
    /// A member's address changed.
    AddressChanged(Option<usize>),
    /// A member's stack changed to `version`.
    StackChanged {
        /// The member.
        member: Option<usize>,
        /// The new stack version.
        version: u64,
    },
    /// An incoming connection.
    Incoming,
    /// An outgoing connection came up.
    Connected,
}

/// One recorded membership event: `(t, node, kind, member, extra)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MemberRec {
    /// When.
    pub t: u64,
    /// The reporting node.
    pub node: usize,
    /// What it reported.
    pub kind: MemberKind,
    /// About whom (`None` when the id was unknown).
    pub member: Option<usize>,
    /// The stack version of a `StackChanged`.
    pub extra: Option<u64>,
}

impl Rec {
    /// A core event of node `idx` (incarnation `incarnation`) at `now`.
    pub fn core_event(&mut self, now: u64, idx: usize, incarnation: u64, ev: &MemberEvent) {
        let (kind, member, extra) = match *ev {
            MemberEvent::ViewChanged { epoch } => {
                let key = (idx, incarnation);
                if self.view_epochs.get(&key).is_some_and(|&last| epoch <= last) {
                    self.violation(now, "G-AWARE", idx, "view epoch not strictly increasing");
                }
                self.view_epochs.insert(key, epoch);
                return;
            }
            MemberEvent::Incoming | MemberEvent::Connected => {
                let k = if matches!(ev, MemberEvent::Incoming) {
                    "Incoming"
                } else {
                    "Connected"
                };
                self.hash(&[Py::Str("C"), idx_py(idx), Py::Str(k), int(now)]);
                return;
            }
            MemberEvent::Joined(m) => (MemberKind::Joined, m, None),
            MemberEvent::Left(m) => (MemberKind::Left, m, None),
            MemberEvent::Suspected(m) => (MemberKind::Suspected, m, None),
            MemberEvent::ConfirmedDown(m) => (MemberKind::ConfirmedDown, m, None),
            MemberEvent::Revoked(m) => (MemberKind::Revoked, m, None),
            MemberEvent::AddressChanged(m) => (MemberKind::AddressChanged, m, None),
            MemberEvent::StackChanged { member, version } => (MemberKind::StackChanged, member, Some(version)),
        };
        self.membership.push(MemberRec {
            t: now,
            node: idx,
            kind,
            member,
            extra,
        });
    }

    /// The oracle's answer to node `idx` asking about `principal` at `now`: `(allow, valid until)`. Allowed iff the
    /// principal is a known node, neither it nor the asker is denied, and it is not revoked at `now`.
    pub fn acp_decide(&mut self, now: u64, idx: usize, principal: Option<usize>) -> (bool, u64) {
        let mut allow = principal.is_some_and(|p| !self.denied.contains(&p) && !self.denied.contains(&idx));
        if principal
            .and_then(|p| self.revoked.get(&p))
            .is_some_and(|&rv| now >= rv)
        {
            allow = false;
        }
        let validity = now + self.world.acp_validity_ns;
        if let Some(p) = principal {
            self.acp_log.entry((idx, p)).or_default().push((now, allow, validity));
        }
        (allow, validity)
    }

    /// Was `principal` allowed for `node` at `t` by an answer the node received (the latest covering answer wins)?
    pub fn acp_allowed(&self, node: usize, principal: usize, t: u64) -> Option<bool> {
        self.acp_log
            .get(&(node, principal))?
            .iter()
            .rev()
            .find(|&&(ta, _, vu)| ta <= t && t <= vu)
            .map(|&(_, allow, _)| allow)
    }

    /// The access check at an application delivery to `node` of data from `origin` (`None`: an origin that is not
    /// a known node, which can never have been allowed). Records a G-ACP violation and returns false on failure.
    pub fn check_acp_delivery(&mut self, now: u64, node: usize, origin: impl Into<Option<usize>>) -> bool {
        let origin = origin.into();
        let bound = self.world.revocation_bound_cap_ns.min(self.revocation_bound_ns);
        for p in [origin, Some(node)] {
            let Some(p) = p else { continue };
            if self.denied.contains(&p) {
                self.acp_violations += 1;
                self.violation(
                    now,
                    "G-ACP",
                    node,
                    "data delivered to or accepted from a denied principal",
                );
                return false;
            }
            if self.revoked.get(&p).is_some_and(|&rv| now > rv + bound) {
                self.acp_violations += 1;
                self.violation(
                    now,
                    "G-ACP",
                    node,
                    "data exchanged with a revoked principal after the revocation bound",
                );
                return false;
            }
        }
        let allowed = origin.and_then(|o| self.acp_allowed(node, o, now));
        if allowed != Some(true) && origin != Some(node) {
            self.acp_violations += 1;
            self.violation(
                now,
                "G-ACP",
                node,
                "data accepted without an allow answer from the access-control oracle (fail closed, H16)",
            );
            return false;
        }
        true
    }
}
