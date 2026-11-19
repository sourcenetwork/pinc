//! Binary spray-and-wait forwarding with a copy budget, contacts as inputs and link-aware retransmission timers.
//!
//! A holder of `n >= 2` copies of a bundle that meets a peer other than the destination hands the peer `n / 2` copies
//! and keeps the rest; a holder of one copy waits and hands the bundle only to the destination. A handover is a
//! transfer: it is recorded when sent, retransmitted when its timer runs out, and finished when the peer acknowledges.
//!
//! The machine is SANS-IO and deterministic: [`Forwarder::step`] takes the physical time and one [`Input`]
//! (contacts, acknowledgements, holds), and [`Forwarder::poll`] returns the next [`Action`] to perform. Nothing reads
//! a clock.
//!
//! Invariants:
//! - **Copies are conserved.** The copies a node holds plus the copies it has handed to peers never exceed the copies
//!   it received. Handed copies are never taken back (a peer may have received them even if the acknowledgement was
//!   lost), so across any forwarding graph the number of copies in existence is at most the head's budget.
//!   A hold of a bundle already held ignores the extra copies: they are lost, never duplicated.
//! - **A finished bundle stays finished.** Every accepted bundle is remembered in a bounded table until its own
//!   expiry, whether it is still held or was released (delivered, expired or forgotten). A hold of a remembered,
//!   unexpired bundle that is no longer held is ignored and counted ([`Forwarder::ignored_holds`]), so a late
//!   duplicate of a hold never re-creates copies the budget already counted. When the table has no free or expired
//!   slot a new hold is refused with [`ForwardError::Full`]; a remembered bundle is never forgotten early, because
//!   that would re-open the over-budget hole.
//! - **Timers pause while a link is down.** A retransmission timer counts down only for the time its link was up:
//!   `step` first charges the elapsed time to the transfers whose link is up, then applies the input. A timer on a
//!   down link keeps its remaining time until the link comes up again. Bundle lifetimes are wall-clock and do not
//!   pause.
//! - **Bounded.** Bundles, links, transfers and remembered bundles live in const-generic arrays; when a table is full the machine
//!   refuses the input or sprays nothing, and says so, rather than growing.
//! - A transfer is created once per (bundle, peer): a bundle is never sprayed to the same peer twice.

use pinc_crypto::NodeId;

use crate::head::BundleId;

/// Tunable policy of the forwarder.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Policy {
    /// Milliseconds of link-up time before an unacknowledged transfer is sent again.
    pub retry_ms: u64,
    /// How many times a transfer is sent in all (the first send included) before it is given up.
    pub max_sends: u8,
}

/// A bundle to forward.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Held {
    /// The bundle.
    pub id: BundleId,
    /// Its destination.
    pub destination: NodeId,
    /// The physical time (milliseconds) at which it expires.
    pub expires: u64,
    /// The copies this node holds (at least 1).
    pub copies: u16,
}

/// An input to the machine.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Input {
    /// Only time passes.
    Tick,
    /// Start forwarding a bundle.
    Hold(Held),
    /// The link to a peer is up (a contact opportunity).
    LinkUp(NodeId),
    /// The link to a peer is down.
    LinkDown(NodeId),
    /// A peer acknowledged a transfer.
    Acked {
        /// The acknowledging peer.
        peer: NodeId,
        /// The bundle.
        bundle: BundleId,
    },
    /// Stop forwarding a bundle (it was released elsewhere).
    Forget(BundleId),
}

/// What the machine asks the host to do.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Action {
    /// Send `bundle` to `peer` with `copies` copies (0 for a delivery to the destination).
    Send {
        /// The peer.
        peer: NodeId,
        /// The bundle.
        bundle: BundleId,
        /// The copies handed over.
        copies: u16,
        /// Whether this repeats an earlier send.
        retransmit: bool,
    },
    /// The bundle is done (delivered or expired): release its store entry.
    Release(BundleId),
}

/// Why an input was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForwardError {
    /// The bundle is already held; the copies offered are ignored.
    Duplicate,
    /// A table is full.
    Full,
    /// The hold carried no copies.
    NoCopies,
    /// The bundle or transfer is unknown.
    Unknown,
    /// The bundle was held and finished (released or forgotten) and has not expired: the hold is ignored.
    Finished,
}

impl core::fmt::Display for ForwardError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::Duplicate => "the bundle is already held",
            Self::Full => "a forwarding table is full",
            Self::NoCopies => "a hold needs at least one copy",
            Self::Unknown => "unknown bundle or transfer",
            Self::Finished => "the bundle is already finished",
        })
    }
}

impl core::error::Error for ForwardError {}

#[derive(Debug, Clone, Copy)]
struct Bundle {
    held: Held,
    delivered: bool,
}

/// A remembered bundle: its id and the physical time at which the memory ends.
#[derive(Debug, Clone, Copy)]
struct Seen {
    id: BundleId,
    expires: u64,
}

#[derive(Debug, Clone, Copy)]
struct Link {
    peer: NodeId,
    up: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Phase {
    /// Sent and not acknowledged; `remaining` link-up milliseconds until the next send.
    Sent {
        remaining: u64,
        sends: u8,
    },
    Acked,
    GaveUp,
}

#[derive(Debug, Clone, Copy)]
struct Transfer {
    bundle: BundleId,
    peer: NodeId,
    given: u16,
    deliver: bool,
    phase: Phase,
}

/// Spray-and-wait for at most `B` bundles, `L` links and `T` transfers, remembering at most `F` bundles (held or
/// finished) until their expiry.
#[derive(Debug, Clone)]
pub struct Forwarder<const B: usize, const L: usize, const T: usize, const F: usize> {
    policy: Policy,
    now: u64,
    bundles: [Option<Bundle>; B],
    links: [Option<Link>; L],
    transfers: [Option<Transfer>; T],
    seen: [Option<Seen>; F],
    // A metric: nothing reads it, so the models leave it out.
    ignored: u32,
}

impl<const B: usize, const L: usize, const T: usize, const F: usize> Forwarder<B, L, T, F> {
    /// An empty forwarder starting at physical time `now`.
    pub const fn new(policy: Policy, now: u64) -> Self {
        Self {
            policy,
            now,
            bundles: [None; B],
            links: [None; L],
            transfers: [None; T],
            seen: [None; F],
            ignored: 0,
        }
    }

    /// Charge the time since the last step to the timers whose link is up. Time never runs backwards.
    fn advance(&mut self, now: u64) {
        let dt = now.saturating_sub(self.now);
        self.now = self.now.max(now);
        let links = self.links;
        for t in self.transfers.iter_mut().flatten() {
            let up = links.iter().flatten().any(|l| l.up && l.peer == t.peer);
            if let (Phase::Sent { remaining, .. }, true) = (&mut t.phase, up) {
                *remaining = remaining.saturating_sub(dt);
            }
        }
    }

    /// Apply `input` at physical time `now`.
    ///
    /// # Errors
    /// [`ForwardError::Duplicate`] for a hold of a bundle already held (its offered copies are ignored);
    /// [`ForwardError::Finished`] for a hold of a bundle that was finished and has not expired (ignored and counted);
    /// [`ForwardError::NoCopies`]; [`ForwardError::Full`] if a table is full, the table of remembered bundles
    /// included; [`ForwardError::Unknown`] for an ack of no transfer. The elapsed time is charged in every case.
    pub fn step(&mut self, now: u64, input: Input) -> Result<(), ForwardError> {
        self.advance(now);
        match input {
            Input::Tick => Ok(()),
            Input::Hold(held) => {
                if held.copies == 0 {
                    return Err(ForwardError::NoCopies);
                }
                if self.bundles.iter().flatten().any(|b| b.held.id == held.id) {
                    return Err(ForwardError::Duplicate);
                }
                if self
                    .seen
                    .iter()
                    .flatten()
                    .any(|d| d.id == held.id && d.expires > self.now)
                {
                    self.ignored = self.ignored.saturating_add(1);
                    return Err(ForwardError::Finished);
                }
                let now = self.now;
                let memory = self
                    .seen
                    .iter_mut()
                    .find(|s| s.is_none_or(|d| d.expires <= now))
                    .ok_or(ForwardError::Full)?;
                let slot = self
                    .bundles
                    .iter_mut()
                    .find(|s| s.is_none())
                    .ok_or(ForwardError::Full)?;
                *memory = Some(Seen {
                    id: held.id,
                    expires: held.expires,
                });
                *slot = Some(Bundle { held, delivered: false });
                Ok(())
            }
            Input::LinkUp(peer) | Input::LinkDown(peer) => {
                let up = matches!(input, Input::LinkUp(_));
                if let Some(l) = self.links.iter_mut().flatten().find(|l| l.peer == peer) {
                    l.up = up;
                    return Ok(());
                }
                let slot = self.links.iter_mut().find(|s| s.is_none()).ok_or(ForwardError::Full)?;
                *slot = Some(Link { peer, up });
                Ok(())
            }
            Input::Acked { peer, bundle } => {
                let t = self
                    .transfers
                    .iter_mut()
                    .flatten()
                    .find(|t| t.bundle == bundle && t.peer == peer)
                    .ok_or(ForwardError::Unknown)?;
                t.phase = Phase::Acked;
                if t.deliver
                    && let Some(b) = self.bundles.iter_mut().flatten().find(|b| b.held.id == bundle)
                {
                    b.delivered = true;
                }
                Ok(())
            }
            Input::Forget(bundle) => self.drop_bundle(&bundle).ok_or(ForwardError::Unknown),
        }
    }

    fn drop_bundle(&mut self, id: &BundleId) -> Option<()> {
        let slot = self.bundles.iter_mut().find(|s| s.is_some_and(|b| b.held.id == *id))?;
        *slot = None;
        for t in &mut self.transfers {
            if t.is_some_and(|t| t.bundle == *id) {
                *t = None;
            }
        }
        Some(())
    }

    /// The physical time (milliseconds) at which the machine next has something to do without any input: the first
    /// bundle expiry, or the first retransmission timer of a transfer whose link is up (a timer on a down link waits
    /// for its link). `None` when neither exists.
    pub fn poll_timeout(&self) -> Option<u64> {
        let expiry = self.bundles.iter().flatten().map(|b| b.held.expires);
        let retry = self.transfers.iter().flatten().filter_map(|t| match t.phase {
            Phase::Sent { remaining, .. } if self.links.iter().flatten().any(|l| l.up && l.peer == t.peer) => {
                Some(self.now.saturating_add(remaining))
            }
            _ => None,
        });
        expiry.chain(retry).min()
    }

    /// The next action to perform, or `None` when the machine is quiet. Call until `None` after every `step`.
    ///
    /// Order: a finished or expired bundle is released first; then due retransmissions on links that are up; then
    /// new handovers, by link slot then bundle slot.
    pub fn poll(&mut self) -> Option<Action> {
        let now = self.now;
        let done = self
            .bundles
            .iter()
            .flatten()
            .find(|b| b.delivered || b.held.expires <= now)
            .map(|b| b.held.id);
        if let Some(id) = done {
            self.drop_bundle(&id);
            return Some(Action::Release(id));
        }
        if let Some(action) = self.poll_retransmit() {
            return Some(action);
        }
        self.poll_spray()
    }

    fn poll_retransmit(&mut self) -> Option<Action> {
        let links = self.links;
        let policy = self.policy;
        for t in self.transfers.iter_mut().flatten() {
            let Phase::Sent { remaining: 0, sends } = t.phase else {
                continue;
            };
            if !links.iter().flatten().any(|l| l.up && l.peer == t.peer) {
                continue;
            }
            if sends >= policy.max_sends {
                t.phase = Phase::GaveUp;
                continue;
            }
            t.phase = Phase::Sent {
                remaining: policy.retry_ms,
                sends: sends.saturating_add(1),
            };
            return Some(Action::Send {
                peer: t.peer,
                bundle: t.bundle,
                copies: t.given,
                retransmit: true,
            });
        }
        None
    }

    fn poll_spray(&mut self) -> Option<Action> {
        let policy = self.policy;
        for li in 0..L {
            let Some(link) = self.links.get(li).copied().flatten().filter(|l| l.up) else {
                continue;
            };
            for bi in 0..B {
                let Some(bundle) = self.bundles.get(bi).copied().flatten() else {
                    continue;
                };
                let id = bundle.held.id;
                if self
                    .transfers
                    .iter()
                    .flatten()
                    .any(|t| t.bundle == id && t.peer == link.peer)
                {
                    continue;
                }
                let deliver = link.peer == bundle.held.destination;
                let given = if deliver { 0 } else { bundle.held.copies / 2 };
                if !deliver && given == 0 {
                    continue;
                }
                let slot = self.transfers.iter_mut().find(|s| s.is_none())?;
                *slot = Some(Transfer {
                    bundle: id,
                    peer: link.peer,
                    given,
                    deliver,
                    phase: Phase::Sent {
                        remaining: policy.retry_ms,
                        sends: 1,
                    },
                });
                if let Some(b) = self.bundles.get_mut(bi).and_then(Option::as_mut) {
                    b.held.copies -= given;
                }
                return Some(Action::Send {
                    peer: link.peer,
                    bundle: id,
                    copies: given,
                    retransmit: false,
                });
            }
        }
        None
    }

    /// How many holds were ignored because the bundle was finished and had not expired.
    pub const fn ignored_holds(&self) -> u32 {
        self.ignored
    }

    /// The copies this node still holds of `bundle`.
    pub fn copies_held(&self, bundle: &BundleId) -> Option<u16> {
        self.bundles
            .iter()
            .flatten()
            .find(|b| b.held.id == *bundle)
            .map(|b| b.held.copies)
    }

    /// The copies this node has handed to peers for `bundle`, acknowledged or not.
    pub fn copies_handed(&self, bundle: &BundleId) -> u32 {
        self.transfers
            .iter()
            .flatten()
            .filter(|t| t.bundle == *bundle)
            .map(|t| u32::from(t.given))
            .sum()
    }

    /// The link-up milliseconds left on the timer of the transfer of `bundle` to `peer`, if one is running.
    pub fn timer_remaining(&self, peer: &NodeId, bundle: &BundleId) -> Option<u64> {
        self.transfers
            .iter()
            .flatten()
            .find(|t| t.bundle == *bundle && t.peer == *peer)
            .and_then(|t| match t.phase {
                Phase::Sent { remaining, .. } => Some(remaining),
                _ => None,
            })
    }
}
