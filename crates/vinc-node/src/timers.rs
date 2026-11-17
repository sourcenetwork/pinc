//! The bound on the node's timer.
//!
//! A host serves what is due before anything else, so a deadline that stays due however often its timer is served has
//! the host call again at once, forever (vinc#551, vinc#569). A layer may name the time of a timer call as its next
//! deadline: the endpoint does when a layer that ran after it in the same call gave it something to send, and the
//! delay-tolerant layer does when its contacts changed. That is a layer asking to be called again at once, and the
//! next call moves it. What no layer may do is leave due, after a timer call, a deadline that was due at the timer
//! call before and that this one left due as well: that deadline does not move.
//!
//! The node checks for it as the last step of every timer call. Such a deadline is counted against the layer that
//! holds it and recorded in the trace the first time for that layer, and the node answers one [`TIMER_TICK`] after
//! the call until the next timer call. The host yields, the layers that kept their contract are served at most one
//! tick late, and [`TimerStats`] names the layer at fault.
//!
//! Invariants: a deadline left due by two timer calls in a row, and due at the time of the first, is answered no
//! earlier than one tick after the second (for every time below the top of the clock's range); a node whose layers
//! move their deadlines counts nothing, records nothing and answers its layers' earliest deadline unchanged.

use crate::apps::Apps;
use crate::config::{Nanos, Store, TIMER_TICK};
use crate::ep::Ep;
use crate::node::Node;
use crate::trace::NodeTrace;

/// One of the deadlines the node combines into its own, in the order it combines them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Timed {
    /// The endpoint.
    Endpoint,
    /// The connectivity client.
    Connectivity,
    /// Membership.
    Membership,
    /// Broadcast.
    Broadcast,
    /// Verified streaming of values.
    Values,
    /// Set reconciliation.
    Sets,
    /// Delay-tolerant delivery.
    Dtn,
    /// The node's own periodic duties.
    Duties,
    /// The port-mapping client.
    PortMapping,
}

impl Timed {
    /// Every deadline, in the order of [`Node::poll_timeout`]'s minimum and of the codes in
    /// [`NodeTrace::TimerStuck`].
    pub const ALL: [Self; 9] = [
        Self::Endpoint,
        Self::Connectivity,
        Self::Membership,
        Self::Broadcast,
        Self::Values,
        Self::Sets,
        Self::Dtn,
        Self::Duties,
        Self::PortMapping,
    ];
}

/// How many timer calls left each of the node's deadlines due as the timer call before had left it, since the node
/// started. All zero in a node whose layers move their deadlines.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TimerStats {
    stuck: [u64; Timed::ALL.len()],
}

impl TimerStats {
    /// The timer calls that did not move the deadline of `timer`.
    pub fn stuck(&self, timer: Timed) -> u64 {
        self.stuck.get(timer as usize).copied().unwrap_or(0)
    }

    /// The count of every deadline together. A call that left two deadlines due counts twice.
    pub fn total(&self) -> u64 {
        self.stuck.iter().fold(0, |n, s| n.saturating_add(*s))
    }
}

/// What the node keeps for the bound.
#[derive(Debug, Default)]
pub(crate) struct Bound {
    /// The last timer call did not move a deadline: until the next one the node answers no earlier than this.
    held: Option<Nanos>,
    /// The time of the last timer call.
    last: Option<Nanos>,
    /// For each deadline, whether the last timer call left it due.
    left: [bool; Timed::ALL.len()],
    stats: TimerStats,
    /// A deadline of the endpoint that no call moves, as a probe.
    #[cfg(feature = "trace")]
    stub: Option<Nanos>,
}

impl Bound {
    /// The deadline the node answers when its layers name `due`.
    pub(crate) fn answer(&self, due: Option<Nanos>) -> Option<Nanos> {
        match (due, self.held) {
            (Some(d), Some(h)) => Some(d.max(h)),
            _ => due,
        }
    }
}

impl<E, P, St, const R: usize, const PEERS: usize, A> Node<E, P, St, R, PEERS, A>
where
    E: Ep,
    P: vinc_crypto::Provider + Clone,
    St: Store,
    A: Apps<P>,
    E::Src: crate::apps::ServeSource<A::Values>,
{
    /// How many timer calls did not move each deadline; see [`TimerStats`].
    pub const fn timer_stats(&self) -> TimerStats {
        self.timers.stats
    }

    /// The endpoint's deadline.
    pub(crate) fn ep_deadline(&self) -> Option<Nanos> {
        let due = self.io.ep.poll_timeout();
        #[cfg(feature = "trace")]
        let due = [due, self.timers.stub].into_iter().flatten().min();
        due
    }

    /// Give the endpoint a deadline at `at` that no call moves, or take it away with `None`, as a probe (with the
    /// `trace` feature, which the tests enable): a layer that breaks the timer contract.
    #[cfg(feature = "trace")]
    #[doc(hidden)]
    pub fn stick_timer(&mut self, at: Option<Nanos>) {
        self.timers.stub = at;
        self.deadline.set(crate::node::Due::Stale);
    }

    /// Check the deadlines the timer call at `now` left, as its last step.
    pub(crate) fn bound_timer(&mut self, now: Nanos) {
        let dues = [self.ep_deadline()]
            .into_iter()
            .chain(self.layer_deadlines(self.io.now));
        let last = self.timers.last.replace(now);
        self.timers.held = None;
        let slots = self.timers.left.iter_mut().zip(&mut self.timers.stats.stuck);
        for (due, (timer, (left, n))) in dues.zip(Timed::ALL.into_iter().zip(slots)) {
            let due = due.filter(|d| *d <= now);
            // Due already at the last timer call, which left it due, and left due again: not moved. A deadline named
            // since then is a layer asking to be called again at once.
            let stuck = *left && last.is_some_and(|l| due.is_some_and(|d| d <= l));
            *left = due.is_some();
            if !stuck {
                continue;
            }
            if *n == 0 {
                self.io.trace(NodeTrace::TimerStuck { timer: timer as u64 });
            }
            *n = n.saturating_add(1);
            self.timers.held = Some(now.saturating_add(TIMER_TICK));
        }
    }
}
