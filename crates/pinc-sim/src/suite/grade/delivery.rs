//! The delivery check: over the small intents of a run, the share of receivers outside the must set that were
//! delivered at all (and the same for the must set).
//!
//! It is not a gate. A candidate more than two points below the baseline share in any checked scenario is excluded
//! by the evaluator; this module only computes the shares.
//!
//! Invariant: only small intents with receivers count, the sender never counts as a receiver of its own intent, and
//! "delivered" means delivered at any time (the deadline is not applied).

use crate::suite::rec::Rec;
use crate::suite::world::model::World;

/// Delivered and intended receiver counts of the must group and of the group outside the must set.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DeliveryShares {
    /// `(delivered, intended)` over receivers in the must set.
    pub must: (u64, u64),
    /// `(delivered, intended)` over receivers outside the must set.
    pub outside: (u64, u64),
}

/// Both shares of a finished run.
pub fn delivery_shares(rec: &Rec) -> DeliveryShares {
    let mut s = DeliveryShares::default();
    for it in rec.intents.values().filter(|it| it.small && !it.receivers.is_empty()) {
        for &x in it.receivers.iter().filter(|&&x| x != it.node) {
            let group = if it.must_set.contains(&x) {
                &mut s.must
            } else {
                &mut s.outside
            };
            group.1 += 1;
            group.0 += u64::from(it.delivered.contains_key(&x));
        }
    }
    s
}

/// `(delivered, intended)` over the receivers outside the must set: the figure the delivery check compares.
pub fn delivery_share(_world: &World, rec: &Rec) -> (u64, u64) {
    delivery_shares(rec).outside
}
