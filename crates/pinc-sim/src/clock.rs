//! A node's local clock: offset, drift and jumps, applied to wall-clock inputs only.
//!
//! `local(t) = t + offset + t * drift_ppm / 1e6 + sum(jumps at or before t)`. The simulator never feeds this to a
//! node by itself; it hands the clock to the node through [`crate::Node::clock_changed`] and answers
//! [`crate::Sim::wall_time`], so the node adapter decides which inputs are wall-clock and converts its deadlines back
//! with [`Clock::to_true`].

use crate::Time;

/// A local clock model. The default is a perfect clock.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Clock {
    /// Constant offset in nanoseconds; may be negative.
    pub offset: i64,
    /// Drift in parts per million.
    pub drift_ppm: i64,
    /// Jumps as `(true time they take effect, nanoseconds added)`.
    pub jumps: Vec<(Time, i64)>,
}

impl Clock {
    /// The local reading at true time `t`; negative values are possible.
    pub fn local(&self, t: Time) -> i64 {
        let drift = (i128::from(t) * i128::from(self.drift_ppm)).div_euclid(1_000_000) as i64;
        let jumps: i64 = self.jumps.iter().filter(|(at, _)| *at <= t).map(|(_, d)| *d).sum();
        t.cast_signed() + self.offset + drift + jumps
    }

    /// The true time at which the local clock reaches `deadline`, seen from true time `now`: `now` if it already
    /// has, else `now + (deadline - local(now)) * 1e6 / (1e6 + drift) + 1`. Jumps between now and the deadline are
    /// ignored.
    pub fn to_true(&self, now: Time, deadline: i64) -> Time {
        let local = self.local(now);
        if deadline <= local {
            return now;
        }
        let span = i128::from(deadline - local) * 1_000_000 / (1_000_000 + i128::from(self.drift_ppm));
        now + span as Time + 1
    }
}
