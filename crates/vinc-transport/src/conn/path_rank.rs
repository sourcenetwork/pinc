//! Which path the session runs on: the rank of a usable path and the choice of the best one.
//!
//! Invariants: the order is total (the key ends with the slot, so no two paths tie), and a relay path no acknowledged
//! packet was sent on is behind every other path unless it is the active path and still answering.

use vinc_crypto::Provider;

use super::Connection;
use super::path::{PATH_IDLE_DIRECT, PTO_FALLBACK, Path, SWITCH_GAIN};
use crate::recovery::PathKind;
use crate::stream::StreamSource;

conn_impl! {
    /// The rank of path `i`, the least being the best: a relay path no acknowledged packet was sent on (a seen path is
    /// one that carried traffic; the round trip stamped on a path the session leaves is no evidence of that) is unseen
    /// and ranks behind every other, unless it is the active path and still answering (it is unseen too after
    /// `PTO_FALLBACK` probe timeouts in a row), then by cost, then by slot. A relay path nothing was measured on thus
    /// cannot take the session from the path it runs on, and the session leaves it for a seen one when it stops
    /// answering.
    ///
    /// What is not built: a failing active relay path is left for a seen path always, and for an unseen one only when
    /// that one ranks before it; a relay path that was seen and then stops delivering is not left by the transport's
    /// own timers, and a standby relay path takes over through `path_lost`, the host's `set_active` or the peer's data.
    // vertexia: a failing relay path is left only for a path that ranks before it; fail-over between relay paths is
    // vinc#625
    pub(super) fn rank(&self, i: usize, p: &Path) -> (bool, u64, usize) {
        let seen = u8::try_from(i).is_ok_and(|slot| self.rec.path_seen(slot));
        let unseen = p.info.kind == PathKind::Relay
            && !seen
            && (i != self.paths.active || self.rec.pto_count() >= PTO_FALLBACK);
        (unseen, p.cost(), i)
    }

    /// The best usable path: validated, and not a direct path that went quiet for 15 s.
    fn best_path(&self) -> Option<usize> {
        let now = self.life.clock;
        self.paths
            .iter()
            .filter(|(_, p)| {
                p.validated && !(p.info.kind == PathKind::Direct && now.saturating_sub(p.last_rx) > PATH_IDLE_DIRECT)
            })
            .min_by_key(|(i, p)| self.rank(*i, p))
            .map(|(i, _)| i)
    }

    /// Move to the cheapest usable path: at once from a relay, otherwise for a gain above 5 ms.
    pub(super) fn choose_path(&mut self) {
        let Some(best) = self.best_path() else { return };
        let (Some(b), cur) = (self.paths.get(best).copied(), self.paths.active().copied()) else { return };
        if cur.is_none_or(|c| c.gone || c.info.kind == PathKind::Relay || b.rtt.saturating_add(SWITCH_GAIN) < c.rtt) {
            self.switch_active(best);
            self.forget_gone();
        }
    }
}
