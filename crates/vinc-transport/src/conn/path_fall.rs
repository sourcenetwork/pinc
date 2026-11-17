//! The ways the active path is given up: a validated direct path that went quiet, a direct path that failed three
//! probe timeouts in a row, and the fall-back to a relay path both lead to.
//!
//! Invariants: the fall-back moves the session only to a relay path the connection tracks, the validated one of least
//! rank first (see `rank`: a seen path before an unseen one, then by cost and slot), else the last relay path. A relay
//! path is validated from the moment it is tracked, so one nothing was seen on is taken whenever no seen one exists.

use vinc_crypto::Provider;
use vinc_security::Env;

use super::Connection;
use super::path::{REJOIN_GAP, REJOIN_PROBES, RJ_IDLE_MAX, RJ_RETRY, RJ_THIN_GAP, SLOW_RTT};
use crate::recovery::{PathKind, SECOND};
use crate::stream::StreamSource;

conn_impl! {
    /// A validated direct path was silent for 15 s: it is no longer validated; a thin node keeps re-challenging it on
    /// a slow cadence, and the active path moves to a relay.
    pub(super) fn idle_out(&mut self, env: &mut Env<'_, P>, i: usize) {
        let now = env.now;
        if let Some(p) = self.paths.get_mut(i) {
            p.validated = false;
        }
        let quiet = self.quiet_ok(now);
        let thin = self.thin_session();
        if thin && self.paths.get(i).is_some_and(|p| p.probes_left == 0) {
            self.set_challenge(env, i);
            if let Some(p) = self.paths.get_mut(i) {
                p.rejoin = true;
                p.probes_left = 1;
                p.probe_gap = RJ_RETRY;
                if quiet {
                    p.rj_back = RJ_IDLE_MAX.min(RJ_RETRY.max(p.rj_back.saturating_mul(2)));
                    p.next_probe = now.saturating_add(p.rj_back);
                } else {
                    p.rj_back = 0;
                    p.next_probe = now.saturating_add(RJ_THIN_GAP);
                }
            }
        }
        if i == self.paths.active {
            self.relay_fallback();
        }
    }

    /// The active direct path failed three probe timeouts in a row: it is no longer validated and is challenged on
    /// the re-join cadence, and the connection falls back to a relay path if it has one.
    pub(super) fn fail_over(&mut self, env: &mut Env<'_, P>) {
        let now = env.now;
        let i = self.paths.active;
        let srtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
        let slow = self.rec.rtt().min_rtt().unwrap_or(0) >= SLOW_RTT;
        let thin = self.thin_session();
        let node = self.rec.peak_rtt();
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.info.kind != PathKind::Direct || !p.validated {
            return;
        }
        p.validated = false;
        // A re-join already running is not set up again.
        if !(p.rejoin && p.probes_left > 0) {
            let mut gap = REJOIN_GAP.max(if slow { srtt } else { srtt / 2 });
            let mut probes = 4.max(REJOIN_PROBES * REJOIN_GAP / gap);
            if thin {
                gap = gap.max(RJ_THIN_GAP).max(srtt).max(node);
                probes = 4.max(12 * SECOND / gap);
            }
            p.probes_left = u32::try_from(probes).unwrap_or(u32::MAX);
            p.probe_gap = gap;
            p.next_probe = now.saturating_add(gap);
            p.rejoin = true;
            self.set_challenge(env, i);
        }
        self.relay_fallback();
    }

    /// Move the active path to the validated relay path of least rank, else to the last relay path, if the connection
    /// has one.
    fn relay_fallback(&mut self) {
        let validated = self
            .paths
            .iter()
            .filter(|(_, p)| p.info.kind == PathKind::Relay && p.validated)
            .min_by_key(|(i, p)| self.rank(*i, p))
            .map(|(i, _)| i);
        let last = self.paths.iter().filter(|(_, p)| p.info.kind == PathKind::Relay).map(|(i, _)| i).last();
        if let Some(r) = validated.or(last) {
            self.switch_active(r);
        }
    }
}
