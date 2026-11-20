//! The path timers: idle-out of a quiet direct path, the probes that fall due, and the fall back to a relay path after
//! probe timeouts.
//!
//! Invariants: a timer moves the active path only onto a validated path, and falls back only onto a validated relay
//! path whose address is not gone; every probe it fires belongs to an unvalidated path with a probe left; the re-join
//! cadence is set once per abandonment.

use pinc_crypto::Provider;
use pinc_security::Env;

use super::Connection;
use super::path::{PATH_IDLE_DIRECT, RJ_THIN_GAP};
use crate::recovery::{MS, PathKind, SECOND};
use crate::stream::StreamSource;

/// The largest gap between probes to a new path.
const PROBE_CAP: u64 = 2 * SECOND;
/// The gap between challenges to a path abandoned after probe timeouts.
const REJOIN_GAP: u64 = 60 * MS;
/// The number of re-join challenges (at [`REJOIN_GAP`], 6 s).
const REJOIN_PROBES: u64 = 100;
/// The cadence of the re-challenge of an idled-out direct path on a thin node.
const RJ_RETRY: u64 = 20 * SECOND;
/// The longest back-off of that cadence.
const RJ_IDLE_MAX: u64 = 160 * SECOND;
/// A round trip at least this long is a slow path.
const SLOW_RTT: u64 = 250 * MS;

conn_impl! {
    /// The earliest path timer: a probe that is due, or a direct path going quiet.
    pub(super) fn path_deadline(&self) -> Option<u64> {
        self.paths
            .iter()
            .filter_map(|(_, p)| {
                if !p.validated {
                    (p.probes_left > 0).then_some(p.next_probe)
                } else if p.info.kind == PathKind::Direct && p.last_rx != 0 {
                    Some(p.last_rx.saturating_add(PATH_IDLE_DIRECT).saturating_add(1))
                } else {
                    None
                }
            })
            .min()
    }

    /// Idle-out, relay escape and the probes that are due.
    pub(super) fn on_path_timers(&mut self, env: &mut Env<'_, P>) {
        let now = env.now;
        self.life.clock = now;
        for i in 0..NP {
            let Some(p) = self.paths.get(i).copied() else { continue };
            if p.validated && p.info.kind == PathKind::Direct && p.last_rx != 0 && now.saturating_sub(p.last_rx) > PATH_IDLE_DIRECT {
                self.idle_out(env, i);
            }
        }
        if self.active_open_to_move() {
            self.choose_path();
        }
        for i in 0..NP {
            let Some(p) = self.paths.get(i).copied() else { continue };
            if !p.validated && p.probes_left > 0 && now >= p.next_probe {
                self.fire_probe(env, i);
            }
        }
    }

    /// A validated direct path was silent for 15 s: it is no longer validated; a thin node keeps re-challenging it on
    /// a slow cadence, and the active path moves to a relay.
    fn idle_out(&mut self, env: &mut Env<'_, P>, i: usize) {
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

    /// Send the probe of path `i` that is due and plan the next one. A re-join challenge of a thin session waits for
    /// the floor the endpoint set, and is reported to it once it leaves.
    fn fire_probe(&mut self, env: &mut Env<'_, P>, i: usize) {
        let now = env.now;
        let srtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
        let slow = self.rec.rtt().min_rtt().unwrap_or(0) >= SLOW_RTT;
        let quiet = self.quiet_ok(now);
        let thin = self.thin_session();
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.rejoin && thin {
            if now < p.rj_floor {
                p.next_probe = p.rj_floor;
                return;
            }
            p.rj_fired = true;
        }
        p.probes_left -= 1;
        p.next_probe = now.saturating_add(p.probe_gap);
        p.probe_gap = if p.rejoin {
            if slow { p.probe_gap.saturating_mul(2).max(srtt) } else { REJOIN_GAP.max(srtt / 2) }
        } else {
            p.probe_gap.saturating_mul(2).min(PROBE_CAP)
        };
        if p.rejoin && p.probes_left == 0 && p.info.kind == PathKind::Direct && thin {
            p.probes_left = 1;
            if quiet {
                p.rj_back = RJ_IDLE_MAX.min(RJ_RETRY.max(p.rj_back.saturating_mul(2)));
                p.next_probe = now.saturating_add(p.rj_back);
            } else {
                p.rj_back = 0;
                p.next_probe = now.saturating_add(RJ_RETRY);
            }
        }
        p.send_challenge = p.challenge.is_some();
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
        if p.info.kind != PathKind::Direct {
            return;
        }
        // Only a validated path has a validation to drop and a re-join to set up; every direct path falls back.
        if p.validated {
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
        }
        self.relay_fallback();
    }

    /// Move the active path to the newest relay path, if the connection has one.
    fn relay_fallback(&mut self) {
        let relay = self
            .paths
            .iter()
            .filter(|(_, p)| p.info.kind == PathKind::Relay && p.validated && !p.gone)
            .map(|(i, _)| i)
            .last();
        if let Some(r) = relay {
            self.switch_active(r);
        }
    }
}
