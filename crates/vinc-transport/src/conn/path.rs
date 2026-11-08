//! Paths: validation, migration, the active-path choice, idle re-challenges and path MTU state.
//!
//! A connection keeps at most `NP` paths. Each has its own validation state, [`AmpBudget`], datagram size, round
//! trip and last-heard time. A path is validated by an answered PATH_CHALLENGE (the previous challenge is accepted
//! too, so a retried challenge cannot strand the answer to the first). The client picks the active path by cost: the
//! round trip, plus one second for a relay, minus 3 ms for IPv6, and it switches only for a gain above 5 ms. The
//! server follows the highest-numbered non-probing packet that arrives on a validated path, so the two ends cannot
//! disagree and bounce.
//!
//! Invariants: the active path index always names a live slot; an unvalidated path never sends past its
//! amplification budget; a path challenge is retried a bounded number of times before the path is marked failed.

use vinc_crypto::Provider;
use vinc_security::{AmpBudget, Env};

use super::config::{MIN_MTU, PathId, PathInfo};
use super::event::Ev;
use super::{Connection, Phase};
use crate::recovery::{MS, PathKind, SECOND};
use crate::stream::StreamSource;

/// Challenge attempts before a path is declared failed.
const CHALLENGE_TRIES: u8 = 3;
/// A relay path costs this much more than a direct one when choosing the active path.
const RELAY_PENALTY: u64 = SECOND;
/// An IPv6 path costs this much less.
const V6_BONUS: u64 = 3 * MS;
/// A path replaces the active one only when it is cheaper by more than this.
const SWITCH_GAIN: u64 = 5 * MS;
/// An active path that stopped answering costs this much more.
const DEGRADED_PENALTY: u64 = 10 * SECOND;
/// A path with no data for this long is idle (the quiet re-challenge applies).
const IDLE_PATH: u64 = 20 * SECOND;
/// The first quiet re-challenge interval; it doubles up to [`REJOIN_MAX`].
const REJOIN_MIN: u64 = 20 * SECOND;
const REJOIN_MAX: u64 = 160 * SECOND;
/// The interval when the path is not quiet.
const REJOIN_BUSY: u64 = SECOND;
/// A path counts as quiet only if it was heard within this long.
const QUIET_HEARD: u64 = 75 * SECOND;
/// A path counts as quiet only if its round trip is under this.
const QUIET_RTT: u64 = 700 * MS;
/// The shortest wait for a challenge answer.
const CHALLENGE_RTO_MIN: u64 = 250 * MS;

/// How far a path got.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PathState {
    /// Seen, not yet proven reachable.
    Unvalidated,
    /// Reachable: a challenge was answered, or the handshake ran over it.
    Validated,
    /// A challenge went unanswered; the path is not used.
    Failed,
}

/// A PATH_CHALLENGE in progress.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Challenge {
    pub(crate) data: [u8; 8],
    pub(crate) sent_at: u64,
    pub(crate) tries: u8,
    pub(crate) retry_at: u64,
    pub(crate) send: bool,
    pub(crate) rejoin: bool,
}

/// Datagram size discovery state of one path.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Mtu {
    pub(crate) current: u16,
    pub(crate) ceiling: u16,
    pub(crate) inflight: Option<u16>,
    pub(crate) failures: u8,
    pub(crate) next_at: u64,
    pub(crate) started: bool,
    pub(crate) last_size: u16,
}

/// One network path.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Path {
    pub(crate) id: PathId,
    pub(crate) info: PathInfo,
    pub(crate) state: PathState,
    pub(crate) amp: AmpBudget,
    pub(crate) mtu: Mtu,
    pub(crate) challenge: Option<Challenge>,
    pub(crate) prev_challenge: Option<[u8; 8]>,
    pub(crate) response: Option<[u8; 8]>,
    pub(crate) echo: Option<u16>,
    pub(crate) rtt: Option<u64>,
    pub(crate) min_rtt: Option<u64>,
    pub(crate) last_heard: u64,
    pub(crate) last_data: u64,
    pub(crate) cid_seq: Option<u64>,
    pub(crate) rejoin_interval: u64,
    pub(crate) rejoin_at: Option<u64>,
    /// The path stopped answering when it was last active; it costs extra until a challenge on it is answered.
    pub(crate) suspect: bool,
}

impl Path {
    pub(crate) fn new(id: PathId, info: PathInfo, now: u64) -> Self {
        Self {
            id,
            info,
            state: PathState::Unvalidated,
            amp: AmpBudget::new(),
            mtu: Mtu {
                current: MIN_MTU,
                ceiling: u16::MAX,
                inflight: None,
                failures: 0,
                next_at: 0,
                started: false,
                last_size: 0,
            },
            challenge: None,
            prev_challenge: None,
            response: None,
            echo: None,
            rtt: None,
            min_rtt: None,
            last_heard: now,
            last_data: now,
            cid_seq: None,
            rejoin_interval: REJOIN_MIN,
            rejoin_at: None,
            suspect: false,
        }
    }

    pub(crate) fn validated(&self) -> bool {
        self.state == PathState::Validated
    }

    /// The cost used to rank paths; `None` while the round trip is unknown.
    fn cost(&self) -> Option<u64> {
        // The minimum round trip is the path's own; the smoothed one of a busy path includes queueing.
        let mut c = self.min_rtt.or(self.rtt)?;
        if self.info.kind == PathKind::Relay {
            c = c.saturating_add(RELAY_PENALTY);
        }
        if self.info.v6 {
            c = c.saturating_sub(V6_BONUS);
        }
        if self.suspect {
            c = c.saturating_add(DEGRADED_PENALTY);
        }
        Some(c)
    }
}

/// Why a path call was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathError {
    /// The connection already tracks as many paths as it can and none can be dropped.
    TooMany,
    /// The path is not known to the connection.
    Unknown,
    /// The path has not been validated.
    NotValidated,
    /// The path is the active one.
    Active,
    /// The peer disabled active migration in its transport parameters.
    MigrationDisabled,
}

impl core::fmt::Display for PathError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::TooMany => "too many paths",
            Self::Unknown => "unknown path",
            Self::NotValidated => "the path is not validated",
            Self::Active => "the path is the active one",
            Self::MigrationDisabled => "the peer disabled active migration",
        })
    }
}

impl core::error::Error for PathError {}

/// The path table.
#[derive(Debug)]
pub(crate) struct Paths<const NP: usize> {
    pub(crate) slots: [Option<Path>; NP],
    pub(crate) active: usize,
}

impl<const NP: usize> Paths<NP> {
    pub(crate) const fn new() -> Self {
        const { assert!(NP >= 1 && NP <= crate::recovery::MAX_PATHS) };
        Self {
            slots: [None; NP],
            active: 0,
        }
    }

    pub(crate) fn find(&self, id: PathId) -> Option<usize> {
        self.slots.iter().position(|s| s.is_some_and(|p| p.id == id))
    }

    pub(crate) fn get(&self, i: usize) -> Option<&Path> {
        self.slots.get(i)?.as_ref()
    }

    pub(crate) fn get_mut(&mut self, i: usize) -> Option<&mut Path> {
        self.slots.get_mut(i)?.as_mut()
    }

    pub(crate) fn active(&self) -> Option<&Path> {
        self.get(self.active)
    }

    pub(crate) fn active_mut(&mut self) -> Option<&mut Path> {
        let a = self.active;
        self.get_mut(a)
    }

    pub(crate) fn iter(&self) -> impl Iterator<Item = (usize, &Path)> {
        self.slots
            .iter()
            .enumerate()
            .filter_map(|(i, s)| s.as_ref().map(|p| (i, p)))
    }
}

conn_impl! {
    /// Add a path the endpoint knows about, or update what it knows about one the connection already tracks.
    /// A new path is validated with a PATH_CHALLENGE once the handshake is done.
    ///
    /// # Errors
    /// [`PathError::TooMany`] if the table is full and no unused path can make room.
    pub fn add_path(&mut self, env: &mut Env<'_, P>, id: PathId, info: PathInfo) -> Result<(), PathError> {
        if let Some(i) = self.paths.find(id) {
            if let Some(p) = self.paths.get_mut(i) {
                p.info = info;
            }
            self.sync_kind(i);
            return Ok(());
        }
        let i = self.new_path_slot(id, info, env.now).ok_or(PathError::TooMany)?;
        // The endpoint chose this address itself, so the amplification limit that guards against spoofed sources
        // does not apply to challenging it.
        if let Some(p) = self.paths.get_mut(i) {
            p.amp.validate();
        }
        if self.phase == Phase::Connected {
            self.start_challenge(env, i, false);
        }
        Ok(())
    }

    /// Challenge `id` again now, to refresh its round trip or check that it still works.
    ///
    /// # Errors
    /// [`PathError::Unknown`] if the path is not tracked.
    pub fn probe(&mut self, env: &mut Env<'_, P>, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        self.start_challenge(env, i, true);
        Ok(())
    }

    /// Make a validated path the active one. Congestion control restarts, except from one relay to another.
    ///
    /// # Errors
    /// [`PathError::Unknown`] or [`PathError::NotValidated`].
    pub fn set_active(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if !self.paths.get(i).is_some_and(Path::validated) {
            return Err(PathError::NotValidated);
        }
        self.switch_active(i);
        Ok(())
    }

    /// Stop tracking a path that is not the active one; its peer connection id is retired.
    ///
    /// # Errors
    /// [`PathError::Unknown`], or [`PathError::Active`] for the active path.
    pub fn remove_path(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if i == self.paths.active {
            return Err(PathError::Active);
        }
        if self.migrate_to == Some(i) {
            self.migrate_to = None;
        }
        self.release_path(i);
        Ok(())
    }

    /// The path packets leave on, if any.
    pub fn active_path(&self) -> Option<PathId> {
        self.paths.active().map(|p| p.id)
    }

    /// The datagram size of a path.
    pub fn path_mtu(&self, id: PathId) -> Option<u16> {
        self.paths.get(self.paths.find(id)?).map(|p| p.mtu.current)
    }

    /// The round trip of a path in nanoseconds, if measured.
    pub fn path_rtt(&self, id: PathId) -> Option<u64> {
        let i = self.paths.find(id)?;
        if i == self.paths.active && self.rec.rtt().has_sample() {
            return Some(self.rec.rtt().smoothed());
        }
        self.paths.get(i).and_then(|p| p.rtt)
    }

    /// Whether a path is validated.
    pub fn path_validated(&self, id: PathId) -> bool {
        self.paths.find(id).and_then(|i| self.paths.get(i)).is_some_and(Path::validated)
    }

    pub(super) fn sync_kind(&mut self, i: usize) {
        let kind = self.paths.get(i).map_or(PathKind::Direct, |p| p.info.kind);
        // The slot index is below `NP <= MAX_PATHS`, so the recovery table has room for it.
        let _ = u8::try_from(i).map(|s| self.rec.set_path_kind(s, kind));
    }

    /// Track a new path, evicting a failed or unvalidated standby path if the table is full.
    pub(super) fn new_path_slot(&mut self, id: PathId, info: PathInfo, now: u64) -> Option<usize> {
        let active = self.paths.active;
        let free = self
            .paths
            .slots
            .iter()
            .position(Option::is_none)
            .or_else(|| {
                self.paths
                    .iter()
                    .find(|(i, p)| *i != active && p.state != PathState::Validated)
                    .map(|(i, _)| i)
            })?;
        self.release_path(free);
        let mut path = Path::new(id, info, now);
        path.mtu.started = self.phase == Phase::Connected;
        path.cid_seq = u8::try_from(free).ok().and_then(|u| self.cids.claim_remote(u));
        if let Some(slot) = self.paths.slots.get_mut(free) {
            *slot = Some(path);
        }
        self.sync_kind(free);
        Some(free)
    }

    /// Give back what a path held: its peer connection id is retired so the next path gets a fresh one.
    fn release_path(&mut self, i: usize) {
        if let Some(p) = self.paths.slots.get_mut(i).and_then(Option::take)
            && let Some(seq) = p.cid_seq
        {
            self.cids.retire_remote(seq);
        }
    }

    /// Start a PATH_CHALLENGE on path `i`. A path that is already validated keeps working while it is re-checked.
    pub(super) fn start_challenge(&mut self, env: &mut Env<'_, P>, i: usize, rejoin: bool) {
        let Ok(data) = env.random::<8>() else { return };
        let now = env.now;
        let Some(p) = self.paths.get_mut(i) else { return };
        p.prev_challenge = p.challenge.map(|c| c.data);
        p.challenge = Some(Challenge {
            data,
            sent_at: 0,
            tries: 0,
            retry_at: now,
            send: true,
            rejoin,
        });
    }

    /// A PATH_RESPONSE arrived on path `i`.
    pub(super) fn on_path_response(&mut self, i: usize, data: [u8; 8], now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        let matches = p.challenge.is_some_and(|c| c.data == data) || p.prev_challenge == Some(data);
        if !matches {
            return;
        }
        let was = p.state;
        let rtt = p.challenge.filter(|c| c.sent_at != 0 || c.tries > 0).map(|c| now.saturating_sub(c.sent_at));
        let rejoin = p.challenge.is_some_and(|c| c.rejoin);
        p.challenge = None;
        p.prev_challenge = None;
        p.suspect = false;
        p.state = PathState::Validated;
        p.amp.validate();
        p.last_heard = now;
        if let Some(r) = rtt.filter(|r| *r > 0) {
            p.rtt = Some(r);
            p.min_rtt = Some(p.min_rtt.map_or(r, |m| m.min(r)));
        }
        if rejoin {
            p.rejoin_interval = (p.rejoin_interval.saturating_mul(2)).min(REJOIN_MAX);
            p.rejoin_at = Some(now.saturating_add(p.rejoin_interval));
        }
        let id = p.id;
        if was != PathState::Validated {
            self.events.push(Ev::PathValidated(id));
        }
        if self.migrate_to == Some(i) {
            self.migrate_to = None;
            if i != self.paths.active {
                self.switch_active(i);
            }
        } else if self.client {
            self.evaluate_paths();
        }
    }

    /// Make slot `i` the active path.
    pub(super) fn switch_active(&mut self, i: usize) {
        if i == self.paths.active || self.paths.get(i).is_none() {
            return;
        }
        let degraded = self.rec.pto_count() >= 3;
        let sample = self.rec.rtt().has_sample().then(|| self.rec.rtt().smoothed());
        if let Some(old) = self.paths.active_mut() {
            old.rtt = sample.or(old.rtt);
            old.suspect |= degraded;
        }
        self.paths.active = i;
        if let Ok(slot) = u8::try_from(i) {
            // The index is below `NP <= MAX_PATHS`, so the switch cannot be refused.
            let _ = self.rec.switch_path(slot);
        }
        if let Some(p) = self.paths.get(i) {
            let mtu = u64::from(p.mtu.current);
            self.rec.set_max_datagram_size(mtu);
        }
        self.rx.set_min_rtt(self.rec.rtt().min_rtt());
    }

    /// Client side: move to a clearly cheaper validated path.
    ///
    /// vertexia: scans every path on each validation, acknowledgement and timeout, which is at most `NP` (default 4)
    /// comparisons; a cached best path would only matter with many paths.
    pub(super) fn evaluate_paths(&mut self) {
        let active = self.paths.active;
        let degraded = self.rec.pto_count() >= 3;
        let cost_of = |i: usize, p: &Path, rec_rtt: Option<u64>| {
            let mut q = *p;
            if i == active {
                // Prefer the path's own challenge round trip; a busy path's samples carry queueing and ack delay.
                q.min_rtt = p.min_rtt.or(rec_rtt);
            }
            q.cost().map(|c| if i == active && degraded { c.saturating_add(DEGRADED_PENALTY) } else { c })
        };
        let rec_rtt = self.rec.rtt().min_rtt();
        let Some(active_cost) = self.paths.get(active).and_then(|p| cost_of(active, p, rec_rtt)) else {
            return;
        };
        let best = self
            .paths
            .iter()
            .filter(|(i, p)| *i != active && p.validated())
            .filter_map(|(i, p)| cost_of(i, p, rec_rtt).map(|c| (c, i)))
            .min();
        if let Some((cost, i)) = best
            && cost.saturating_add(SWITCH_GAIN) < active_cost
        {
            self.switch_active(i);
        }
    }

    /// Whether a quiet re-challenge may use the long interval for path `p`.
    fn quiet_ok(&self, p: &Path, now: u64) -> bool {
        now.saturating_sub(p.last_data) >= IDLE_PATH
            && self.rec.pto_count() == 0
            && now.saturating_sub(p.last_heard) <= QUIET_HEARD
            && p.rtt.is_some_and(|r| r < QUIET_RTT)
    }

    /// The earliest path timer: a challenge retry or a re-challenge.
    pub(super) fn path_deadline(&self) -> Option<u64> {
        self.paths
            .iter()
            .flat_map(|(_, p)| {
                let retry = p.challenge.filter(|c| !c.send).map(|c| c.retry_at);
                let rejoin = if self.cfg.thin && p.validated() && p.challenge.is_none() { p.rejoin_at } else { None };
                [retry, rejoin]
            })
            .flatten()
            .min()
    }

    /// Retry challenges, fail paths and start re-challenges that are due.
    pub(super) fn on_path_timers(&mut self, env: &mut Env<'_, P>) {
        let now = env.now;
        for i in 0..NP {
            let Some(p) = self.paths.get(i).copied() else { continue };
            if let Some(c) = p.challenge
                && !c.send
                && c.retry_at <= now
            {
                if c.tries >= CHALLENGE_TRIES {
                    self.fail_path(i);
                } else if let Some(pm) = self.paths.get_mut(i)
                    && let Some(ch) = pm.challenge.as_mut()
                {
                    ch.send = true;
                }
                continue;
            }
            let idle_direct = p.info.kind == PathKind::Direct
                && i != self.paths.active
                && p.validated()
                && p.challenge.is_none()
                && now.saturating_sub(p.last_data) >= IDLE_PATH;
            if self.cfg.thin && idle_direct {
                let interval = if self.quiet_ok(&p, now) { p.rejoin_interval } else { REJOIN_BUSY };
                let due = p.rejoin_at.unwrap_or_else(|| p.last_data.saturating_add(interval));
                if due <= now {
                    self.start_challenge(env, i, true);
                    if let Some(pm) = self.paths.get_mut(i) {
                        pm.rejoin_at = Some(now.saturating_add(interval));
                    }
                }
            }
        }
    }

    fn fail_path(&mut self, i: usize) {
        let Some(p) = self.paths.get_mut(i) else { return };
        let id = p.id;
        let was_validated = p.state == PathState::Validated;
        p.challenge = None;
        p.state = PathState::Failed;
        self.events.push(Ev::PathFailed(id));
        if self.migrate_to == Some(i) {
            self.migrate_to = None;
        }
        if was_validated && i != self.paths.active {
            // A standby path that stopped answering is dropped; its connection id is retired for reuse.
            self.release_path(i);
        }
    }

    /// The retry delay of a challenge on path `i` after `tries` attempts.
    pub(super) fn challenge_rto(&self, i: usize, tries: u8) -> u64 {
        let base = self
            .paths
            .get(i)
            .and_then(|p| p.rtt)
            .map_or(CHALLENGE_RTO_MIN.max(self.rec.pto_duration()), |r| (r.saturating_mul(3)).max(CHALLENGE_RTO_MIN));
        base.saturating_mul(1u64 << tries.min(4))
    }
}
