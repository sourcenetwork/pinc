//! Paths: validation, following the peer, the active-path choice, the idle rules and path MTU state.
//!
//! A connection keeps at most `NP` paths. Each has its own validated flag, [`AmpBudget`], datagram size, round trip
//! and last-heard time. A path is validated by an answered PATH_CHALLENGE (the previous challenge is
//! accepted too, so a replaced challenge cannot strand the answer to the first); the round trip it gives is the time
//! since the challenge the response echoes was first sent, kept in a small table of the outstanding challenges, so
//! challenges repeated faster than the round trip cannot under-read it. Challenges and responses are small and unpadded: the datagram size is
//! found by the separate probe.
//!
//! Both ends follow the peer at once: the highest-numbered packet that carries STREAM, DATAGRAM or WAKE data moves
//! the active path to the path it came from, and a new UDP path is challenged in parallel (a new path gets three
//! times what it sent us until its challenge is answered). The active path is chosen by cost: the smoothed round
//! trip of the path, plus one second for a relay, minus 3 ms for IPv6; a validated UDP path that was silent for 15 s
//! is left out; from a relay the connection moves at once, otherwise only for a gain above 5 ms. After three
//! probe timeouts in a row on a direct path the path is dropped as validated, challenged on the re-join cadence, and
//! the connection falls back to a relay path if it has one.
//!
//! A challenge sent to a new or abandoned path follows a cadence that depends on why: a new path is probed 9 times
//! from `max(33.3 ms, srtt / 8)`, doubling up to 2 s; a path abandoned after probe timeouts is probed at a flat gap
//! for about 12 s; on a thin node an idled-out direct path is re-challenged every 20 s, backing off to 160 s while the
//! session is quiet. A path that never answers stays unvalidated and is only removed when its slot is needed.
//!
//! Invariants: the active path index always names a live slot; an unvalidated path never sends past its
//! amplification budget; a path is validated only by an answer to a challenge sent to it.

use vinc_crypto::Provider;
use vinc_security::{AmpBudget, ConnId, Env};

use super::config::{MIN_MTU, PathId, PathInfo};
use super::event::Ev;
use super::mtu::Jumbo;
use super::{Connection, Phase};
use crate::recovery::{MS, PathKind, SECOND};
use crate::stream::StreamSource;

/// Probe timeouts in a row on a direct path after which the connection falls back.
pub(crate) const PTO_FALLBACK: u32 = 3;
/// Probes sent to a new path.
const NAT_PROBES: u32 = 9;
/// The first gap between probes to a new path.
const PROBE_BASE: u64 = 33_300_000;
/// The largest gap between probes to a new path.
const PROBE_CAP: u64 = 2 * SECOND;
/// The gap between challenges to a path abandoned after probe timeouts.
const REJOIN_GAP: u64 = 60 * MS;
/// The number of re-join challenges (at [`REJOIN_GAP`], 6 s).
const REJOIN_PROBES: u64 = 100;
/// The shortest gap between re-join challenges on a thin node, and the shortest wait for a migration challenge.
pub(crate) const RJ_THIN_GAP: u64 = SECOND;
/// The cadence of the re-challenge of an idled-out direct path on a thin node.
const RJ_RETRY: u64 = 20 * SECOND;
/// The longest back-off of that cadence.
const RJ_IDLE_MAX: u64 = 160 * SECOND;
/// A relay path costs this much more than a direct one when choosing the active path.
const RELAY_PENALTY: u64 = SECOND;
/// An IPv6 path costs this much less.
const V6_BONUS: u64 = 3 * MS;
/// A path replaces the active one only when it is cheaper by more than this.
const SWITCH_GAIN: u64 = 5 * MS;
/// A validated direct path silent for longer than this is no longer validated.
pub(crate) const PATH_IDLE_DIRECT: u64 = 15 * SECOND;
/// A session with no application data for this long is idle.
const ACTIVE_KEEP: u64 = 20 * SECOND;
/// A session is quiet only while its round trip is under this.
const QUIET_RTT: u64 = 700 * MS;
/// A session is quiet only if it heard the peer within this long.
const QUIET_RX: u64 = 75 * SECOND;
/// A round trip at least this long is a slow path.
const SLOW_RTT: u64 = 250 * MS;
/// Outstanding challenges kept per path with their send times.
const CHALLENGES: usize = 4;
/// Data larger than this is more than a control message.
pub(crate) const CTRL_SMALL: usize = 72;

/// Datagram size discovery state of one path.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Mtu {
    pub(crate) current: u16,
    pub(crate) inflight: Option<u16>,
    /// The main probe was sent since the last path event.
    pub(crate) probed: bool,
    pub(crate) jumbo: Jumbo,
    /// A lost probe waits until this time (or a path event).
    pub(crate) retry_at: u64,
    pub(crate) started: bool,
    /// The packet number of the newest packet above the minimum size sent on the path.
    pub(crate) last_big: Option<u64>,
    /// The newest full-size packet the peer acknowledged.
    pub(crate) big_acked: Option<u64>,
    /// The newest full-size packet sent before the last probe-timeout PING.
    pub(crate) ping_big: Option<u64>,
    /// A black-hole suspicion: that full-size packet, and the time (one round trip after the PING was acknowledged)
    /// at which it is still unacknowledged evidence.
    pub(crate) suspect: Option<(u64, u64)>,
}

/// One network path.
#[derive(Debug, Clone, Copy)]
#[allow(clippy::struct_excessive_bools, reason = "independent facts about one path")]
pub(crate) struct Path {
    pub(crate) id: PathId,
    pub(crate) info: PathInfo,
    pub(crate) validated: bool,
    pub(crate) amp: AmpBudget,
    pub(crate) mtu: Mtu,
    /// The challenge outstanding on this path.
    pub(crate) challenge: Option<[u8; 8]>,
    /// The newest challenges (the outstanding one and those it replaced) with the time each was first sent, 0 while
    /// unsent; the oldest entry is overwritten.
    pub(crate) sent: [Option<([u8; 8], u64)>; CHALLENGES],
    sent_next: usize,
    /// When the outstanding migration challenge was sent.
    pub(crate) challenge_at: u64,
    /// The challenge is waiting for a packet.
    pub(crate) send_challenge: bool,
    pub(crate) response: Option<[u8; 8]>,
    pub(crate) echo: Option<u16>,
    pub(crate) probes_left: u32,
    pub(crate) next_probe: u64,
    pub(crate) probe_gap: u64,
    pub(crate) rejoin: bool,
    pub(crate) rj_back: u64,
    /// The smoothed round trip of the path, 0 while unknown.
    pub(crate) rtt: u64,
    /// When a datagram last arrived on this path, 0 for never.
    pub(crate) last_rx: u64,
    /// The peer's id this path sends with, and its index.
    pub(crate) dcid: Option<ConnId>,
    /// The local address of the path is gone (the host's interface moved): nothing can use it again.
    pub(crate) gone: bool,
}

impl Path {
    pub(crate) fn new(id: PathId, info: PathInfo) -> Self {
        Self {
            id,
            info,
            validated: false,
            amp: AmpBudget::new(),
            mtu: Mtu {
                current: MIN_MTU,
                inflight: None,
                probed: false,
                jumbo: Jumbo::Untried,
                retry_at: 0,
                started: false,
                last_big: None,
                big_acked: None,
                ping_big: None,
                suspect: None,
            },
            challenge: None,
            sent: [None; CHALLENGES],
            sent_next: 0,
            challenge_at: 0,
            send_challenge: false,
            response: None,
            echo: None,
            probes_left: 0,
            next_probe: 0,
            probe_gap: PROBE_BASE,
            rejoin: false,
            rj_back: 0,
            rtt: 0,
            last_rx: 0,
            dcid: None,
            gone: false,
        }
    }

    /// Record a fresh challenge, keeping the ones it replaces.
    fn push_challenge(&mut self, data: [u8; 8]) {
        self.challenge = Some(data);
        if let Some(s) = self.sent.get_mut(self.sent_next) {
            *s = Some((data, 0));
        }
        self.sent_next = (self.sent_next + 1) % CHALLENGES;
    }

    /// Note that the challenge `data` left on the path at `now`; only the first send counts.
    pub(crate) fn challenge_sent(&mut self, data: [u8; 8], now: u64) {
        if let Some((_, at)) = self.sent.iter_mut().flatten().find(|(d, _)| *d == data)
            && *at == 0
        {
            *at = now;
        }
    }

    /// The time the challenge `data` was first sent, if it is one of the outstanding ones.
    fn challenge_time(&self, data: [u8; 8]) -> Option<u64> {
        self.sent.iter().flatten().find(|(d, _)| *d == data).map(|(_, at)| *at)
    }

    /// The cost used to rank paths.
    fn cost(&self) -> u64 {
        let mut c = self.rtt;
        if self.info.kind == PathKind::Relay {
            c = c.saturating_add(RELAY_PENALTY);
        }
        if self.info.v6 {
            c = c.saturating_sub(V6_BONUS);
        }
        c
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
}

impl core::fmt::Display for PathError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::TooMany => "too many paths",
            Self::Unknown => "unknown path",
            Self::NotValidated => "the path is not validated",
            Self::Active => "the path is the active one",
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
    /// A new path is probed with PATH_CHALLENGE once the handshake is done.
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
            self.start_punch(env, i);
        }
        Ok(())
    }

    /// Add the path `id`, or start its 9-probe punch over again if the connection already tracks it. Used to re-punch
    /// a candidate path that did not validate.
    ///
    /// # Errors
    /// As [`add_path`](Self::add_path).
    pub fn punch(&mut self, env: &mut Env<'_, P>, id: PathId, info: PathInfo) -> Result<(), PathError> {
        let known = self.paths.find(id).is_some();
        self.add_path(env, id, info)?;
        if known && self.phase == Phase::Connected && let Some(i) = self.paths.find(id) && !self.paths.get(i).is_some_and(|p| p.validated) {
            self.start_punch(env, i);
        }
        Ok(())
    }

    /// Whether the active path runs through a relay.
    pub fn active_is_relay(&self) -> bool {
        self.paths.active().is_some_and(|p| p.info.kind == PathKind::Relay)
    }

    /// When a datagram last arrived on a path, in the connection's clock; 0 before the first.
    pub fn path_last_rx(&self, id: PathId) -> Option<u64> {
        let i = self.paths.find(id)?;
        self.paths.get(i).map(|p| p.last_rx)
    }

    /// Challenge `id` again now, to refresh its round trip or check that it still works.
    ///
    /// # Errors
    /// [`PathError::Unknown`] if the path is not tracked.
    pub fn probe(&mut self, env: &mut Env<'_, P>, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        self.queue_challenge(env, i);
        Ok(())
    }

    /// Make a validated path the active one. Congestion control restarts, except from one relay to another.
    ///
    /// # Errors
    /// [`PathError::Unknown`] or [`PathError::NotValidated`].
    pub fn set_active(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if !self.paths.get(i).is_some_and(|p| p.validated) {
            return Err(PathError::NotValidated);
        }
        self.switch_active(i);
        Ok(())
    }

    /// Stop tracking a path that is not the active one.
    ///
    /// # Errors
    /// [`PathError::Unknown`], or [`PathError::Active`] for the active path.
    pub fn remove_path(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if i == self.paths.active {
            return Err(PathError::Active);
        }
        if let Some(s) = self.paths.slots.get_mut(i) {
            *s = None;
        }
        Ok(())
    }

    /// Tell the connection the local address of path `id` is gone (the host's interface moved). The path is no longer
    /// usable: the connection leaves it for the best validated path at once, or as soon as one validates, and then
    /// forgets it.
    ///
    /// # Errors
    /// [`PathError::Unknown`] if the path is not tracked.
    pub fn path_lost(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if let Some(p) = self.paths.get_mut(i) {
            p.gone = true;
            p.validated = false;
        }
        self.choose_path();
        self.forget_gone();
        Ok(())
    }

    /// Stop tracking the paths whose local address is gone, except the active one.
    pub(super) fn forget_gone(&mut self) {
        let active = self.paths.active;
        for (i, s) in self.paths.slots.iter_mut().enumerate() {
            if i != active && s.as_ref().is_some_and(|p| p.gone) {
                *s = None;
            }
        }
    }

    /// The path packets leave on, if any.
    pub fn active_path(&self) -> Option<PathId> {
        self.paths.active().map(|p| p.id)
    }

    /// The datagram size of a path.
    pub fn path_mtu(&self, id: PathId) -> Option<u16> {
        self.paths.get(self.paths.find(id)?).map(|p| p.mtu.current)
    }

    /// The smoothed round trip of a path in nanoseconds, if measured.
    pub fn path_rtt(&self, id: PathId) -> Option<u64> {
        let i = self.paths.find(id)?;
        self.paths.get(i).map(|p| p.rtt).filter(|r| *r > 0)
    }

    /// Whether a path is validated.
    pub fn path_validated(&self, id: PathId) -> bool {
        self.paths.find(id).and_then(|i| self.paths.get(i)).is_some_and(|p| p.validated)
    }

    pub(super) fn sync_kind(&mut self, i: usize) {
        let kind = self.paths.get(i).map_or(PathKind::Direct, |p| p.info.kind);
        // The slot index is below `NP <= MAX_PATHS`, so the recovery table has room for it.
        let _ = u8::try_from(i).map(|s| self.rec.set_path_kind(s, kind));
    }

    /// Track a new path, evicting an unvalidated standby path if the table is full.
    pub(super) fn new_path_slot(&mut self, id: PathId, info: PathInfo, now: u64) -> Option<usize> {
        let active = self.paths.active;
        let free = self
            .paths
            .slots
            .iter()
            .position(Option::is_none)
            .or_else(|| self.paths.iter().find(|(i, p)| *i != active && !p.validated).map(|(i, _)| i))?;
        let mut path = Path::new(id, info);
        path.mtu.started = self.phase == Phase::Connected;
        path.last_rx = now;
        if let Some(slot) = self.paths.slots.get_mut(free) {
            *slot = Some(path);
        }
        self.sync_kind(free);
        Some(free)
    }

    /// Put a fresh random challenge on path `i`, keeping the one it replaces, without sending it yet.
    pub(super) fn set_challenge(&mut self, env: &mut Env<'_, P>, i: usize) {
        let Ok(data) = env.random::<8>() else { return };
        let now = env.now;
        let Some(p) = self.paths.get_mut(i) else { return };
        p.push_challenge(data);
        p.challenge_at = now;
    }

    /// Put a fresh random challenge on path `i` and queue it for the next packet.
    pub(super) fn queue_challenge(&mut self, env: &mut Env<'_, P>, i: usize) {
        self.set_challenge(env, i);
        if let Some(p) = self.paths.get_mut(i) {
            p.send_challenge = p.challenge.is_some();
        }
    }

    /// Probe a new path on the cadence of a path that never answered: 9 probes, doubling.
    fn start_punch(&mut self, env: &mut Env<'_, P>, i: usize) {
        let srtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
        self.set_challenge(env, i);
        if let Some(p) = self.paths.get_mut(i) {
            p.probes_left = NAT_PROBES;
            p.probe_gap = PROBE_BASE.max(srtt / 8);
            p.next_probe = env.now;
            p.rejoin = false;
        }
    }

    /// A PATH_RESPONSE arrived on path `i`.
    pub(super) fn on_path_response(&mut self, i: usize, data: [u8; 8], now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        let Some(sent_at) = p.challenge_time(data) else { return };
        let was = p.validated;
        p.sent = [None; CHALLENGES];
        p.challenge = None;
        p.send_challenge = false;
        p.validated = true;
        p.amp.validate();
        p.probes_left = 0;
        p.rtt = if sent_at == 0 { 0 } else { now.saturating_sub(sent_at) };
        p.rejoin = false;
        let id = p.id;
        if !was {
            self.events.push(Ev::PathValidated(id));
            self.mtu_event(i);
        }
        self.choose_path();
    }

    /// Make slot `i` the active path by our own choice.
    pub(super) fn switch_active(&mut self, i: usize) {
        if i == self.paths.active || self.paths.get(i).is_none() {
            return;
        }
        let sample = self.rec.rtt().has_sample().then(|| self.rec.rtt().smoothed());
        if let Some(old) = self.paths.active_mut()
            && let Some(s) = sample
        {
            old.rtt = s;
        }
        self.paths.active = i;
        if let Ok(slot) = u8::try_from(i) {
            // The index is below `NP <= MAX_PATHS`, so the switch cannot be refused.
            let _ = self.rec.switch_path(slot);
        }
        self.after_active_change(i);
    }

    /// Follow the peer onto slot `i`: nothing restarts.
    pub(super) fn follow_active(&mut self, i: usize) {
        if i == self.paths.active || self.paths.get(i).is_none() {
            return;
        }
        self.paths.active = i;
        if let Ok(slot) = u8::try_from(i) {
            let _ = self.rec.follow_path(slot);
        }
        self.mtu_event(i);
        self.after_active_change(i);
    }

    fn after_active_change(&mut self, i: usize) {
        if let Some(p) = self.paths.get(i) {
            let mtu = u64::from(p.mtu.current);
            self.rec.set_max_datagram_size(mtu);
        }
        self.rx.set_min_rtt(self.rec.rtt().min_rtt());
        self.shed_extensions();
    }

    /// The best usable path: validated, and not a direct path that went quiet for 15 s.
    fn best_path(&self) -> Option<usize> {
        let now = self.life.clock;
        self.paths
            .iter()
            .filter(|(_, p)| p.validated && !(p.info.kind == PathKind::Direct && now.saturating_sub(p.last_rx) > PATH_IDLE_DIRECT))
            .min_by_key(|(i, p)| (p.cost(), *i))
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

    /// Take the round trips recovery measured per path.
    pub(super) fn update_path_rtts(&mut self) {
        for i in 0..NP {
            let Some(r) = u8::try_from(i).ok().and_then(|s| self.rec.path_rtt(s)) else { continue };
            if let Some(p) = self.paths.get_mut(i) {
                p.rtt = r;
            }
        }
    }

    /// The session is idle, healthy and not on a slow link, so a re-check of an idled-out direct path can be sparse.
    pub(super) fn quiet_ok(&self, now: u64) -> bool {
        let srtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
        let heard = self.paths.iter().map(|(_, p)| p.last_rx).max().unwrap_or(0);
        now.saturating_sub(self.life.last_app.max(self.life.last_data)) >= ACTIVE_KEEP
            && self.rec.pto_count() == 0
            && self.rec.peak_rtt().max(srtt) < QUIET_RTT
            && now.saturating_sub(heard) < QUIET_RX
    }

    /// The application wrote data after an idle spell: a direct path on the idle back-off is re-challenged now.
    pub(super) fn data_seen(&mut self, now: u64) {
        let idle = now.saturating_sub(self.life.last_data) >= ACTIVE_KEEP;
        self.life.last_data = now;
        self.life.last_app = now;
        if !idle {
            return;
        }
        for p in self.paths.slots.iter_mut().flatten() {
            if p.rj_back != 0 && !p.validated && p.probes_left > 0 {
                p.rj_back = 0;
                if p.next_probe > now.saturating_add(RJ_THIN_GAP) {
                    p.next_probe = now;
                }
            }
        }
    }

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
        if self.paths.active().is_none_or(|p| p.info.kind == PathKind::Relay) {
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
        let thin = self.cfg.thin;
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

    /// Send the probe of path `i` that is due and plan the next one.
    // vertexia: the protocol also spaces re-join challenges per destination address across sessions; that table
    // belongs to the endpoint, which owns the sessions that share an address.
    fn fire_probe(&mut self, env: &mut Env<'_, P>, i: usize) {
        let now = env.now;
        let srtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
        let slow = self.rec.rtt().min_rtt().unwrap_or(0) >= SLOW_RTT;
        let quiet = self.quiet_ok(now);
        let thin = self.cfg.thin;
        let Some(p) = self.paths.get_mut(i) else { return };
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
        let thin = self.cfg.thin;
        let node = self.rec.peak_rtt();
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.info.kind != PathKind::Direct || !p.validated {
            return;
        }
        p.validated = false;
        if !(thin && p.rejoin && p.probes_left > 0) {
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

    /// Move the active path to the newest relay path, if the connection has one.
    fn relay_fallback(&mut self) {
        let relay = self.paths.iter().filter(|(_, p)| p.info.kind == PathKind::Relay).map(|(i, _)| i).last();
        if let Some(r) = relay {
            self.switch_active(r);
        }
    }
}
