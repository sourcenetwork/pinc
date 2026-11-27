//! Paths: validation, following the peer, the active-path choice, the idle rules and path MTU state.
//!
//! A connection keeps at most `NP` paths. Each has its own validated flag, [`AmpBudget`], datagram size, round trip
//! and last-heard and last-sent times. A path is validated by an answered PATH_CHALLENGE (the challenges it replaced
//! are accepted too, kept in a small table of the outstanding ones, so a replaced challenge cannot strand the answer to
//! the first); the round trip it gives is the time since a datagram last left on the path, as the reference model
//! reads it. A challenge repeated faster than the round trip therefore reads less than the true round trip. That is
//! the reference model's behaviour and its path choice relies on it: a direct path several seconds long, probed on the
//! doubling cadence, reads below a relay's one-second penalty and takes the session off the relay. Once packets sent
//! on the path are acknowledged, its round trip follows the connection's smoothed one. Challenges and responses are
//! small and unpadded: the datagram size is found by the separate probe.
//!
//! Both ends follow the peer at once: the highest-numbered packet that carries STREAM, DATAGRAM or WAKE data moves the
//! active path to the path it came from unless that path's local address is gone (a gone path is never followed), and
//! only a packet carrying WAKE moves it from a direct path onto a relay path; a new UDP path is challenged in parallel
//! (a new path gets three times what it sent us until its challenge is answered). An end that sends through a relay and
//! is challenged on a direct path it has not validated, and has no challenge out on, answers with its own challenge in
//! the same datagram, so both ends validate the path in one round trip and the session leaves the relay then (the
//! reference model's responder starts its challenge only when the peer's candidate list arrives, a hop behind the
//! peer's first challenge, where the address limit then holds it back until the next probe; a node declared thin keeps
//! that cadence, and an end whose session moved no application data for 20 s only answers, as the reference model looks
//! for no direct path on an idle session). The active path is chosen by cost: the smoothed round trip of the path, plus
//! one second for a relay, minus 3 ms for IPv6; a validated UDP path that was silent for 15 s is left out; from a
//! relay, or from a path whose address is gone, the connection moves at once, otherwise only when the cheaper path's
//! round trip is more than 5 ms shorter. After three probe timeouts in a row on a direct path the path is dropped as
//! validated, challenged on the re-join cadence, and the connection falls back to a relay path if it has one.
//!
//! A challenge sent to a new or abandoned path follows a cadence that depends on why: a new path is probed 9 times
//! from `max(33.3 ms, srtt / 8)`, doubling up to 2 s; a path abandoned after probe timeouts is probed at a flat gap
//! for about 12 s, and not set up again while such a re-join is still running; on a thin session an idled-out direct
//! path is re-challenged every 20 s, backing off to 160 s while the session is quiet. A session is thin when the host
//! declared the node thin, it has no round trip yet, or the node's, its minimum or half its smoothed round trip
//! reaches 250 ms. A thin session's re-join challenge waits for the floor the endpoint sets
//! ([`Connection::set_rejoin_floor`]) and is reported to it ([`Connection::take_rejoin_fired`]), so the sessions of
//! one node space their re-join challenges to one address. A path that never answers stays
//! unvalidated and is only removed when its slot is needed.
//!
//! A relay path is valid from the moment the connection tracks it and is never challenged: the relay authenticated
//! the node at each end, as the reference model takes a relay path to be. Like every validated standby path it is
//! kept alive by the endpoint's keepalive, which is what keeps a member's carrier heard by its hub and the hub's by
//! the member.
//!
//! Invariants: the active path index always names a live slot; an unvalidated path never sends past its
//! amplification budget; a direct path is validated only by an answer to a challenge sent to it, or, for a resumed responder, by
//! the dialer's first 1-RTT packet, for the one path its Reply went to, or by another
//! session to the same peer validating the same address again ([`Connection::path_returned`]); a path whose address
//! is gone is never validated again, unless the endpoint adds its id again.

use pinc_crypto::Provider;
use pinc_security::{AmpBudget, ConnId, Env};

use super::config::{PathId, PathInfo};
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
/// How many of the oldest packets sent on another path are sent again at once when an abandoned path answers.
const REJOIN_RESEND: usize = 8;
/// The shortest gap between re-join challenges on a thin node, and the shortest wait for a migration challenge.
pub const RJ_THIN_GAP: u64 = SECOND;
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
/// Outstanding challenges kept per path with their send times.
pub(crate) const CHALLENGES: usize = 4;
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
    /// The newest challenges (the outstanding one and those it replaced); the oldest entry is overwritten.
    pub(crate) sent: [Option<[u8; 8]>; CHALLENGES],
    pub(crate) sent_next: usize,
    /// When the outstanding migration challenge was sent.
    pub(crate) challenge_at: u64,
    /// The challenge is waiting for a packet.
    pub(crate) send_challenge: bool,
    pub(crate) response: Option<[u8; 8]>,
    /// A PING is waiting to leave on this path (a standby path's keepalive).
    pub(crate) send_ping: bool,
    pub(crate) echo: Option<u16>,
    pub(crate) probes_left: u32,
    pub(crate) next_probe: u64,
    pub(crate) probe_gap: u64,
    pub(crate) rejoin: bool,
    pub(crate) rj_back: u64,
    /// No re-join challenge of a thin session leaves before this time: the node's other thin sessions challenged the
    /// same address (the endpoint sets it before each timer).
    pub(crate) rj_floor: u64,
    /// A re-join challenge of a thin session left since the endpoint last asked.
    pub(crate) rj_fired: bool,
    /// The smoothed round trip of the path, 0 while unknown.
    pub(crate) rtt: u64,
    /// When a datagram last arrived on this path, 0 for never.
    pub(crate) last_rx: u64,
    /// When a datagram last left on this path, 0 for never.
    pub(crate) last_tx: u64,
    /// The peer's id this path sends with, its index, the number of the first packet that can carry it, and whether
    /// the peer acknowledged a packet this path sent with it.
    pub(crate) dcid: Option<ConnId>,
    pub(crate) dcid_index: u64,
    pub(crate) dcid_pn: u64,
    pub(crate) dcid_seen: bool,
    /// The local address of the path is gone (the host's interface moved): nothing can use it again.
    pub(crate) gone: bool,
    /// The endpoint's ledger holds the path's address until it answers something we sent (see `path_held`).
    pub(crate) held: bool,
}

impl Path {
    pub(crate) fn new(id: PathId, info: PathInfo) -> Self {
        let relay = info.kind == PathKind::Relay;
        let mut amp = AmpBudget::new();
        if relay {
            amp.validate();
        }
        Self {
            id,
            info,
            validated: relay,
            amp,
            mtu: Mtu::new(),
            challenge: None,
            sent: [None; CHALLENGES],
            sent_next: 0,
            challenge_at: 0,
            send_challenge: false,
            response: None,
            send_ping: false,
            echo: None,
            probes_left: 0,
            next_probe: 0,
            probe_gap: PROBE_BASE,
            rejoin: false,
            rj_back: 0,
            rj_floor: 0,
            rj_fired: false,
            rtt: 0,
            last_rx: 0,
            last_tx: 0,
            dcid: None,
            dcid_index: 0,
            dcid_pn: 0,
            dcid_seen: false,
            gone: false,
            held: false,
        }
    }

    /// Record a fresh challenge, keeping the ones it replaces.
    fn push_challenge(&mut self, data: [u8; 8]) {
        self.challenge = Some(data);
        if let Some(s) = self.sent.get_mut(self.sent_next) {
            *s = Some(data);
        }
        self.sent_next = (self.sent_next + 1) % CHALLENGES;
    }

    /// Whether `data` is one of the outstanding challenges.
    fn is_challenge(&self, data: [u8; 8]) -> bool {
        self.sent.iter().flatten().any(|d| *d == data)
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
    /// A path with that id is already tracked.
    Exists,
}

impl core::fmt::Display for PathError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            Self::TooMany => "too many paths",
            Self::Unknown => "unknown path",
            Self::NotValidated => "the path is not validated",
            Self::Active => "the path is the active one",
            Self::Exists => "the path is already tracked",
        })
    }
}

impl core::error::Error for PathError {}

/// The path table.
#[derive(Debug)]
pub(crate) struct Paths<const NP: usize> {
    pub(crate) slots: [Option<Path>; NP],
    pub(crate) active: usize,
    pub(crate) held: usize,
}

impl<const NP: usize> Paths<NP> {
    pub(crate) const fn new() -> Self {
        const { assert!(NP >= 1 && NP <= crate::recovery::MAX_PATHS) };
        Self {
            slots: [None; NP],
            active: 0,
            held: 0,
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
    /// A new direct path is probed with PATH_CHALLENGE once the handshake is done; a new relay path is valid as it is
    /// and is not probed. Nothing is heard on a new path until a datagram arrives on it, as in the reference model: a
    /// session that moves onto a relay path it added does not read as heard from the moment the path was added.
    /// When the active path is gone, the best usable path takes the session at once.
    ///
    /// # Errors
    /// [`PathError::TooMany`] if the table is full and no unused path can make room.
    pub fn add_path(&mut self, env: &mut Env<'_, P>, id: PathId, info: PathInfo) -> Result<(), PathError> {
        let i = match self.paths.find(id) {
            Some(i) if !self.paths.get(i).is_some_and(|p| p.gone) => {
                self.take_info(i, info);
                if self.paths.active().is_none_or(|p| p.gone) {
                    self.choose_path();
                }
                return Ok(());
            }
            // The endpoint names a live local address for the id of a lost path again: the slot starts over.
            Some(i) => {
                self.put_path(i, id, info, env.now);
                i
            }
            None => self.new_path_slot(id, info, env.now).ok_or(PathError::TooMany)?,
        };
        // The endpoint chose this address itself, so the amplification limit that guards against spoofed sources
        // does not apply to challenging it.
        if let Some(p) = self.paths.get_mut(i) {
            p.amp.validate();
            p.last_rx = 0;
        }
        if self.phase == Phase::Connected && info.kind != PathKind::Relay {
            self.start_punch(env, i);
        }
        // Only a lost active path is left here: a relay added from a relay must not hop to a second relay whose round
        // trip still reads 0 (see `set_path_info`).
        if self.paths.active().is_none_or(|p| p.gone) {
            self.choose_path();
        }
        Ok(())
    }

    /// The path `old` now leaves from another local address, and `new` is its id from here on: the host's interface
    /// kept its network but changed address. The path keeps its slot and all it knows (validated, round trip,
    /// congestion and packet size state, the id it sends with, whether it is the active path), as the same path to the
    /// same peer address does when only the interface under it moves.
    ///
    /// # Errors
    /// [`PathError::Unknown`] if `old` is not tracked, [`PathError::Exists`] if `new` already is (the caller then adds
    /// `new` and drops `old` as for a path that is gone).
    pub fn rebind_path(&mut self, old: PathId, new: PathId) -> Result<(), PathError> {
        let i = self.paths.find(old).ok_or(PathError::Unknown)?;
        if self.paths.find(new).is_some() {
            return Err(PathError::Exists);
        }
        if let Some(p) = self.paths.get_mut(i) {
            p.id = new;
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

    /// A punch round: every direct path the connection tracks that is not validated and has no probe left is probed
    /// on the cadence of a new path. The reference model's punch challenges every such path of the session, not only
    /// the addresses the layer above names. Without it a path that lost its validation with no re-join running (an
    /// abandoned path of a session that is not thin once its re-join probes are spent, a path a sub-session took
    /// unvalidated from its parent) is never tried again by this end, and a session on a relay stays there.
    pub fn punch_known(&mut self, env: &mut Env<'_, P>) {
        if self.phase != Phase::Connected {
            return;
        }
        for i in 0..NP {
            let due = self
                .paths
                .get(i)
                .is_some_and(|p| p.info.kind == PathKind::Direct && !p.validated && !p.gone && p.probes_left == 0);
            if due {
                self.start_punch(env, i);
            }
        }
    }

    /// Whether the session counts as thin for its path rules: the host declared the node thin, or the session has no
    /// round trip yet, or the node's, its minimum or half its smoothed round trip reaches 250 ms.
    pub(crate) fn thin_session(&self) -> bool {
        self.cfg.thin || self.rec.is_thin()
    }

    /// The paths whose re-join challenges the connection spaces against its node's other thin sessions: those still
    /// being re-challenged on a thin session. The endpoint sets their floors with [`Connection::set_rejoin_floor`].
    pub fn rejoin_paths(&self) -> impl Iterator<Item = PathId> + '_ {
        let thin = self.thin_session();
        self.paths
            .iter()
            .filter(move |(_, p)| thin && p.rejoin && p.probes_left > 0)
            .map(|(_, p)| p.id)
    }

    /// Whether any path is still being re-challenged after it was abandoned or idled out. A re-join challenge leaves
    /// only on such a path, and never in the call that starts the re-join, so a caller that sees `false` before a
    /// timer has no floor to set and no challenge to collect after it.
    pub fn rejoin_running(&self) -> bool {
        self.paths.iter().any(|(_, p)| p.rejoin && p.probes_left > 0)
    }

    /// No re-join challenge on path `id` leaves before `at`: another session of the node challenged the same address
    /// within the spacing. 0 lifts the wait. Ignored for a path the connection does not track.
    pub fn set_rejoin_floor(&mut self, id: PathId, at: u64) {
        if let Some(p) = self.paths.find(id).and_then(|i| self.paths.get_mut(i)) {
            p.rj_floor = at;
        }
    }

    /// A path on which a re-join challenge of a thin session left since the last call, once per challenge.
    pub fn take_rejoin_fired(&mut self) -> Option<PathId> {
        let p = self.paths.slots.iter_mut().flatten().find(|p| p.rj_fired)?;
        p.rj_fired = false;
        Some(p.id)
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

    /// Keep the standby path `id` alive: a PING leaves on it with the next packet, which the peer acknowledges. Unlike
    /// [`probe`](Self::probe) it starts no challenge, so the path's round trip and the choice of the active path are
    /// left as they are.
    ///
    /// # Errors
    /// [`PathError::Unknown`] if the path is not tracked.
    pub fn ping_path(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if let Some(p) = self.paths.get_mut(i) {
            p.send_ping = true;
        }
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
        self.paths.recount();
        Ok(())
    }

    /// Tell the connection path `id` can no longer be used: its local address is gone (the host's interface moved) or
    /// the endpoint no longer holds its address pair. The path is no
    /// longer usable: the connection leaves it for the best validated path at once, or as soon as one validates, and
    /// then forgets it.
    ///
    /// # Errors
    /// [`PathError::Unknown`] if the path is not tracked.
    pub fn path_lost(&mut self, id: PathId) -> Result<(), PathError> {
        let i = self.paths.find(id).ok_or(PathError::Unknown)?;
        if let Some(p) = self.paths.get_mut(i) {
            p.gone = true;
            p.validated = false;
            // A gone path sends nothing more: no probe, re-join or challenge is left armed on it.
            p.probes_left = 0;
            p.rejoin = false;
            p.send_challenge = false;
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
        self.paths.recount();
    }

    /// Whether the connection tracks path `id`.
    pub fn has_path(&self, id: PathId) -> bool {
        self.paths.find(id).is_some()
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

    /// Say what the endpoint knows of a path the connection already tracks. A server learns the path of its first packet
    /// by receiving on it and takes it to be direct; the endpoint knows when the address is a relay's, and a relay
    /// path must rank behind every direct one, or the session never leaves it for a direct path that validates. A path
    /// the connection does not track is left alone: the amplification limit still guards it.
    ///
    /// The active path is chosen again only if it is now a relay path, gone, or there is none: the reference model
    /// chooses by itself only from a relay, and otherwise when a direct path validates. A session on a direct path
    /// stays on it whatever the endpoint says of another path. Chosen again there, it would leave a direct path
    /// slower than a second for a relay path whose round trip is not known yet and reads as zero.
    pub fn set_path_info(&mut self, id: PathId, info: PathInfo) {
        let Some(i) = self.paths.find(id) else { return };
        if let Some(p) = self.paths.get_mut(i)
            && p.info != info
        {
            p.info = info;
            self.sync_kind(i);
            if self.active_open_to_move() {
                self.choose_path();
            }
            // The path becomes a candidate for the next choice of the active path, not this one.
            self.take_info(i, info);
        }
    }

    /// The active path is one the connection leaves for any better path at once: none, a relay, or gone.
    pub(super) fn active_open_to_move(&self) -> bool {
        self.paths.active().is_none_or(|p| p.gone || p.info.kind == PathKind::Relay)
    }

    /// Take what the endpoint knows of held path `i`: its kind decides the path cost, and a path named a relay's is
    /// valid as every relay path is.
    fn take_info(&mut self, i: usize, info: PathInfo) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.info = info;
        if info.kind == PathKind::Relay && !p.validated && !p.gone {
            p.validated = true;
            p.amp.validate();
        }
        self.sync_kind(i);
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
    /// What is assumed of a path the connection learns of by receiving on it: direct, and as wide as the host's
    /// interface.
    pub(super) fn learned_path(&self) -> PathInfo {
        PathInfo {
            interface_mtu: self.cfg.interface_mtu,
            ..PathInfo::default()
        }
    }

    /// Learn the path `id` of a packet by receiving on it, as the endpoint knows nothing else of it yet: the one rule
    /// for both roles. The slot of a path already held, else a new one; `None` when the table is full of validated
    /// paths and the active one.
    pub(super) fn learn_path(&mut self, id: PathId, now: u64) -> Option<usize> {
        self.new_path_slot(id, self.learned_path(), now)
    }

    /// The slot of path `id` if it is held (its state and `info` untouched), else a new one for it, taking a free slot
    /// or the first unvalidated path that is not the active one; `None` when neither exists. A path is never held
    /// twice.
    pub(super) fn new_path_slot(&mut self, id: PathId, info: PathInfo, now: u64) -> Option<usize> {
        if let Some(i) = self.paths.find(id) {
            return Some(i);
        }
        let active = self.paths.active;
        let free = self
            .paths
            .slots
            .iter()
            .position(Option::is_none)
            .or_else(|| self.paths.iter().find(|(i, p)| *i != active && !p.validated).map(|(i, _)| i))?;
        self.put_path(free, id, info, now);
        Some(free)
    }

    /// Start slot `i` over as the new path `id`.
    fn put_path(&mut self, i: usize, id: PathId, info: PathInfo, now: u64) {
        let mut path = Path::new(id, info);
        path.mtu.started = self.phase == Phase::Connected;
        path.last_rx = now;
        if let Some(slot) = self.paths.slots.get_mut(i) {
            *slot = Some(path);
        }
        self.paths.recount();
        self.sync_kind(i);
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

    /// Start validating path `i` by a challenge: queue it, and retry it on the probe cadence (one probe per round
    /// of the probe timeout, doubling) until it is answered or the probes are spent. A punch or re-join already
    /// running on the path keeps its own cadence.
    pub(super) fn challenge_path(&mut self, env: &mut Env<'_, P>, i: usize) {
        self.queue_challenge(env, i);
        let gap = self.rec.pto_duration();
        if let Some(p) = self.paths.get_mut(i)
            && p.probes_left == 0
        {
            p.probes_left = NAT_PROBES;
            p.probe_gap = gap;
            p.next_probe = env.now.saturating_add(gap);
            p.rejoin = false;
        }
    }

    /// The peer challenged path `i`. If this end sends through a relay, and the path is a direct one it has not
    /// validated and has no challenge out on, its own challenge leaves with the response, in the same datagram, so
    /// both ends validate the direct path in the round trip of the peer's challenge and the session leaves the relay
    /// then. Sent on its own after the response, the challenge would be more than an address that has only sent a
    /// challenge may be answered with (three times what arrived from it), and it would wait for the next probe; the
    /// two frames together fit. One challenge, never a second while it is out: the probes of a punch keep their own
    /// cadence. An end whose active path is direct gains nothing from it and is left alone, and so is an idle one (no
    /// application data for 20 s): the reference model looks for no direct path on an idle session (its punch round
    /// is skipped), so a session that lapsed onto its relay stays there until data moves again.
    pub(super) fn challenge_back(&mut self, env: &mut Env<'_, P>, i: usize) {
        // vertexia: a node the host declared thin keeps the reference model's cadence (its challenges are counted
        // against a thin uplink); lift this once the scenario matrix shows no thin row worse with it.
        let wanted = self.phase == Phase::Connected
            && !self.cfg.thin
            && env.now < self.life.app_until
            && self.paths.active().is_none_or(|c| c.info.kind == PathKind::Relay)
            && self
                .paths
                .get(i)
                .is_some_and(|p| p.info.kind == PathKind::Direct && !p.validated && p.challenge.is_none());
        if wanted {
            self.challenge_path(env, i);
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

    /// A PATH_RESPONSE arrived on path `i`. The path's round trip is the time since the last datagram left on it, as in
    /// the reference model, whose path choice is tuned to that reading.
    pub(super) fn on_path_response(&mut self, i: usize, data: [u8; 8], now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.gone || !p.is_challenge(data) {
            return;
        }
        let was = p.validated;
        let rejoining = p.rejoin;
        p.sent = [None; CHALLENGES];
        p.challenge = None;
        p.send_challenge = false;
        p.validated = true;
        p.amp.validate();
        p.probes_left = 0;
        p.rtt = if p.last_tx == 0 { 0 } else { now.saturating_sub(p.last_tx) };
        p.rejoin = false;
        let id = p.id;
        if !was {
            self.events.push(Ev::PathValidated(id));
            self.mtu_event(i);
        }
        self.choose_path();
        if rejoining {
            let rtt = self.paths.get(i).map_or(0, |p| p.rtt);
            self.life.rejoined = Some((id, rtt));
            self.rejoin_resend(now, i);
        }
    }

    /// The path of slot `i` was abandoned and answers again: if it is the active path, what went out on the other path
    /// is sent again now.
    fn rejoin_resend(&mut self, now: u64, i: usize) {
        if i != self.paths.active {
            return;
        }
        let Ok(slot) = u8::try_from(i) else { return };
        let mut out = super::ctl::Outcome::default();
        let (streams, pool, ctl) = (&mut *self.streams, &mut self.pool, &mut self.ctl);
        self.rec
            .resend_off_path(now, slot, REJOIN_RESEND, |ev| super::ctl::apply(&ev, streams, pool, ctl, &mut out));
        self.life.probes = 0;
        self.degraded_told = false;
        self.after_feedback(out, now);
    }

    /// The path a session of this peer's abandoned address validated again, with its round trip, once; the endpoint
    /// hands it to the peer's other sessions with [`Connection::path_returned`].
    pub fn take_rejoined(&mut self) -> Option<(PathId, u64)> {
        self.life.rejoined.take()
    }

    /// Another session to the same peer validated the address of path `id` again: if this session waits for it on a
    /// path it abandoned, that path is valid at once with the round trip `rtt`, and what went out on the other path is
    /// sent again. Returns whether the path was taken.
    pub fn path_returned(&mut self, id: PathId, rtt: u64, now: u64) -> bool {
        let Some(i) = self.paths.find(id) else { return false };
        let Some(p) = self.paths.get_mut(i) else { return false };
        if p.gone || !p.rejoin || p.validated {
            return false;
        }
        p.sent = [None; CHALLENGES];
        p.challenge = None;
        p.send_challenge = false;
        p.validated = true;
        p.amp.validate();
        p.probes_left = 0;
        p.rtt = rtt;
        p.rejoin = false;
        p.last_rx = now;
        self.events.push(Ev::PathValidated(id));
        self.mtu_event(i);
        self.choose_path();
        self.rejoin_resend(now, i);
        true
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

    /// Move to the cheapest usable path: at once from a relay or a gone path, otherwise when its round trip is more
    /// than 5 ms shorter than the active path's.
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
}
