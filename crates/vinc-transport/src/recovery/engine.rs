//! The recovery engine of one connection: the ring of sent packets, the round-trip estimate, loss detection, the
//! probe timer, congestion control and pacing behind one interface.
//!
//! Acknowledged ranges come in as inclusive packet-number ranges (largest first); what happened to each packet goes
//! out through an [`Event`] callback, so nothing is buffered or allocated. This file holds the state, the sending
//! side, the path rules and the accounting; acknowledgement handling is in `ack`, loss detection in `loss` and the
//! probe timer in `pto`.
//!
//! Only packets that need an acknowledgement and count toward bytes in flight are recorded with
//! [`Recovery::on_packet_sent`]. Acknowledgement-only packets, probes, path-validation packets on standby paths and
//! CLOSE are announced with [`Recovery::on_packet_untracked`]: they use a packet number but are never in flight, never
//! lost and never sampled.
//!
//! Invariants:
//! - for recorded packets, `bytes_sent == bytes_acked + bytes_in_flight + bytes_lost` at every call boundary; a late
//!   acknowledgement moves a packet's bytes from lost to acked;
//! - the cumulative byte counters are `u128` (at most 2^64 packets of at most 2^32 bytes cannot overflow it) and the
//!   in-flight counter is `u64` (at most `N <= 2^31` packets of at most 2^32 bytes: below 2^63);
//! - a repair packet or a path MTU probe that is lost is reported with `requeue == false` (the probe with
//!   `mtu_probe == true`) and never reduces the window;
//! - the window grows on every acknowledged byte, and the rate gate (see [`Cubic::gate_cap`]) is the only brake
//!   besides loss.

use super::cubic::{AckInput, Cubic, MAX_MSS, MIN_MSS};
use super::frame_ref::FrameRefs;
use super::pacer::Pacer;
use super::rtt::RttEstimator;
use super::sent::{Sent, SentRing};
use super::{LONG_RTT, MAX_PACKET_NUMBER, MS, RecoveryError};

/// The most paths one connection tracks.
pub const MAX_PATHS: usize = 8;
/// The segment size of the window growth on every path but a fast direct one.
const DEFAULT_SEGMENT: u64 = 1_200;
/// A direct path whose minimum round trip is below this (2 ms) grows the window in units of its datagram size.
const FAST_RTT: u64 = 2 * MS;
/// Probe timeouts at which the endpoint is told the path is struggling.
const PTO_TELL_ENDPOINT: u32 = 3;
/// Probe timeouts at which the connection gives up (with the silence conditions of [`Recovery::health`]).
const PTO_GIVE_UP: u32 = 10;
/// Silence needed to give up on a slow or thin path (20 s).
const GIVE_UP_SILENCE_SLOW: u64 = 20 * super::SECOND;
/// Silence needed to give up, in smoothed round trips.
const GIVE_UP_SILENCE_RTTS: u64 = 8;
/// A node round trip of this much or more marks a thin node.
const THIN_RTT: u64 = LONG_RTT;
/// Lost send times remembered so a late acknowledgement can still seed the round trip.
const LATE_SENDS: usize = 32;

/// Whether a path is a direct path or a relay.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathKind {
    /// A direct path between the endpoints.
    Direct,
    /// A path through a relay.
    Relay,
}

/// What happened to one packet.
#[derive(Debug, Clone, Copy)]
pub enum Event<'a> {
    /// The packet was acknowledged: its stream bytes can be freed.
    Acked {
        /// The packet number.
        pn: u64,
        /// The datagram size.
        size: u32,
        /// What the packet carried.
        frames: &'a FrameRefs,
        /// Whether the packet was a path MTU probe.
        mtu_probe: bool,
        /// Whether the packet was a repair packet.
        repair: bool,
        /// The path the packet left on.
        path: u8,
    },
    /// A packet already declared lost was acknowledged after all: cancel any retransmission still queued for it.
    LateAcked {
        /// The packet number.
        pn: u64,
        /// What the packet carried.
        frames: &'a FrameRefs,
    },
    /// The packet was declared lost.
    Lost {
        /// The packet number.
        pn: u64,
        /// The datagram size.
        size: u32,
        /// What the packet carried.
        frames: &'a FrameRefs,
        /// Whether the frames are to be requeued; false for a repair packet or a path MTU probe.
        requeue: bool,
        /// Whether the packet was a path MTU probe.
        mtu_probe: bool,
    },
}

/// Totals of one call.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Summary {
    /// Packets newly acknowledged while in flight.
    pub acked_packets: u32,
    /// Bytes newly acknowledged.
    pub acked_bytes: u64,
    /// Packets acknowledged after being declared lost.
    pub late_acked_packets: u32,
    /// Packets declared lost.
    pub lost_packets: u32,
    /// Bytes declared lost.
    pub lost_bytes: u64,
}

/// What a timer expiry asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Timeout {
    /// Packets declared lost by this expiry.
    pub summary: Summary,
    /// Whether to send one PING now. It is not recorded as in flight.
    pub ping: bool,
}

/// How the path is doing, from consecutive probe timeouts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Health {
    /// Fewer than 3 consecutive probe timeouts.
    Healthy,
    /// 3 or more probe timeouts: tell the endpoint.
    Degraded,
    /// 10 or more probe timeouts and enough silence (see [`Recovery::health`]): give up.
    Dead,
}

#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Account {
    pub(super) sent: u128,
    pub(super) acked: u128,
    pub(super) lost: u128,
    pub(super) in_flight: u64,
}

/// The window saved by the first probe timeout, restored if the packet it declared lost is acknowledged.
#[derive(Debug, Clone, Copy)]
pub(super) struct SavedWindow {
    pub(super) pn: u64,
    pub(super) cwnd: u64,
    pub(super) ssthresh: u64,
}

/// The reorder lens: what overtaken packets showed about reordering on one path.
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Reorder {
    /// The widest send-time spread between an overtaken packet and the packet acknowledged ahead of it.
    pub(super) extent: u64,
    /// When the last overtaken packet was acknowledged.
    pub(super) seen: Option<u64>,
}

/// Send times of the newest lost packets, so a late acknowledgement of one can seed an empty round-trip estimate.
#[derive(Debug, Clone, Copy)]
pub(super) struct LateSends {
    items: [(u64, u64); LATE_SENDS],
    len: usize,
}

impl LateSends {
    const fn new() -> Self {
        Self {
            items: [(0, 0); LATE_SENDS],
            len: 0,
        }
    }

    /// Remember that packet `pn` sent at `time` was declared lost; the lowest number goes when the table is full.
    pub(super) fn insert(&mut self, pn: u64, time: u64) {
        if self.len == LATE_SENDS
            && let Some(min) = self.items.iter().take(self.len).map(|e| e.0).min()
        {
            self.take(min);
        }
        if let Some(slot) = self.items.get_mut(self.len) {
            *slot = (pn, time);
            self.len += 1;
        }
    }

    /// The remembered entries, in insertion order, for trace validation.
    #[cfg(feature = "trace")]
    pub(super) fn entries(&self) -> alloc::vec::Vec<(u64, u64)> {
        self.items.iter().take(self.len).copied().collect()
    }

    /// Forget and return the send time of lost packet `pn`.
    pub(super) fn take(&mut self, pn: u64) -> Option<u64> {
        let i = self.items.iter().take(self.len).position(|e| e.0 == pn)?;
        let time = self.items.get(i).map(|e| e.1);
        self.items.copy_within(i + 1..self.len, i);
        self.len -= 1;
        time
    }
}

/// Loss recovery for one connection, with room for `N` recorded packets.
#[derive(Debug, Clone)]
pub struct Recovery<const N: usize> {
    pub(super) ring: SentRing<N>,
    pub(super) rtt: RttEstimator,
    pub(super) cc: Cubic,
    pub(super) pacer: Pacer,
    pub(super) acct: Account,
    pub(super) in_flight_packets: u32,
    pub(super) largest_sent: Option<u64>,
    pub(super) largest_acked: Option<u64>,
    pub(super) loss_time: Option<u64>,
    pub(super) pto_count: u32,
    pub(super) last_pto: u64,
    pub(super) asleep: bool,
    pub(super) link_down: bool,
    pub(super) last_heard: u64,
    pub(super) clock: u64,
    pub(super) tgr: u64,
    pub(super) lrtt: u64,
    pub(super) paths: [PathKind; MAX_PATHS],
    pub(super) path_rtt: [u64; MAX_PATHS],
    pub(super) active: u8,
    pub(super) flip_at: Option<u64>,
    pub(super) mtu: u64,
    pub(super) late_sends: LateSends,
    pub(super) saved_window: Option<SavedWindow>,
    pub(super) reorder: [Reorder; MAX_PATHS],
    /// When the ghosts were last looked at.
    pub(super) ghost_scan: u64,
    /// When the window last limited the sender; `None` before the first time.
    pub(super) limited_at: Option<u64>,
    /// The send time of the largest acknowledged packet, from the acknowledgement that sampled it.
    pub(super) largest_acked_time: u64,
}

impl<const N: usize> Recovery<N> {
    /// A recovery state for a path datagram size of `mtu` (clamped to 1200..=65535), path 0 active and direct.
    pub fn new(mtu: u64) -> Self {
        Self::with_ring(mtu, SentRing::new())
    }

    /// A recovery state that records its packets in `ring`, which must be empty.
    pub fn with_ring(mtu: u64, ring: SentRing<N>) -> Self {
        Self {
            ring,
            rtt: RttEstimator::new(),
            cc: Cubic::new(),
            pacer: Pacer::new(),
            acct: Account::default(),
            in_flight_packets: 0,
            largest_sent: None,
            largest_acked: None,
            loss_time: None,
            pto_count: 0,
            last_pto: 0,
            asleep: false,
            link_down: false,
            last_heard: 0,
            clock: 0,
            tgr: 0,
            lrtt: 0,
            paths: [PathKind::Direct; MAX_PATHS],
            path_rtt: [0; MAX_PATHS],
            active: 0,
            flip_at: None,
            mtu: mtu.clamp(MIN_MSS, MAX_MSS),
            late_sends: LateSends::new(),
            saved_window: None,
            reorder: [Reorder { extent: 0, seen: None }; MAX_PATHS],
            ghost_scan: 0,
            limited_at: None,
            largest_acked_time: 0,
        }
    }

    /// Give back the table of sent packets, for the next connection (see [`SentRing::clear`]).
    pub fn into_ring(self) -> SentRing<N> {
        self.ring
    }

    // ---- read access ----

    /// The round-trip estimator.
    pub const fn rtt(&self) -> &RttEstimator {
        &self.rtt
    }

    /// Seed the smoothed round trip and its variation with the handshake round trip when the estimate is still empty,
    /// so the first probe timeout, the loss timer and the pacer start from it instead of the initial guess. The
    /// latest and minimum round trip stay unknown until an acknowledgement measures them (see [`RttEstimator::seed`]).
    pub fn seed_rtt(&mut self, rtt: u64) {
        self.rtt.seed(rtt);
    }

    /// Take another connection's round-trip estimate when this one has none yet: a sub-session starts from its
    /// parent's.
    pub fn adopt_rtt(&mut self, rtt: RttEstimator) {
        if !self.rtt.has_sample() {
            self.rtt = rtt;
        }
    }

    /// The congestion controller.
    pub const fn cc(&self) -> &Cubic {
        &self.cc
    }

    /// The pacer; its [`Pacer::next_release`] feeds the connection's timeout.
    pub const fn pacer(&self) -> &Pacer {
        &self.pacer
    }

    /// The congestion window in bytes.
    pub const fn cwnd(&self) -> u64 {
        self.cc.cwnd()
    }

    /// The path the oldest packet still in flight left on; a packet declared lost or acknowledged is not in flight.
    pub fn oldest_in_flight_path(&mut self) -> Option<u8> {
        let i = self.ring.first_in_flight()?;
        self.ring.get(i).map(|s| s.sent.path)
    }

    /// Bytes sent and neither acknowledged nor declared lost.
    pub const fn bytes_in_flight(&self) -> u64 {
        self.acct.in_flight
    }

    /// Whether the window has room for one more datagram of the path's size, `in_flight + mtu <= cwnd`, and the ring
    /// has a slot to record it. A full ring closes the window like a full `cwnd`: the caller then sends only what is
    /// never recorded (an acknowledgement), instead of building data packets the ring refuses.
    pub fn can_send(&self) -> bool {
        self.acct.in_flight.saturating_add(self.mtu) <= self.cc.cwnd() && self.ring.has_room()
    }

    /// Whether the sent ring has a slot to record one more packet. With none, only what is never recorded (an
    /// acknowledgement, a path validation packet) can leave.
    pub fn ring_has_room(&self) -> bool {
        self.ring.has_room()
    }

    /// Cumulative bytes of recorded packets sent.
    pub const fn bytes_sent(&self) -> u128 {
        self.acct.sent
    }

    /// Cumulative bytes acknowledged (late acknowledgements included).
    pub const fn bytes_acked(&self) -> u128 {
        self.acct.acked
    }

    /// Bytes currently counted as lost (declared lost and not acknowledged since).
    pub const fn bytes_lost(&self) -> u128 {
        self.acct.lost
    }

    /// The number of consecutive probe timeouts.
    pub const fn pto_count(&self) -> u32 {
        self.pto_count
    }

    /// The largest packet number sent, recorded or not.
    pub const fn largest_sent(&self) -> Option<u64> {
        self.largest_sent
    }

    /// The largest packet number the peer acknowledged.
    pub const fn largest_acked(&self) -> Option<u64> {
        self.largest_acked
    }

    /// Recorded packets in flight.
    pub const fn packets_in_flight(&self) -> u32 {
        self.in_flight_packets
    }

    /// The packet number the next sent packet will have.
    pub const fn next_pn(&self) -> u64 {
        match self.largest_sent {
            Some(l) => l + 1,
            None => 0,
        }
    }

    /// The frames of packet `pn` if it is still in flight; used to build a tail repair.
    pub fn sent_frames(&self, pn: u64) -> Option<&FrameRefs> {
        self.ring.in_flight(pn).map(|s| &s.frames)
    }

    /// The segment size of the window growth: 1200, or the path datagram size on a direct path whose minimum round
    /// trip is below 2 ms.
    pub fn segment_size(&self) -> u64 {
        let fast = self.rtt.min_rtt().is_some_and(|m| m < FAST_RTT)
            && self.paths.get(usize::from(self.active)) == Some(&PathKind::Direct);
        if fast && self.mtu > DEFAULT_SEGMENT {
            self.mtu
        } else {
            DEFAULT_SEGMENT
        }
    }

    /// The round trip last measured on `path`, if it carried the newest acknowledged packet of some acknowledgement.
    pub fn path_rtt(&self, path: u8) -> Option<u64> {
        self.path_rtt.get(usize::from(path)).copied().filter(|r| *r > 0)
    }

    // ---- configuration ----

    /// Mark `path` as direct or relay.
    ///
    /// # Errors
    /// [`RecoveryError::PathOutOfRange`] if `path` is not below 8.
    pub fn set_path_kind(&mut self, path: u8, kind: PathKind) -> Result<(), RecoveryError> {
        *self
            .paths
            .get_mut(usize::from(path))
            .ok_or(RecoveryError::PathOutOfRange)? = kind;
        Ok(())
    }

    /// Make `path` the active path. Unless both the old and the new path are relays, the congestion
    /// controller restarts (initial window, slow start, fresh slow-start rounds) and a loss of anything sent before
    /// the switch cuts nothing; the round-trip estimate, the probe count and the pacer are kept. Returns whether the
    /// controller restarted. The switch is stamped with the newest time any call has carried.
    ///
    /// # Errors
    /// [`RecoveryError::PathOutOfRange`] if `path` is not below 8.
    pub fn switch_path(&mut self, path: u8) -> Result<bool, RecoveryError> {
        let new = *self.paths.get(usize::from(path)).ok_or(RecoveryError::PathOutOfRange)?;
        if path == self.active {
            return Ok(false);
        }
        let old = self.paths.get(usize::from(self.active)).copied();
        self.active = path;
        if old == Some(PathKind::Relay) && new == PathKind::Relay {
            return Ok(false);
        }
        self.cc.new_path(self.clock, self.next_pn());
        self.flip_at = Some(self.clock);
        Ok(true)
    }

    /// The session follows the peer onto `path` (a migration the peer started): nothing restarts, but packets sent
    /// before now on a relay path are judged by the slow rule.
    ///
    /// # Errors
    /// [`RecoveryError::PathOutOfRange`] if `path` is not below 8.
    pub fn follow_path(&mut self, path: u8) -> Result<(), RecoveryError> {
        if usize::from(path) >= MAX_PATHS {
            return Err(RecoveryError::PathOutOfRange);
        }
        if path != self.active {
            self.active = path;
            self.flip_at = Some(self.clock);
        }
        Ok(())
    }

    /// Set the datagram size of the active path (clamped to 1200..=65535).
    pub fn set_max_datagram_size(&mut self, mtu: u64) {
        self.mtu = mtu.clamp(MIN_MSS, MAX_MSS);
    }

    /// While the peer sleeps, a probe timeout sends nothing and does not grow the backoff or the counter.
    pub fn set_peer_asleep(&mut self, asleep: bool) {
        self.asleep = asleep;
    }

    /// While the link is down, a probe timeout still declares the oldest packet lost and asks for a PING, but does
    /// not grow the counter.
    pub fn set_link_down(&mut self, down: bool) {
        self.link_down = down;
    }

    /// Seed the node's peak round trip (see [`Self::peak_rtt`]), for example from an earlier connection. A node
    /// whose peak or handshake round trip is 250 ms or more is thin, which lengthens the silence needed before
    /// giving up; without a sample of its own the probe timeout starts from `max(333 ms, 2 x` the larger of the two`)`.
    pub fn set_node_rtt(&mut self, rtt: u64) {
        self.tgr = rtt;
    }

    /// Set the node's handshake round trip (what the first flight measured).
    pub fn set_handshake_rtt(&mut self, rtt: u64) {
        self.lrtt = rtt;
    }

    /// The node's peak round trip: after each sample `peak = max(srtt, peak - peak / 32)`. The endpoint reads it
    /// and feeds it back to later connections through [`Self::set_node_rtt`].
    pub const fn peak_rtt(&self) -> u64 {
        self.tgr
    }

    pub(super) const fn node_rtt(&self) -> u64 {
        if self.tgr > self.lrtt { self.tgr } else { self.lrtt }
    }

    /// Set the rate gate's slack for round trips between 2 ms and 250 ms (44,000 bytes by default).
    pub fn set_gate_slack(&mut self, bytes: u64) {
        self.cc.set_gate_slack(bytes);
    }

    /// Note that anything arrived from the peer at `now` (restarts the silence clock).
    pub fn note_peer_activity(&mut self, now: u64) {
        self.last_heard = self.last_heard.max(now);
        self.clock = self.clock.max(now);
    }

    /// Whether the node is thin as far as this connection can tell: no round-trip estimate yet (a handshake seed
    /// counts), or the node round trip, the minimum round trip or half the smoothed round trip is 250 ms or more.
    pub fn is_thin(&self) -> bool {
        if !self.rtt.has_sample() {
            return true;
        }
        self.node_rtt()
            .max(self.rtt.min_rtt().unwrap_or(0))
            .max(self.rtt.smoothed() >> 1)
            >= THIN_RTT
    }

    // ---- sending ----

    fn check_next(&self, pn: u64) -> Result<(), RecoveryError> {
        if pn > MAX_PACKET_NUMBER {
            return Err(RecoveryError::PacketNumberOutOfRange);
        }
        if self.largest_sent.is_some_and(|l| pn <= l) {
            return Err(RecoveryError::PacketNumberNotIncreasing);
        }
        Ok(())
    }

    /// Record a sent packet that needs an acknowledgement and counts toward bytes in flight.
    ///
    /// # Errors
    /// [`RecoveryError::PacketNumberOutOfRange`], [`RecoveryError::PacketNumberNotIncreasing`],
    /// [`RecoveryError::PathOutOfRange`], or [`RecoveryError::RingFull`] when the ring is full of packets in flight.
    pub fn on_packet_sent(&mut self, p: Sent) -> Result<(), RecoveryError> {
        self.check_next(p.pn)?;
        if usize::from(p.path) >= MAX_PATHS {
            return Err(RecoveryError::PathOutOfRange);
        }
        self.clock = self.clock.max(p.time);
        self.ring.trim(p.time);
        if self.unlimited_for(p.time) {
            self.cc.resume(self.rtt.min_rtt());
        }
        if !self.ring.push(p) {
            return Err(RecoveryError::RingFull);
        }
        self.largest_sent = Some(p.pn);
        self.acct.sent += u128::from(p.size);
        self.acct.in_flight += u64::from(p.size);
        self.in_flight_packets += 1;
        if self.rtt.has_sample() {
            self.pacer.on_sent(
                p.time,
                self.mtu,
                self.rtt.smoothed(),
                self.cc.cwnd(),
                self.window_limits(),
            );
        }
        self.note_limited(p.time);
        Ok(())
    }

    /// Whether the window limits the sender: it cannot send, or at least half of the window is in flight (a paced or
    /// credit-limited sender that keeps the path busy is not idle).
    fn window_limits(&self) -> bool {
        !self.can_send() || self.acct.in_flight >= self.cc.cwnd() / 2
    }

    /// Remember that the window limits the sender at `now`.
    pub(super) fn note_limited(&mut self, now: u64) {
        if self.window_limits() {
            self.limited_at = Some(now);
        }
    }

    /// Whether the window has not limited the sender for at least one smoothed round trip (or ever).
    fn unlimited_for(&self, now: u64) -> bool {
        self.limited_at
            .is_none_or(|t| now.saturating_sub(t) >= self.rtt.smoothed())
    }

    /// Note that packet `pn` was sent without being recorded: an acknowledgement-only packet, a probe, a path
    /// validation packet on a standby path, or a CLOSE. It never counts as in flight and is never lost.
    ///
    /// # Errors
    /// [`RecoveryError::PacketNumberOutOfRange`] or [`RecoveryError::PacketNumberNotIncreasing`].
    pub fn on_packet_untracked(&mut self, pn: u64) -> Result<(), RecoveryError> {
        self.check_next(pn)?;
        self.largest_sent = Some(pn);
        Ok(())
    }

    // ---- state changes shared by the submodules ----

    pub(super) fn ack_input(&self, now: u64, acked: u64) -> AckInput {
        AckInput {
            now,
            acked,
            largest_acked: self.largest_acked.unwrap_or(0),
            next_pn: self.next_pn(),
            srtt: self.rtt.has_sample().then(|| self.rtt.smoothed()),
            min_rtt: self.rtt.min_rtt(),
            mss: self.segment_size(),
        }
    }

    /// Declare every packet in flight lost with no congestion response and reset the probe backoff: the peer woke
    /// from sleep, the link came back, or early data was rejected. Each packet is reported as lost and to be requeued.
    pub fn flush_in_flight<F: FnMut(Event<'_>)>(&mut self, now: u64, on_event: F) -> Summary {
        let s = self.lose_in_flight(now, usize::MAX, None, on_event);
        self.loss_time = None;
        self.pto_count = 0;
        self.last_pto = 0;
        self.saved_window = None;
        s
    }

    /// A path that was abandoned answers again and is the active path: declare the oldest `limit` packets in flight
    /// that were sent on another path than `path` lost, with no congestion response, so they are sent again at once and
    /// not at the next backed-off probe timeout, and reset the probe timeout count. Each is reported as lost and to be
    /// requeued.
    pub fn resend_off_path<F: FnMut(Event<'_>)>(&mut self, now: u64, path: u8, limit: usize, on_event: F) -> Summary {
        let s = self.lose_in_flight(now, limit, Some(path), on_event);
        self.pto_count = 0;
        s
    }

    /// Lose up to `limit` packets in flight, oldest first, skipping those sent on `keep`.
    fn lose_in_flight<F: FnMut(Event<'_>)>(
        &mut self,
        now: u64,
        limit: usize,
        keep: Option<u8>,
        mut on_event: F,
    ) -> Summary {
        self.clock = self.clock.max(now);
        let mut s = Summary::default();
        let mut i = 0;
        while let Some(slot) = self.ring.get_mut(i) {
            i += 1;
            if slot.state != super::sent::State::InFlight || keep == Some(slot.sent.path) {
                continue;
            }
            if s.lost_packets as usize >= limit {
                break;
            }
            slot.state = super::sent::State::Lost(now);
            let sent = slot.sent;
            let size = u64::from(sent.size);
            s.lost_packets += 1;
            s.lost_bytes += size;
            self.acct.in_flight -= size;
            self.acct.lost += u128::from(size);
            self.in_flight_packets -= 1;
            on_event(Event::Lost {
                pn: sent.pn,
                size: sent.size,
                frames: &sent.frames,
                requeue: !sent.is_repair && !sent.is_mtu_probe,
                mtu_probe: sent.is_mtu_probe,
            });
        }
        s
    }

    /// When the peer was last heard (an authenticated packet), 0 before that.
    pub const fn last_heard(&self) -> u64 {
        self.last_heard
    }

    /// How the path is doing.
    ///
    /// `Dead` needs 10 probe timeouts and silence of at least `max(20 s if the minimum round trip is 250 ms or more
    /// or the node is thin, 8 x smoothed round trip)`; the smoothed round trip counts as 0 before a sample.
    /// `Degraded` is 3 or more probe timeouts.
    pub fn health(&self, now: u64) -> Health {
        let slow = self.rtt.is_long_rtt() || self.is_thin();
        let srtt = if self.rtt.has_sample() { self.rtt.smoothed() } else { 0 };
        let need = if slow { GIVE_UP_SILENCE_SLOW } else { 0 }.max(srtt.saturating_mul(GIVE_UP_SILENCE_RTTS));
        if self.pto_count >= PTO_GIVE_UP && now.saturating_sub(self.last_heard) >= need {
            Health::Dead
        } else if self.pto_count >= PTO_TELL_ENDPOINT {
            Health::Degraded
        } else {
            Health::Healthy
        }
    }
}
