//! The recovery engine of one connection: sent ring, round-trip estimate, loss detection, probe timer, spurious-loss
//! repair, congestion control and pacing behind one interface.
//!
//! Acknowledged ranges come in as inclusive packet-number ranges (largest first) plus the reported delay; what
//! happened to each packet goes out through an [`Event`] callback, so nothing is buffered or allocated.
//!
//! Invariants:
//! - for packets flagged in flight, `bytes_sent == bytes_acked + bytes_in_flight + bytes_lost` at every call
//!   boundary; a late acknowledgement moves a packet's bytes from lost to acked;
//! - the cumulative byte counters are `u128` (at most 2^64 packets of at most 2^32 bytes cannot overflow it) and the
//!   in-flight counter is `u64` (at most `N <= 2^31` packets of at most 2^32 bytes: below 2^63);
//! - an acknowledgement grows the window only for packets sent while the window was in use (bytes in flight, with
//!   the packet, at least cwnd minus one segment); acknowledgements of packets sent application limited pause the
//!   cubic epoch instead;
//! - persistent congestion (RFC 9002 section 7.6) collapses the window to its minimum and clears the saved response,
//!   so a later spurious-loss undo cannot restore it; it needs a round-trip sample taken before the lost packets
//!   were sent and never counts a repair packet or path MTU probe;
//! - a repair packet or a path MTU probe that is lost is reported with `requeue == false` (the probe with
//!   `mtu_probe == true`) and never reduces the window.

use core::ops::RangeInclusive;

use super::cubic::{AckInput, Cubic, MAX_MSS, MIN_MSS};
use super::frame_ref::FrameRefs;
use super::math::sat;
use super::pacer::Pacer;
use super::rtt::RttEstimator;
use super::sent::{Sent, SentRing, State};
use super::{LONG_RTT, MAX_PACKET_NUMBER, MS, RecoveryError, SECOND};

/// The most paths one connection tracks.
pub const MAX_PATHS: usize = 8;
const PACKET_THRESHOLD: u64 = 3;
const OLD_PATH_RTT_FACTOR: u64 = 4;
const OLD_PATH_EXTRA: u64 = 50 * MS;
const RELAY_MIN_DELAY: u64 = 1_500 * MS;
const MAX_RTT_SAMPLE_LATE: u64 = 4 * SECOND;
const PTO_FLOOR_VAR: u64 = MS;
const PTO_MAX_ACK_DELAY: u64 = 25 * MS;
const PTO_MAX_SHIFT: u32 = 6;
const PTO_CAP: u64 = 2 * SECOND;
const PERSISTENT_PTOS: u64 = 3;
const PTO_TELL_ENDPOINT: u32 = 3;
const PTO_GIVE_UP: u32 = 10;
const GIVE_UP_SILENCE_SLOW: u64 = 20 * SECOND;

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
    /// Packets newly acknowledged (late acknowledgements included).
    pub acked_packets: u32,
    /// Bytes newly acknowledged that were in flight.
    pub acked_bytes: u64,
    /// Packets acknowledged after being declared lost.
    pub late_acked_packets: u32,
    /// Packets declared lost.
    pub lost_packets: u32,
    /// Bytes declared lost that were in flight.
    pub lost_bytes: u64,
    /// Whether a congestion response was undone because every loss of its episode was spurious.
    pub congestion_undone: bool,
    /// Whether the losses amounted to persistent congestion and the window collapsed to its minimum.
    pub persistent_congestion: bool,
}

/// What a timer expiry asks for.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Timeout {
    /// Packets declared lost by this expiry.
    pub summary: Summary,
    /// The number of probe packets to send now (0 when the expiry only detected loss).
    pub probes: u8,
}

/// How the path is doing, from consecutive probe timeouts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Health {
    /// Fewer than 3 consecutive probe timeouts.
    Healthy,
    /// 3 or more probe timeouts: tell the endpoint.
    Degraded,
    /// 10 or more probe timeouts (and, on a long-RTT path, 20 s of silence): give up.
    Dead,
}

#[derive(Debug, Clone, Copy, Default)]
struct Account {
    sent: u128,
    acked: u128,
    lost: u128,
    in_flight: u64,
}

/// What the ranges of one acknowledgement turned up.
#[derive(Debug, Default)]
struct AckScan {
    /// The largest packet number the acknowledgement names.
    frame_largest: Option<u64>,
    /// The largest newly acknowledged packet: (number, send time, ack-eliciting, was declared lost).
    newest: Option<(u64, u64, bool, bool)>,
    growth: u64,
    /// Whether a packet sent while the window was not in use was acknowledged.
    app_limited: bool,
    new_eliciting: bool,
}

#[derive(Debug, Clone, Copy, Default)]
struct Episode {
    lost: u32,
    spurious: u32,
    closed: bool,
}

/// Loss recovery for one connection, with room for `MAX_IN_FLIGHT` sent packets.
#[derive(Debug, Clone)]
pub struct Recovery<const MAX_IN_FLIGHT: usize> {
    ring: SentRing<MAX_IN_FLIGHT>,
    rtt: RttEstimator,
    cc: Cubic,
    pacer: Pacer,
    acct: Account,
    episode: Episode,
    eliciting_in_flight: u32,
    largest_sent: Option<u64>,
    largest_acked: Option<u64>,
    last_eliciting_sent: u64,
    loss_time: Option<u64>,
    pto_count: u32,
    asleep: bool,
    last_heard: u64,
    paths: [PathKind; MAX_PATHS],
    active: u8,
    first_sample_at: Option<u64>,
    pc_barrier: Option<u64>,
}

impl<const N: usize> Recovery<N> {
    /// A recovery state with segment size `mss` (clamped to 1200..=65535), path 0 active and direct.
    pub fn new(mss: u64) -> Self {
        let cc = Cubic::new(mss);
        let mut r = Self {
            ring: SentRing::new(),
            rtt: RttEstimator::new(),
            cc,
            pacer: Pacer::new(cc.mss()),
            acct: Account::default(),
            episode: Episode::default(),
            eliciting_in_flight: 0,
            largest_sent: None,
            largest_acked: None,
            last_eliciting_sent: 0,
            loss_time: None,
            pto_count: 0,
            asleep: false,
            last_heard: 0,
            paths: [PathKind::Direct; MAX_PATHS],
            active: 0,
            first_sample_at: None,
            pc_barrier: None,
        };
        r.refresh_pacer();
        r
    }

    // ---- read access ----

    /// The round-trip estimator.
    pub const fn rtt(&self) -> &RttEstimator {
        &self.rtt
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

    /// Bytes sent and neither acknowledged nor declared lost.
    pub const fn bytes_in_flight(&self) -> u64 {
        self.acct.in_flight
    }

    /// Bytes still allowed by the congestion window.
    pub const fn cwnd_available(&self) -> u64 {
        self.cc.cwnd().saturating_sub(self.acct.in_flight)
    }

    /// Cumulative bytes of in-flight packets sent.
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

    /// The largest packet number sent.
    pub const fn largest_sent(&self) -> Option<u64> {
        self.largest_sent
    }

    /// The largest packet number the peer acknowledged.
    pub const fn largest_acked(&self) -> Option<u64> {
        self.largest_acked
    }

    /// Ack-eliciting packets in flight.
    pub const fn ack_eliciting_in_flight(&self) -> u32 {
        self.eliciting_in_flight
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

    /// Make `path` the active path. Congestion control, the round-trip estimate and the pacer restart, except on a
    /// switch from one relay path to another. Returns whether they restarted.
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
        self.cc.restart();
        self.rtt.reset();
        self.first_sample_at = None;
        self.pc_barrier = None;
        self.pacer = Pacer::new(self.cc.mss());
        self.pto_count = 0;
        self.episode = Episode::default();
        self.refresh_pacer();
        Ok(true)
    }

    /// Change the datagram size (clamped to 1200..=65535).
    pub fn set_max_datagram_size(&mut self, mss: u64) {
        self.cc.set_mss(mss.clamp(MIN_MSS, MAX_MSS));
        self.refresh_pacer();
    }

    /// While the peer sleeps or the link is down, a probe timeout does not grow the backoff or the counter.
    pub fn set_peer_asleep(&mut self, asleep: bool) {
        self.asleep = asleep;
    }

    /// Note that anything arrived from the peer at `now` (restarts the silence clock).
    pub fn note_peer_activity(&mut self, now: u64) {
        self.last_heard = self.last_heard.max(now);
    }

    fn refresh_pacer(&mut self) {
        self.pacer.set_rate(self.cc.cwnd(), self.rtt.smoothed(), self.cc.mss());
    }

    // ---- sending ----

    /// Record a sent packet.
    ///
    /// # Errors
    /// [`RecoveryError::PacketNumberOutOfRange`], [`RecoveryError::PacketNumberNotIncreasing`],
    /// [`RecoveryError::PathOutOfRange`], or [`RecoveryError::RingFull`] when the ring is full of packets in flight.
    pub fn on_packet_sent(&mut self, p: Sent) -> Result<(), RecoveryError> {
        if p.pn > MAX_PACKET_NUMBER {
            return Err(RecoveryError::PacketNumberOutOfRange);
        }
        if usize::from(p.path) >= MAX_PATHS {
            return Err(RecoveryError::PathOutOfRange);
        }
        if self.largest_sent.is_some_and(|l| p.pn <= l) {
            return Err(RecoveryError::PacketNumberNotIncreasing);
        }
        self.ring.trim(p.time);
        let in_use = p.in_flight
            && self.acct.in_flight.saturating_add(u64::from(p.size)) >= self.cc.cwnd().saturating_sub(self.cc.mss());
        if !self.ring.push(p, in_use) {
            return Err(RecoveryError::RingFull);
        }
        self.largest_sent = Some(p.pn);
        if p.in_flight {
            self.acct.sent += u128::from(p.size);
            self.acct.in_flight += u64::from(p.size);
            self.pacer.on_sent(p.time, u64::from(p.size));
            if p.ack_eliciting {
                self.eliciting_in_flight += 1;
                self.last_eliciting_sent = p.time;
            }
        }
        Ok(())
    }

    // ---- acknowledgements ----

    /// Process an acknowledgement. `ranges` are inclusive packet-number ranges, largest first; `ack_delay` is the
    /// delay the peer reported, in nanoseconds. Every packet event goes to `on_event`.
    ///
    /// An acknowledgement of a packet number that is not in flight is ignored. Each range costs a binary search plus
    /// one step per packet it covers in the ring, so the work is bounded by the ring size and the ranges given.
    ///
    /// # Errors
    /// [`RecoveryError::AckOfUnsentPacket`] if a range reaches above the largest packet sent;
    /// [`RecoveryError::InvalidAckRange`] if a range is reversed. Ranges before the bad one stay applied.
    pub fn on_ack_received<I, F>(
        &mut self,
        now: u64,
        ranges: I,
        ack_delay: u64,
        mut on_event: F,
    ) -> Result<Summary, RecoveryError>
    where
        I: IntoIterator<Item = RangeInclusive<u64>>,
        F: FnMut(Event<'_>),
    {
        let mut s = Summary::default();
        let mut scan = AckScan::default();
        for range in ranges {
            let (start, end) = (*range.start(), *range.end());
            if start > end {
                return Err(RecoveryError::InvalidAckRange);
            }
            if self.largest_sent.is_none_or(|l| end > l) {
                return Err(RecoveryError::AckOfUnsentPacket);
            }
            scan.frame_largest.get_or_insert(end);
            self.ack_range(start..=end, &mut scan, &mut s, &mut on_event);
        }
        let AckScan {
            frame_largest,
            newest,
            growth,
            app_limited,
            new_eliciting,
            ..
        } = scan;
        self.last_heard = self.last_heard.max(now);
        if let Some(l) = frame_largest {
            self.largest_acked = self.largest_acked.max(Some(l));
        }
        let mut sample = None;
        if let Some((pn, time, true, late)) = newest
            && Some(pn) == frame_largest
        {
            let raw = now.saturating_sub(time);
            let raw = if late { raw.min(MAX_RTT_SAMPLE_LATE) } else { raw };
            self.rtt.update(raw, ack_delay);
            self.first_sample_at.get_or_insert(now);
            sample = Some(raw);
        }
        if new_eliciting {
            self.pto_count = 0;
        }
        if let (Some(largest_acked), Some(largest_sent)) = (newest.map(|n| n.0), self.largest_sent)
            && s.acked_bytes > 0
        {
            if app_limited {
                self.cc.on_app_limited(now);
            }
            self.cc.on_acked(&AckInput {
                now,
                growth_bytes: growth,
                acked_bytes: s.acked_bytes,
                largest_acked,
                largest_sent,
                rtt_sample: sample,
                min_rtt: self.rtt.min_rtt(),
            });
        }
        self.detect_lost(now, &mut s, &mut on_event);
        self.finish(now, &mut s);
        Ok(s)
    }

    /// Acknowledge every slot with a packet number in `range`.
    fn ack_range<F: FnMut(Event<'_>)>(
        &mut self,
        range: RangeInclusive<u64>,
        scan: &mut AckScan,
        s: &mut Summary,
        on_event: &mut F,
    ) {
        let recovery_start = self.cc.recovery_start();
        let mut i = self.ring.lower_bound(*range.start());
        while let Some(slot) = self.ring.get_mut(i) {
            if slot.sent.pn > *range.end() {
                break;
            }
            i += 1;
            let sent = slot.sent;
            let late = match slot.state {
                State::Done => continue,
                State::InFlight => false,
                State::Lost(_) => true,
            };
            let counted = slot.counted;
            let slot_limited = slot.cwnd_limited;
            slot.state = State::Done;
            let size = u64::from(sent.size);
            s.acked_packets += 1;
            if late {
                s.late_acked_packets += 1;
                if sent.in_flight {
                    self.acct.lost -= u128::from(size);
                    self.acct.acked += u128::from(size);
                }
                if counted {
                    self.episode.spurious = self.episode.spurious.saturating_add(1);
                }
                on_event(Event::LateAcked {
                    pn: sent.pn,
                    frames: &sent.frames,
                });
            } else {
                if sent.in_flight {
                    self.acct.in_flight -= size;
                    self.acct.acked += u128::from(size);
                    s.acked_bytes += size;
                    if sent.ack_eliciting {
                        self.eliciting_in_flight -= 1;
                    }
                    let after = recovery_start.is_none_or(|rs| sent.time > rs);
                    if after && slot_limited {
                        scan.growth += size;
                    }
                    if after && !slot_limited {
                        scan.app_limited = true;
                    }
                    if recovery_start.is_some() && after {
                        self.episode.closed = true;
                    }
                }
                on_event(Event::Acked {
                    pn: sent.pn,
                    size: sent.size,
                    frames: &sent.frames,
                    mtu_probe: sent.is_mtu_probe,
                });
            }
            scan.new_eliciting |= sent.ack_eliciting;
            if scan.newest.is_none_or(|n| sent.pn > n.0) {
                scan.newest = Some((sent.pn, sent.time, sent.ack_eliciting, late));
            }
        }
    }

    /// Declare lost every in-flight packet below the largest acknowledged that crossed a threshold, and arm the loss
    /// timer for the next one to cross.
    ///
    /// vertexia: scans from the ring head to the largest acknowledged packet on every acknowledgement, O(ring);
    /// an index of in-flight packets would make it O(losses) if profiles show it.
    fn detect_lost<F: FnMut(Event<'_>)>(&mut self, now: u64, s: &mut Summary, on_event: &mut F) {
        self.loss_time = None;
        let Some(largest_acked) = self.largest_acked else {
            return;
        };
        let rtt = self.rtt.latest().max(self.rtt.smoothed());
        let base_delay = sat(u128::from(rtt) * 9 / 8).max(MS);
        let old_delay = rtt.saturating_mul(OLD_PATH_RTT_FACTOR).saturating_add(OLD_PATH_EXTRA);
        let srtt = self.rtt.smoothed();
        let min_rtt = self.rtt.min_rtt();
        let (paths, active) = (self.paths, self.active);
        let mut i = 0;
        while let Some(slot) = self.ring.get_mut(i) {
            if slot.sent.pn > largest_acked {
                break;
            }
            i += 1;
            if slot.state != State::InFlight {
                continue;
            }
            let sent = slot.sent;
            let kind = paths.get(usize::from(sent.path)).copied().unwrap_or(PathKind::Direct);
            let (by_count, delay) = if sent.path == active {
                (kind == PathKind::Direct, base_delay)
            } else if kind == PathKind::Relay {
                (false, old_delay.max(RELAY_MIN_DELAY))
            } else {
                (false, old_delay)
            };
            let due = sent.time.saturating_add(delay);
            let lost = (by_count && largest_acked >= sent.pn.saturating_add(PACKET_THRESHOLD)) || now >= due;
            if !lost {
                self.loss_time = Some(self.loss_time.map_or(due, |t| t.min(due)));
                continue;
            }
            slot.state = State::Lost(now);
            let size = u64::from(sent.size);
            s.lost_packets += 1;
            let congestion = sent.in_flight && !sent.is_repair && !sent.is_mtu_probe;
            if sent.in_flight {
                self.acct.in_flight -= size;
                self.acct.lost += u128::from(size);
                s.lost_bytes += size;
                if sent.ack_eliciting {
                    self.eliciting_in_flight -= 1;
                }
            }
            if congestion {
                slot.counted = true;
                if self.cc.on_congestion_event(now, sent.time, srtt, min_rtt) {
                    self.episode = Episode {
                        lost: 1,
                        spurious: 0,
                        closed: false,
                    };
                } else {
                    self.episode.lost = self.episode.lost.saturating_add(1);
                }
            }
            on_event(Event::Lost {
                pn: sent.pn,
                size: sent.size,
                frames: &sent.frames,
                requeue: !sent.is_repair && !sent.is_mtu_probe,
                mtu_probe: sent.is_mtu_probe,
            });
        }
    }

    /// Persistent congestion: ack-eliciting packets sent over a period longer than three probe timeouts (without
    /// backoff) were all lost, with none acknowledged or still unresolved in between, and every one sent after the
    /// first round-trip sample. Repair packets and path MTU probes neither extend nor break a run. Returns the send
    /// time of the last lost packet of the run.
    fn persistent_congestion(&self) -> Option<u64> {
        let first_sample = self.first_sample_at?;
        let floor = self.pc_barrier.map_or(first_sample, |b| b.max(first_sample));
        let var = self.rtt.rttvar().saturating_mul(4).max(PTO_FLOOR_VAR);
        let span = self
            .rtt
            .smoothed()
            .saturating_add(var)
            .saturating_add(PTO_MAX_ACK_DELAY)
            .saturating_mul(PERSISTENT_PTOS);
        let mut run: Option<(u64, u64)> = None;
        let mut i = 0;
        while let Some(slot) = self.ring.get(i) {
            i += 1;
            let sent = &slot.sent;
            if !sent.ack_eliciting || sent.is_repair || sent.is_mtu_probe {
                continue;
            }
            if matches!(slot.state, State::Lost(_)) && sent.time > floor {
                let (start, _) = run.unwrap_or((sent.time, sent.time));
                run = Some((start, sent.time));
                if sent.time.saturating_sub(start) > span {
                    return Some(sent.time);
                }
            } else {
                run = None;
            }
        }
        None
    }

    /// Undo a fully spurious congestion response, drop finished slots and refresh the pacer.
    fn finish(&mut self, now: u64, s: &mut Summary) {
        if s.lost_packets > 0
            && let Some(last) = self.persistent_congestion()
        {
            self.cc.on_persistent_congestion();
            self.episode = Episode::default();
            self.pc_barrier = Some(last);
            s.persistent_congestion = true;
        }
        let e = self.episode;
        if e.closed && e.lost > 0 && e.spurious == e.lost && self.cc.undo() {
            self.episode = Episode::default();
            s.congestion_undone = true;
        }
        self.ring.trim(now);
        self.refresh_pacer();
    }

    /// Declare every packet in flight lost with no congestion response and reset the probe backoff: the peer woke
    /// from sleep, the link came back, or early data was rejected. Each packet is reported as lost and to be requeued.
    pub fn flush_in_flight<F: FnMut(Event<'_>)>(&mut self, now: u64, mut on_event: F) -> Summary {
        let mut s = Summary::default();
        let mut i = 0;
        while let Some(slot) = self.ring.get_mut(i) {
            i += 1;
            if slot.state != State::InFlight {
                continue;
            }
            slot.state = State::Lost(now);
            slot.counted = false;
            let sent = slot.sent;
            s.lost_packets += 1;
            if sent.in_flight {
                let size = u64::from(sent.size);
                self.acct.in_flight -= size;
                self.acct.lost += u128::from(size);
                s.lost_bytes += size;
                if sent.ack_eliciting {
                    self.eliciting_in_flight -= 1;
                }
            }
            on_event(Event::Lost {
                pn: sent.pn,
                size: sent.size,
                frames: &sent.frames,
                requeue: !sent.is_repair && !sent.is_mtu_probe,
                mtu_probe: sent.is_mtu_probe,
            });
        }
        self.loss_time = None;
        self.pto_count = 0;
        s
    }

    // ---- timers ----

    /// The probe timeout duration: srtt + max(4 x rttvar, 1 ms) + 25 ms, doubled per consecutive timeout (at most
    /// 6 doublings), capped at 2 s, or at max(2 s, 2 x srtt) on a long-RTT path.
    pub fn pto_duration(&self) -> u64 {
        let var = self.rtt.rttvar().saturating_mul(4).max(PTO_FLOOR_VAR);
        let base = self
            .rtt
            .smoothed()
            .saturating_add(var)
            .saturating_add(PTO_MAX_ACK_DELAY);
        let shifted = base.saturating_mul(1u64 << self.pto_count.min(PTO_MAX_SHIFT));
        let cap = if self.rtt.min_rtt().is_some_and(|m| m >= LONG_RTT) {
            PTO_CAP.max(self.rtt.smoothed().saturating_mul(2))
        } else {
            PTO_CAP
        };
        shifted.min(cap)
    }

    fn pto_deadline(&self) -> Option<u64> {
        (self.eliciting_in_flight > 0).then(|| self.last_eliciting_sent.saturating_add(self.pto_duration()))
    }

    /// The next time [`Self::on_timeout`] must run: the loss timer, or the probe timer when no loss is pending.
    pub fn next_timeout(&self) -> Option<u64> {
        self.loss_time.or_else(|| self.pto_deadline())
    }

    /// Run the expired timer. A loss timer detects losses; a probe timer asks for 1 probe on the first expiry and 2
    /// after, and grows the backoff unless the peer is marked asleep.
    pub fn on_timeout<F: FnMut(Event<'_>)>(&mut self, now: u64, mut on_event: F) -> Timeout {
        let mut out = Timeout::default();
        if self.loss_time.is_some_and(|t| t <= now) {
            self.detect_lost(now, &mut out.summary, &mut on_event);
            self.finish(now, &mut out.summary);
            return out;
        }
        if self.pto_deadline().is_some_and(|d| d <= now) {
            if !self.asleep {
                self.pto_count = self.pto_count.saturating_add(1);
            }
            out.probes = if self.pto_count <= 1 { 1 } else { 2 };
        }
        out
    }

    /// How the path is doing.
    pub fn health(&self, now: u64) -> Health {
        let silent = !self.rtt.is_long_rtt() || now.saturating_sub(self.last_heard) >= GIVE_UP_SILENCE_SLOW;
        if self.pto_count >= PTO_GIVE_UP && silent {
            Health::Dead
        } else if self.pto_count >= PTO_TELL_ENDPOINT {
            Health::Degraded
        } else {
            Health::Healthy
        }
    }
}
