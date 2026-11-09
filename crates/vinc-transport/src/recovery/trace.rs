//! Test-only observation of the recovery engine, for trace validation (cargo feature `trace`, off by default).
//!
//! [`Recovery::trace_view`] shows the state the loss recovery works on: the sent ring slot by slot, the byte
//! accounts, the round-trip estimate, the probe timer, the paths and the reorder lens. Nothing here is compiled
//! without the feature, and nothing here feeds back into the engine.

use alloc::vec::Vec;

use super::engine::{PathKind, Recovery};
use super::sent::{State, is_ghost_data};

/// One slot of the sent ring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlotView {
    /// The packet number.
    pub pn: u64,
    /// The send time.
    pub time: u64,
    /// The datagram size.
    pub size: u32,
    /// The path the packet left on.
    pub path: u8,
    /// A repair packet.
    pub repair: bool,
    /// A path MTU probe.
    pub probe: bool,
    /// Per frame: whether a ghost keeps it (stream data without an end).
    pub frames: Vec<bool>,
    /// 0 in flight, 1 declared lost (a ghost), 2 done.
    pub state: u8,
    /// When the packet was declared lost (0 unless the state is 1).
    pub lost_at: u64,
}

/// The state of a recovery engine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecoveryView {
    /// The ring, oldest first.
    pub slots: Vec<SlotView>,
    /// The largest packet number sent.
    pub largest_sent: Option<u64>,
    /// The largest packet number acknowledged.
    pub largest_acked: Option<u64>,
    /// Bytes of recorded packets sent, acknowledged, declared lost, and in flight.
    pub bytes: [u64; 4],
    /// Recorded packets in flight.
    pub in_flight_packets: u32,
    /// The loss timer.
    pub loss_time: Option<u64>,
    /// Consecutive probe timeouts.
    pub pto_count: u32,
    /// When the probe timer last fired.
    pub last_pto: u64,
    /// The peer sleeps.
    pub asleep: bool,
    /// The link is down.
    pub link_down: bool,
    /// When the peer was last heard.
    pub last_heard: u64,
    /// The newest time any call carried.
    pub clock: u64,
    /// The node's peak round trip and the handshake round trip.
    pub node_rtt: [u64; 2],
    /// The latest, smoothed, variation and minimum round trip, and whether the estimate has a sample.
    pub rtt: (Option<u64>, u64, u64, Option<u64>, bool),
    /// Per path: relay or not.
    pub relay: Vec<bool>,
    /// Per path: the round trip last measured on it.
    pub path_rtt: Vec<u64>,
    /// Per path: the reorder extent and when it was last seen.
    pub reorder: Vec<(u64, Option<u64>)>,
    /// The active path.
    pub active: u8,
    /// When the active path last changed.
    pub flip_at: Option<u64>,
    /// The send times of lost packets kept for a late acknowledgement, in insertion order.
    pub late_sends: Vec<(u64, u64)>,
    /// The packet number whose loss by the first probe timeout saved the window.
    pub saved: Option<u64>,
    /// When the ghosts were last looked at.
    pub ghost_scan: u64,
    /// The send time of the largest acknowledged packet.
    pub largest_acked_time: u64,
    /// The next time a timer must run.
    pub next_timeout: Option<u64>,
}

impl<const N: usize> Recovery<N> {
    /// The state of the engine, for trace validation.
    pub fn trace_view(&self) -> RecoveryView {
        let slots = (0..N)
            .map_while(|i| self.ring.get(i))
            .map(|s| {
                let (state, lost_at) = match s.state {
                    State::InFlight => (0, 0),
                    State::Lost(at) => (1, at),
                    State::Done => (2, 0),
                };
                SlotView {
                    pn: s.sent.pn,
                    time: s.sent.time,
                    size: s.sent.size,
                    path: s.sent.path,
                    repair: s.sent.is_repair,
                    probe: s.sent.is_mtu_probe,
                    frames: s.sent.frames.iter().map(is_ghost_data).collect(),
                    state,
                    lost_at,
                }
            })
            .collect();
        RecoveryView {
            slots,
            largest_sent: self.largest_sent,
            largest_acked: self.largest_acked,
            bytes: [
                u64::try_from(self.acct.sent).unwrap_or(u64::MAX),
                u64::try_from(self.acct.acked).unwrap_or(u64::MAX),
                u64::try_from(self.acct.lost).unwrap_or(u64::MAX),
                self.acct.in_flight,
            ],
            in_flight_packets: self.in_flight_packets,
            loss_time: self.loss_time,
            pto_count: self.pto_count,
            last_pto: self.last_pto,
            asleep: self.asleep,
            link_down: self.link_down,
            last_heard: self.last_heard,
            clock: self.clock,
            node_rtt: [self.tgr, self.lrtt],
            rtt: (
                self.rtt.latest(),
                self.rtt.smoothed(),
                self.rtt.rttvar(),
                self.rtt.min_rtt(),
                self.rtt.has_sample(),
            ),
            relay: self.paths.iter().map(|k| *k == PathKind::Relay).collect(),
            path_rtt: self.path_rtt.to_vec(),
            reorder: self.reorder.iter().map(|r| (r.extent, r.seen)).collect(),
            active: self.active,
            flip_at: self.flip_at,
            late_sends: self.late_sends.entries(),
            saved: self.saved_window.map(|w| w.pn),
            ghost_scan: self.ghost_scan,
            largest_acked_time: self.largest_acked_time,
            next_timeout: self.next_timeout(),
        }
    }
}
