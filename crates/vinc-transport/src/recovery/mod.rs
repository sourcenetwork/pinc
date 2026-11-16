//! Loss recovery, acknowledgement policy, congestion control and pacing of one connection.
//!
//! Everything here is sans-IO: time is a monotonic `u64` of nanoseconds passed in, and nothing allocates, blocks or
//! reads a clock. Every table is bounded by a const generic or a constant.
//!
//! - [`ReceivedPackets`] records received packet numbers of one packet space in a bounded range set, drops
//!   duplicates, decides when to acknowledge and yields the ranges to report (largest first, at most 32).
//! - [`Recovery`] keeps the bounded ring of sent packets, estimates the round trip ([`RttEstimator`]), detects loss,
//!   runs the probe timer, and drives [`Cubic`] and the [`Pacer`]. Acknowledgements carry no delay and
//!   acknowledgement-only packets are not recorded.
//! - [`LossEstimate`] is the node-wide loss average that decides tail repair; it is lock-free and shared by
//!   reference. [`TailRepair`] decides which packet to repair when the send queue drains.
//!
//! Invariants:
//! - Sent packet numbers are strictly increasing; an acknowledgement above the largest sent number is a typed error
//!   ([`RecoveryError::AckOfUnsentPacket`]); acknowledging anything else not in flight is ignored.
//! - For recorded packets: bytes sent = bytes acknowledged + bytes in flight + bytes declared lost, always. A late
//!   acknowledgement moves bytes from lost to acknowledged.
//! - The congestion window never drops below [`MIN_CWND`] and never exceeds [`MAX_CWND`].
//! - All arithmetic is integer and cannot overflow or panic; the bound behind each product is documented where the
//!   product is computed (see `cubic`, `pacer`, `rtt`, `delivery` and `math`).

mod ack;
mod cubic;
mod delivery;
mod engine;
mod frame_ref;
mod loss;
mod loss_estimate;
mod math;
mod pacer;
mod pto;
mod recv;
mod round_exit;
mod rtt;
mod sent;
mod tail;
#[cfg(feature = "trace")]
pub mod trace;

pub use cubic::{
    AckInput, CONGESTION_BETA_SMALL, Cubic, GATE_SLACK_FAST, GATE_SLACK_MID, INITIAL_CWND, MAX_CWND, MAX_MSS, MIN_CWND,
    MIN_MSS,
};
pub use engine::{Event, Health, MAX_PATHS, PathKind, Recovery, Summary, Timeout};
pub use frame_ref::{FrameRef, FrameRefs, FrameRefsFull, MAX_FRAME_REFS};
pub use loss_estimate::{LossEstimate, REPAIR_MIN_AGE, REPAIR_THRESHOLD, SCALE as LOSS_SCALE};
pub use pacer::{BURST_PACKETS, Pacer, burst_budget};
pub use recv::{MAX_ACK_RANGES, ReceivedPackets, RxOutcome, RxPacket};
pub use rtt::{INITIAL_RTT, RttEstimator, max_ack_delay};
pub use sent::{SENT_PACKETS, Sent, SentRing};
pub use tail::{REPAIR_BURST, REPAIR_FRAME_BYTES, REPAIR_OVERHEAD, REPAIR_PACKET_BYTES, TailRepair};

use core::fmt;

/// One millisecond in nanoseconds.
pub const MS: u64 = 1_000_000;
/// One second in nanoseconds.
pub const SECOND: u64 = 1_000_000_000;
/// A path whose minimum round trip is at least this long (250 ms) is a long-RTT path.
pub const LONG_RTT: u64 = 250 * MS;
/// The largest packet number that can be tracked (2^62 - 1).
pub const MAX_PACKET_NUMBER: u64 = (1 << 62) - 1;

/// Whether `min_rtt` marks a long-RTT path.
pub(crate) fn is_long_rtt(min_rtt: Option<u64>) -> bool {
    min_rtt.is_some_and(|m| m >= LONG_RTT)
}

/// A protocol or usage error of the recovery state.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecoveryError {
    /// A packet number above 2^62 - 1.
    PacketNumberOutOfRange,
    /// An acknowledgement of a packet number that was never sent.
    AckOfUnsentPacket,
    /// An acknowledged range whose start is above its end.
    InvalidAckRange,
    /// A sent packet number that is not above the previous one.
    PacketNumberNotIncreasing,
    /// The sent ring is full of packets still in flight; stop sending until acknowledgements arrive.
    RingFull,
    /// A path id outside the supported paths.
    PathOutOfRange,
}

impl fmt::Display for RecoveryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::PacketNumberOutOfRange => "packet number out of range",
            Self::AckOfUnsentPacket => "acknowledgement of a packet that was never sent",
            Self::InvalidAckRange => "acknowledged range is reversed",
            Self::PacketNumberNotIncreasing => "packet number does not increase",
            Self::RingFull => "too many packets in flight",
            Self::PathOutOfRange => "path id out of range",
        })
    }
}

impl core::error::Error for RecoveryError {}
