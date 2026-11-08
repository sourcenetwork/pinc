//! Tail repair: one extra packet that re-carries the last data when the send queue drains on a lossy direct path.
//!
//! The connection feeds every ack-eliciting packet it builds on a direct path (while the loss estimate is at least
//! [`REPAIR_THRESHOLD`](super::REPAIR_THRESHOLD) and the connection is at least 2 s old) to [`TailRepair::on_packet`],
//! saying whether the packet carried plain stream bytes (whole frames of at most [`REPAIR_FRAME_BYTES`], nothing
//! backed by a value source) or something a repair cannot re-carry. When the queue drains the connection asks [`TailRepair::on_drain`]; it answers with the
//! packet number to repair only after a burst of exactly one packet that carried plain bytes, and the repair is sent
//! at once. The connection then reads that packet's frames with [`Recovery::sent_frames`](super::Recovery::sent_frames),
//! skips every range already acknowledged, and puts whole frames, newest first, into one packet of at most
//! [`REPAIR_PACKET_BYTES`] of payload (`min(mtu - 23, 600)`), flagged as a repair packet so its loss is neither
//! retransmitted nor a congestion signal.
//!
//! Invariant: the burst counter saturates at 2, so any burst longer than one packet forgets the candidate for good
//! until the next drain.

/// The longest burst, in packets, that can still be repaired.
pub const REPAIR_BURST: u32 = 1;
/// The longest stream frame a repair re-carries, and the most payload bytes in a repair packet.
pub const REPAIR_FRAME_BYTES: u32 = 600;
/// The most payload bytes in one repair packet before the path datagram size is considered.
pub const REPAIR_PACKET_BYTES: u32 = 600;
/// The bytes the short header, the packet number and the authentication tag take from a repair packet's room.
pub const REPAIR_OVERHEAD: u32 = 23;

/// The burst bookkeeping of one connection.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct TailRepair {
    burst: u32,
    candidate: Option<u64>,
}

impl TailRepair {
    /// A tracker with no burst.
    pub const fn new() -> Self {
        Self {
            burst: 0,
            candidate: None,
        }
    }

    /// Note one ack-eliciting packet `pn` just built. `has_plain` is true when it carried at least one stream frame
    /// with bytes or a stream end; `ineligible` is true when any of its stream frames could not be re-carried (longer
    /// than [`REPAIR_FRAME_BYTES`], or backed by a value source), which ends the candidate for this burst.
    pub fn on_packet(&mut self, pn: u64, has_plain: bool, ineligible: bool) {
        self.burst = (self.burst + 1).min(REPAIR_BURST + 1);
        if ineligible {
            self.burst = REPAIR_BURST + 1;
        }
        if self.burst > REPAIR_BURST {
            self.candidate = None;
        } else if has_plain {
            self.candidate = Some(pn);
        }
    }

    /// The send queue drained: the packet to repair, if the burst was one plain packet. Resets the tracker.
    pub fn on_drain(&mut self) -> Option<u64> {
        let c = self.candidate;
        *self = Self::new();
        c
    }
}
