//! Acknowledgement handling for [`Recovery`]: which packets a range acknowledges, the round-trip sample, the rate
//! and window updates, and the late-acknowledgement rules.
//!
//! The steps of one acknowledgement, in order:
//! 1. each range is checked against the largest packet sent; if the first probe's packet is in it, the window saved
//!    before that probe is restored (the probe was spurious);
//! 2. packets in flight inside a range are acknowledged; a packet already declared lost (a ghost) inside a range is
//!    reported as late-acknowledged and moves its bytes from lost to acknowledged, but is not a new acknowledgement;
//! 3. when the acknowledgement's largest packet had been declared lost, nothing newer is acknowledged and no round
//!    trip sample exists yet, that packet's send time (at most 4 s old) seeds the estimate;
//! 4. if nothing was newly acknowledged, stop; otherwise the sample is taken (the largest newly acknowledged packet,
//!    if it is the acknowledgement's largest), the probe count resets, the congestion controller learns the bytes and
//!    the sample, and loss detection runs.
//!
//! Overflow bounds: sums of packet sizes of at most `N <= 2^31` recorded packets of at most 2^32 bytes stay below
//! 2^63 in `u64`; byte totals are `u128`.

use core::ops::RangeInclusive;

use super::engine::{Event, Recovery, Summary};
use super::frame_ref::FrameRefs;
use super::sent::{GHOST_RETENTION, State, is_ghost_data};
use super::{RecoveryError, SECOND};

/// A late sample seeds the round trip only up to this age (4 s).
const MAX_LATE_SAMPLE: u64 = 4 * SECOND;

/// What the ranges of one acknowledgement turned up.
#[derive(Default)]
struct Scan {
    /// The largest packet number any range names.
    frame_largest: Option<u64>,
    /// The newest newly acknowledged packet: (number, send time, path).
    newest: Option<(u64, u64, u8)>,
}

impl<const N: usize> Recovery<N> {
    /// Process an acknowledgement. `ranges` are inclusive packet-number ranges, largest first. Every packet event goes
    /// to `on_event`. Acknowledgements carry no delay: the sample is used as measured.
    ///
    /// An acknowledgement of a packet number that is not in flight and not a ghost is ignored. Each range costs a
    /// binary search plus one step per packet it covers in the ring, so the work is bounded by the ring size and the
    /// ranges given.
    ///
    /// # Errors
    /// [`RecoveryError::AckOfUnsentPacket`] if a range reaches above the largest packet sent;
    /// [`RecoveryError::InvalidAckRange`] if a range is reversed. Ranges before the bad one stay applied.
    pub fn on_ack_received<I, F>(&mut self, now: u64, ranges: I, mut on_event: F) -> Result<Summary, RecoveryError>
    where
        I: IntoIterator<Item = RangeInclusive<u64>>,
        F: FnMut(Event<'_>),
    {
        self.clock = self.clock.max(now);
        let mut s = Summary::default();
        let mut scan = Scan::default();
        for range in ranges {
            let (start, end) = (*range.start(), *range.end());
            if start > end {
                return Err(RecoveryError::InvalidAckRange);
            }
            if self.largest_sent.is_none_or(|l| end > l) {
                return Err(RecoveryError::AckOfUnsentPacket);
            }
            scan.frame_largest = scan.frame_largest.max(Some(end));
            if let Some(t) = self.saved_window.filter(|t| range.contains(&t.pn)) {
                self.cc.restore(t.cwnd, t.ssthresh);
                self.saved_window = None;
            }
            self.ack_range(now, start..=end, &mut scan, &mut s, &mut on_event);
        }
        self.last_heard = self.last_heard.max(now);
        let Some(frame_largest) = scan.frame_largest else {
            return Ok(s);
        };
        self.largest_acked = self.largest_acked.max(Some(frame_largest));
        let lost_send_time = self.late_sends.take(frame_largest);
        if let Some(sent_at) = lost_send_time
            && scan.newest.is_none_or(|n| n.0 != frame_largest)
            && !self.rtt.has_sample()
        {
            self.pto_count = 0;
            scan.newest = Some((
                frame_largest,
                sent_at.max(now.saturating_sub(MAX_LATE_SAMPLE)),
                self.active,
            ));
        }
        let Some((newest_pn, newest_time, newest_path)) = scan.newest else {
            self.ring.trim(now);
            return Ok(s);
        };
        if newest_pn == frame_largest {
            let sample = now.saturating_sub(newest_time);
            self.rtt.update(sample);
            self.tgr = self.rtt.smoothed().max(self.tgr - (self.tgr >> 5));
            self.cc.on_rtt_sample(sample);
            if let Some(r) = self.path_rtt.get_mut(usize::from(newest_path)) {
                *r = self.rtt.smoothed();
            }
        }
        self.pto_count = 0;
        let input = self.ack_input(now, s.acked_bytes);
        self.cc.on_acked(&input);
        self.detect_lost(now, frame_largest, &mut s, &mut on_event);
        self.ring.trim(now);
        Ok(s)
    }

    /// Acknowledge every slot with a packet number in `range`.
    fn ack_range<F: FnMut(Event<'_>)>(
        &mut self,
        now: u64,
        range: RangeInclusive<u64>,
        scan: &mut Scan,
        s: &mut Summary,
        on_event: &mut F,
    ) {
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
                State::Lost(at) if now.saturating_sub(at) > GHOST_RETENTION => {
                    slot.state = State::Done;
                    continue;
                }
                State::Lost(_) => true,
            };
            slot.state = State::Done;
            let size = u64::from(sent.size);
            if late {
                s.late_acked_packets += 1;
                self.acct.lost -= u128::from(size);
                self.acct.acked += u128::from(size);
                // A late acknowledgement acts on the stream data frames the ghost kept, and on nothing else.
                let mut data = FrameRefs::new();
                for f in sent.frames.iter().filter(|f| is_ghost_data(f)) {
                    let _ = data.push(*f);
                }
                on_event(Event::LateAcked {
                    pn: sent.pn,
                    frames: &data,
                });
                continue;
            }
            s.acked_packets += 1;
            s.acked_bytes += size;
            self.acct.in_flight -= size;
            self.acct.acked += u128::from(size);
            self.in_flight_packets -= 1;
            on_event(Event::Acked {
                pn: sent.pn,
                size: sent.size,
                frames: &sent.frames,
                mtu_probe: sent.is_mtu_probe,
                repair: sent.is_repair,
            });
            if scan.newest.is_none_or(|n| sent.pn > n.0) {
                scan.newest = Some((sent.pn, sent.time, sent.path));
            }
        }
    }
}
