//! Path datagram size: one probe of 1452 bytes after the handshake (only when the interface carries that much on the
//! path's address family), and on a path under 2 ms one probe at the interface's payload (its MTU less the IP and UDP
//! headers) up to 8952 when that is above 2904, each a PING plus PADDING packet of exactly the probed size.
//!
//! Only direct (UDP) paths are probed, never on a thin node, and not for 10 s after a wake or a link return. A path
//! is probed once: a lost probe is not retried, it waits for the next path event (a re-join that worked, a link
//! return, a new address, a re-validation) or for 10 minutes. A path whose address the endpoint's ledger still holds
//! is not probed, because the ledger would refuse the probe and a lost probe is not retried for 10 minutes; it is
//! probed once the address has answered. A path is not probed while the oldest packet in flight left on another path:
//! that recovery is timed first, and the probe's lone acknowledgement, held for the ack delay, would stretch its round
//! trip; the probe goes once those packets are acknowledged or declared lost. When a probe-timeout PING is
//! acknowledged while a full-size packet sent before it still is not one round trip later, the path drops to 1200,
//! because the signature is a path that carries small packets only.
//!
//! Invariants: at most one probe is in flight per path; a lost probe is not a congestion signal (recovery is told the
//! packet is a probe); the datagram size only rises to a size the peer confirmed (an acknowledgement or an echo) and
//! falls back to 1200 on the black-hole signature.

use pinc_crypto::Provider;

use super::Connection;
use super::config::{JUMBO_FLOOR, JUMBO_MTU, JUMBO_RTT, MIN_MTU, PROBE_MTU, interface_payload};
use super::path::Mtu;
use crate::recovery::{PathKind, SECOND};
use crate::stream::StreamSource;

/// How long a lost probe waits for a path event before the path is probed again.
pub(crate) const REPROBE_AFTER: u64 = 600 * SECOND;

/// Where the jumbo probe of a path stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Jumbo {
    /// Not tried since the last path event.
    Untried,
    /// Tried, or not worth trying (the interface does not go above 2904).
    Done,
}

/// What an acknowledgement of a probe did to the path's datagram size.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Rose {
    /// The acknowledgement named the probe in flight but the size did not rise: taken, no refusal.
    Flat,
    /// The size rose to this.
    New(u16),
}

/// What the probe decision needs to know about the path and the connection.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ProbeCtx {
    /// The configuration allows probing, the node is not thin, the path is direct, and the quiet period is over.
    pub(crate) allowed: bool,
    /// The MTU of the path's interface, IP and UDP headers included.
    pub(crate) interface_mtu: u16,
    /// The path is IPv6.
    pub(crate) v6: bool,
    /// The path's minimum round trip is under [`JUMBO_RTT`].
    pub(crate) low_latency: bool,
}

impl Mtu {
    /// A path not yet probed: the minimum size, nothing in flight.
    pub(crate) const fn new() -> Self {
        Self {
            current: MIN_MTU,
            inflight: None,
            flushed: None,
            probed: false,
            jumbo: Jumbo::Untried,
            retry_at: 0,
            started: false,
            last_big: None,
            big_acked: None,
            ping_big: None,
            suspect: None,
        }
    }

    /// The next size to probe, if one is due now.
    pub(crate) fn target(&self, ctx: ProbeCtx, now: u64) -> Option<u16> {
        if !ctx.allowed || !self.started || self.inflight.is_some() || self.retry_at > now {
            return None;
        }
        let room = interface_payload(ctx.interface_mtu, ctx.v6);
        if !self.probed {
            return (room >= PROBE_MTU && self.current < PROBE_MTU).then_some(PROBE_MTU);
        }
        let jumbo = room.min(JUMBO_MTU);
        (self.jumbo == Jumbo::Untried && self.current == PROBE_MTU && ctx.low_latency && jumbo > JUMBO_FLOOR)
            .then_some(jumbo)
    }

    /// A probe of `size` left as packet `pn`.
    pub(crate) fn probe_sent(&mut self, size: u16, pn: u64) {
        self.inflight = Some((size, pn));
        self.flushed = None;
        if size == PROBE_MTU && !self.probed {
            self.probed = true;
        } else {
            self.jumbo = Jumbo::Done;
        }
    }

    /// The datagram size rose to `size`.
    fn rose(&mut self, size: u16) -> Option<u16> {
        (size > self.current).then(|| {
            self.current = size;
            size
        })
    }

    /// A probe of `size` was acknowledged or echoed; the new datagram size if it rose. An acknowledgement of any
    /// other probe than the one in flight is no evidence about this path and raises nothing.
    pub(crate) fn raise(&mut self, size: u16) -> Option<u16> {
        if self.inflight.is_some_and(|(s, _)| s == size) {
            self.inflight = None;
        }
        self.rose(size)
    }

    /// The probe of `size` sent as `pn` was acknowledged; `None` when the acknowledgement names another probe than
    /// the one in flight (no evidence about this path, a refusal), otherwise what it did to the datagram size.
    pub(crate) fn acked(&mut self, size: u16, pn: u64) -> Option<Rose> {
        if self.inflight != Some((size, pn)) {
            return None;
        }
        self.inflight = None;
        Some(match self.rose(size) {
            Some(new) => Rose::New(new),
            None => Rose::Flat,
        })
    }

    /// The probe of `size` sent as `pn` was declared lost: it waits for the next path event or [`REPROBE_AFTER`].
    /// The loss of any other probe than the one in flight is refused.
    pub(crate) fn probe_lost(&mut self, size: u16, pn: u64, now: u64) -> bool {
        if self.inflight != Some((size, pn)) {
            return false;
        }
        self.inflight = None;
        self.retry_at = now.saturating_add(REPROBE_AFTER);
        if size > PROBE_MTU {
            self.jumbo = Jumbo::Done;
        }
        true
    }

    /// A flush took the probe of `size` sent as `pn`: its size and packet number are kept, so its acknowledgement
    /// can still raise the path, and the probe is owed again at once. The flush of any other probe than the one in
    /// flight is refused.
    pub(crate) fn flush(&mut self, size: u16, pn: u64) -> bool {
        if self.inflight != Some((size, pn)) {
            return false;
        }
        self.inflight = None;
        self.flushed = Some((size, pn));
        true
    }

    /// The probe a flush took, of `size` sent as `pn`, was acknowledged after all; the new datagram size if it rose.
    pub(crate) fn flushed_acked(&mut self, pn: u64) -> Option<u16> {
        let (size, marked) = self.flushed?;
        if marked != pn {
            return None;
        }
        self.flushed = None;
        self.rose(size)
    }

    /// A path event happened: probe again. The probe a flush took stays marked: its acknowledgement is still owed.
    pub(crate) fn event(&mut self) {
        self.probed = false;
        self.jumbo = Jumbo::Untried;
        self.retry_at = 0;
    }

    /// The last probe-timeout PING was acknowledged; `rtt` is the smoothed round trip, 0 while unknown.
    pub(crate) fn black_hole(&mut self, now: u64, rtt: u64) {
        let Some(big) = self.ping_big else { return };
        if self.current <= MIN_MTU || self.big_acked.is_some_and(|a| a >= big) {
            return;
        }
        self.suspect = Some((big, now.saturating_add(rtt)));
    }

    /// Settle a black-hole suspicion; true when the path dropped to the minimum size.
    pub(crate) fn black_hole_check(&mut self, now: u64) -> bool {
        let Some((big, at)) = self.suspect else { return false };
        if self.big_acked.is_some_and(|a| a >= big) || self.current <= MIN_MTU {
            self.suspect = None;
            return false;
        }
        if now < at {
            return false;
        }
        self.suspect = None;
        self.current = MIN_MTU;
        self.inflight = None;
        // The path was condemned for carrying small packets only: the mark of the probe a flush took is stale
        // evidence against that, and its acknowledgement, arriving late, raises nothing.
        self.flushed = None;
        self.last_big = None;
        self.ping_big = None;
        self.retry_at = now.saturating_add(REPROBE_AFTER);
        self.probed = true;
        self.jumbo = Jumbo::Done;
        true
    }
}

conn_impl! {
    /// The next size to probe on path `i`, if one is due now.
    pub(super) fn mtu_target(&self, i: usize, now: u64) -> Option<u16> {
        let p = self.paths.get(i)?;
        let ctx = ProbeCtx {
            allowed: self.cfg.probe_mtu && !self.cfg.thin && p.info.kind == PathKind::Direct && now >= self.life.qr_until,
            interface_mtu: p.info.interface_mtu,
            v6: p.info.v6,
            low_latency: self.rec.rtt().min_rtt().is_some_and(|r| r < JUMBO_RTT),
        };
        p.mtu.target(ctx, now)
    }

    /// Note that a probe of `size` left on path `i` as packet `pn`.
    pub(super) fn mtu_probe_sent(&mut self, i: usize, size: u16, pn: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.mtu.probe_sent(size, pn);
    }

    /// A probe of `size` was acknowledged on path `i`: the path carries it. An acknowledgement naming another probe
    /// than the one in flight there is refused and counted; one naming the probe in flight but not raising the size
    /// is taken, and no refusal.
    pub(super) fn mtu_acked(&mut self, i: usize, size: u16, pn: u64) {
        let active = i == self.paths.active;
        let Some(p) = self.paths.get_mut(i) else { return };
        match p.mtu.acked(size, pn) {
            Some(Rose::New(new)) if active => self.rec.set_max_datagram_size(u64::from(new)),
            Some(_) => {}
            None => self.stats.probe_outcomes_dropped += 1,
        }
    }

    /// A probe of `size` sent as `pn` was declared lost on path `i`: it waits for the next path event or
    /// [`REPROBE_AFTER`]. The loss of another probe than the one in flight there is refused and counted.
    pub(super) fn mtu_probe_lost(&mut self, i: usize, size: u16, pn: u64, now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        if !p.mtu.probe_lost(size, pn, now) {
            self.stats.probe_outcomes_dropped += 1;
        }
    }

    /// A flush took the probe of `size` sent as `pn` on path `i`: its size and packet number are kept for its
    /// acknowledgement. The flush of another probe than the one in flight there is refused and counted.
    pub(super) fn mtu_flushed(&mut self, i: usize, size: u16, pn: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        if !p.mtu.flush(size, pn) {
            self.stats.probe_outcomes_dropped += 1;
        }
    }

    /// An acknowledgement naming `pn` arrived: if it is the probe a flush took on path `i`, the path rises to the
    /// size the probe carried.
    pub(super) fn mtu_flush_raise(&mut self, i: usize, pn: u64) {
        let active = i == self.paths.active;
        let Some(p) = self.paths.get_mut(i) else { return };
        if let Some(new) = p.mtu.flushed_acked(pn)
            && active
        {
            self.rec.set_max_datagram_size(u64::from(new));
        }
    }

    /// The peer echoed `mtu` on path `i`: the path rises to it only when a probe of exactly that size is in flight
    /// there and the smaller of the jumbo size and what the path's interface carries can hold it. Any other echo is
    /// refused and counted.
    pub(super) fn mtu_echo(&mut self, i: usize, mtu: u16) {
        let Some(p) = self.paths.get(i) else { return };
        let ceiling = interface_payload(p.info.interface_mtu, p.info.v6).min(JUMBO_MTU);
        if p.mtu.inflight.is_none_or(|(size, _)| size != mtu) || mtu > ceiling {
            self.stats.probe_outcomes_dropped += 1;
            return;
        }
        self.mtu_raise(i, mtu);
    }

    /// The earliest time a path whose probe was lost is probed again.
    pub(super) fn mtu_deadline(&self) -> Option<u64> {
        self.paths
            .iter()
            .flat_map(|(_, p)| [p.mtu.retry_at, p.mtu.suspect.map_or(0, |(_, at)| at)])
            .filter(|t| *t > 0)
            .min()
    }

    /// A probe of `size` was acknowledged or echoed: the path carries it.
    pub(super) fn mtu_raise(&mut self, i: usize, size: u16) {
        let active = i == self.paths.active;
        let Some(p) = self.paths.get_mut(i) else { return };
        if let Some(new) = p.mtu.raise(size)
            && active
        {
            self.rec.set_max_datagram_size(u64::from(new));
        }
    }

    /// A path event happened on path `i`: probe it again.
    pub(super) fn mtu_event(&mut self, i: usize) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.mtu.event();
    }

    /// A path event happened on every path.
    pub(super) fn mtu_event_all(&mut self) {
        for i in 0..NP {
            self.mtu_event(i);
        }
    }

    /// The last probe-timeout PING was acknowledged. If a full-size packet sent before it is still unacknowledged
    /// the path is suspect, and [`mtu_black_hole_check`](Self::mtu_black_hole_check) decides one round trip later.
    /// The full-size retransmission that follows the PING does not matter: the evidence is the packet that preceded it.
    pub(super) fn mtu_black_hole(&mut self, now: u64) {
        let rtt = if self.rec.rtt().has_sample() { self.rec.rtt().smoothed() } else { 0 };
        let Some(p) = self.paths.active_mut() else { return };
        p.mtu.black_hole(now, rtt);
    }

    /// Settle a black-hole suspicion once its round trip has passed: if no full-size packet at or after the suspect one
    /// was acknowledged, the path carries small packets only. Drop the active path to the minimum size.
    pub(super) fn mtu_black_hole_check(&mut self, now: u64) {
        // A suspicion belongs to the path that carried the PING; once the connection has left that path nothing settles
        // it, and its deadline would stay in the past and keep the driver spinning.
        let active = self.paths.active;
        for (i, slot) in self.paths.slots.iter_mut().enumerate() {
            if let Some(p) = slot.as_mut().filter(|_| i != active) {
                p.mtu.suspect = None;
            }
        }
        let Some(p) = self.paths.active_mut() else { return };
        if p.mtu.black_hole_check(now) {
            self.rec.set_max_datagram_size(u64::from(MIN_MTU));
            self.shed_extensions();
        }
    }

    /// Start discovery on every path once the handshake is done.
    pub(super) fn mtu_start(&mut self) {
        for p in self.paths.slots.iter_mut().flatten() {
            p.mtu.started = true;
        }
    }
}

/// Test-only driver of the path MTU state machine, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
pub(super) mod trace {
    use super::{Jumbo, Mtu, ProbeCtx, Rose};

    /// The state of the machine.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MtuView {
        /// The datagram size the path carries.
        pub current: u16,
        /// The probe in flight: its size and packet number.
        pub inflight: Option<(u16, u64)>,
        /// The probe a flush took: its size and packet number.
        pub flushed: Option<(u16, u64)>,
        /// The main probe was sent since the last path event.
        pub probed: bool,
        /// The jumbo probe is done.
        pub jumbo_done: bool,
        /// A lost probe waits until this time.
        pub retry_at: u64,
        /// Discovery started.
        pub started: bool,
        /// The newest full-size packet sent.
        pub last_big: Option<u64>,
        /// The newest full-size packet acknowledged.
        pub big_acked: Option<u64>,
        /// The newest full-size packet sent before the last probe-timeout PING.
        pub ping_big: Option<u64>,
        /// The black-hole suspicion: the packet and the time it is judged.
        pub suspect: Option<(u64, u64)>,
    }

    /// One path's MTU state, driven by the calls the connection makes.
    #[derive(Debug, Clone, Copy)]
    pub struct MtuProbe(Mtu);

    impl Default for MtuProbe {
        fn default() -> Self {
            Self::new()
        }
    }

    impl MtuProbe {
        /// A path not yet probed.
        pub const fn new() -> Self {
            Self(Mtu::new())
        }

        /// Discovery starts (the handshake is done).
        pub const fn start(&mut self) {
            self.0.started = true;
        }

        /// The packet numbers of the full-size packets the connection tracks (inputs from the send and receive paths).
        pub const fn set_big(&mut self, last_big: Option<u64>, big_acked: Option<u64>, ping_big: Option<u64>) {
            self.0.last_big = last_big;
            self.0.big_acked = big_acked;
            self.0.ping_big = ping_big;
        }

        /// The next size to probe, if one is due now.
        pub fn target(&self, allowed: bool, interface_mtu: u16, v6: bool, low_latency: bool, now: u64) -> Option<u16> {
            self.0.target(
                ProbeCtx {
                    allowed,
                    interface_mtu,
                    v6,
                    low_latency,
                },
                now,
            )
        }

        /// A probe of `size` left as packet `pn`.
        pub fn probe_sent(&mut self, size: u16, pn: u64) {
            self.0.probe_sent(size, pn);
        }

        /// A probe of `size` was acknowledged or echoed; the new size if it rose.
        pub fn raise(&mut self, size: u16) -> Option<u16> {
            self.0.raise(size)
        }

        /// A probe of `size` sent as `pn` was acknowledged; `None` when it names another probe than the one in
        /// flight, otherwise what it did to the size.
        pub fn acked(&mut self, size: u16, pn: u64) -> Option<Rose> {
            self.0.acked(size, pn)
        }

        /// A probe of `size` sent as `pn` was lost; false when the loss names another probe.
        pub fn probe_lost(&mut self, size: u16, pn: u64, now: u64) -> bool {
            self.0.probe_lost(size, pn, now)
        }

        /// A flush took the probe of `size` sent as `pn`; false when it names another probe.
        pub fn flush(&mut self, size: u16, pn: u64) -> bool {
            self.0.flush(size, pn)
        }

        /// The probe a flush took, sent as `pn`, was acknowledged after all; the new size if it rose.
        pub fn flushed_acked(&mut self, pn: u64) -> Option<u16> {
            self.0.flushed_acked(pn)
        }

        /// A path event.
        pub fn event(&mut self) {
            self.0.event();
        }

        /// The probe-timeout PING was acknowledged.
        pub fn black_hole(&mut self, now: u64, rtt: u64) {
            self.0.black_hole(now, rtt);
        }

        /// Settle the suspicion; true when the path dropped to the minimum size.
        pub fn black_hole_check(&mut self, now: u64) -> bool {
            self.0.black_hole_check(now)
        }

        /// The state.
        pub fn view(&self) -> MtuView {
            let m = &self.0;
            MtuView {
                current: m.current,
                inflight: m.inflight,
                flushed: m.flushed,
                probed: m.probed,
                jumbo_done: m.jumbo == Jumbo::Done,
                retry_at: m.retry_at,
                started: m.started,
                last_big: m.last_big,
                big_acked: m.big_acked,
                ping_big: m.ping_big,
                suspect: m.suspect,
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{MIN_MTU, Mtu, PROBE_MTU, Rose};

    /// An acknowledgement that names the probe in flight but does not raise the size is taken (the probe leaves
    /// flight, nothing is refused); only an acknowledgement of any other packet is a refusal.
    #[test]
    fn an_acknowledgment_that_names_the_probe_but_raises_nothing_is_no_refusal() {
        let mut m = Mtu::new();
        m.started = true;
        m.probe_sent(PROBE_MTU, 7);
        m.current = PROBE_MTU;
        assert_eq!(
            m.acked(PROBE_MTU, 7),
            Some(Rose::Flat),
            "a matched, flat acknowledgement is a refusal"
        );
        assert_eq!(m.inflight, None, "the matched probe stayed in flight");
        m.probe_sent(PROBE_MTU, 8);
        assert_eq!(
            m.acked(PROBE_MTU, 9),
            None,
            "an acknowledgement of another packet was taken"
        );
        assert_eq!(
            m.inflight,
            Some((PROBE_MTU, 8)),
            "the refusal touched the probe in flight"
        );
    }

    /// A black-hole drop clears the mark of the probe a flush took: the path was condemned for carrying small
    /// packets only, and the stale acknowledgement of its probe is no evidence against that.
    #[test]
    fn a_black_hole_drop_clears_the_mark_of_the_probe_the_flush_took() {
        let mut m = Mtu::new();
        m.started = true;
        m.probe_sent(PROBE_MTU, 7);
        m.current = PROBE_MTU;
        assert!(m.flush(PROBE_MTU, 7));
        assert_eq!(m.flushed, Some((PROBE_MTU, 7)));
        // The signature: a probe-timeout PING was answered while the full-size packet before it was not.
        m.ping_big = Some(5);
        m.black_hole(1_000, 4_000_000);
        assert!(m.black_hole_check(5_000_000), "the path did not drop to the minimum");
        assert_eq!(m.current, MIN_MTU);
        assert_eq!(m.flushed, None, "the drop kept the stale mark");
        assert_eq!(m.flushed_acked(7), None, "the stale acknowledgement raised the path");
    }
}
