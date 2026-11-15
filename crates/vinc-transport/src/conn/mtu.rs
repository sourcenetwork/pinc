//! Path datagram size: one probe of 1452 bytes after the handshake, and on a path under 2 ms one probe at the
//! interface size up to 8952 when that is above 2904, each a PING plus PADDING packet of exactly the probed size.
//!
//! Only direct (UDP) paths are probed, never on a thin node, and not for 10 s after a wake or a link return. A path
//! is probed once: a lost probe is not retried, it waits for the next path event (a re-join that worked, a link
//! return, a new address, a re-validation) or for 10 minutes. A path is not probed while the oldest packet in flight
//! left on another path: that recovery is timed first, and the probe's lone acknowledgement, held for the ack delay,
//! would stretch its round trip; the probe goes once those packets are acknowledged or declared lost. When a
//! probe-timeout PING is acknowledged while a full-size packet sent before it still is not one round trip later, the
//! path drops to 1200, because the signature is a path that carries small packets only.
//!
//! Invariants: at most one probe is in flight per path; a lost probe is not a congestion signal (recovery is told the
//! packet is a probe); the datagram size only rises to a size the peer confirmed (an acknowledgement or an echo) and
//! falls back to 1200 on the black-hole signature.

use vinc_crypto::Provider;

use super::Connection;
use super::config::{JUMBO_FLOOR, JUMBO_MTU, JUMBO_RTT, MIN_MTU, PROBE_MTU};
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

/// What the probe decision needs to know about the path and the connection.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ProbeCtx {
    /// The configuration allows probing, the node is not thin, the path is direct, and the quiet period is over.
    pub(crate) allowed: bool,
    /// The interface datagram size of the path.
    pub(crate) interface_mtu: u16,
    /// The path's minimum round trip is under [`JUMBO_RTT`].
    pub(crate) low_latency: bool,
}

impl Mtu {
    /// A path not yet probed: the minimum size, nothing in flight.
    pub(crate) const fn new() -> Self {
        Self {
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
        }
    }

    /// The next size to probe, if one is due now.
    pub(crate) fn target(&self, ctx: ProbeCtx, now: u64) -> Option<u16> {
        if !ctx.allowed || !self.started || self.inflight.is_some() || self.retry_at > now {
            return None;
        }
        if !self.probed {
            return (ctx.interface_mtu >= PROBE_MTU && self.current < PROBE_MTU).then_some(PROBE_MTU);
        }
        let jumbo = ctx.interface_mtu.min(JUMBO_MTU);
        (self.jumbo == Jumbo::Untried && self.current == PROBE_MTU && ctx.low_latency && jumbo > JUMBO_FLOOR)
            .then_some(jumbo)
    }

    /// A probe of `size` left.
    pub(crate) fn probe_sent(&mut self, size: u16) {
        self.inflight = Some(size);
        if size == PROBE_MTU && !self.probed {
            self.probed = true;
        } else {
            self.jumbo = Jumbo::Done;
        }
    }

    /// A probe of `size` was acknowledged or echoed; the new datagram size if it rose.
    pub(crate) fn raise(&mut self, size: u16) -> Option<u16> {
        if self.inflight == Some(size) {
            self.inflight = None;
        }
        (size > self.current).then(|| {
            self.current = size;
            size
        })
    }

    /// A probe of `size` was lost: it waits for the next path event or [`REPROBE_AFTER`].
    pub(crate) fn probe_lost(&mut self, size: u16, now: u64) {
        if self.inflight == Some(size) {
            self.inflight = None;
        }
        self.retry_at = now.saturating_add(REPROBE_AFTER);
        if size > PROBE_MTU {
            self.jumbo = Jumbo::Done;
        }
    }

    /// A path event happened: probe again.
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
            low_latency: self.rec.rtt().min_rtt().is_some_and(|r| r < JUMBO_RTT),
        };
        p.mtu.target(ctx, now)
    }

    /// Note that a probe of `size` left on path `i`.
    pub(super) fn mtu_probe_sent(&mut self, i: usize, size: u16) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.mtu.probe_sent(size);
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

    /// A probe of `size` was lost: it waits for the next path event or [`REPROBE_AFTER`].
    pub(super) fn mtu_probe_lost(&mut self, i: usize, size: u16, now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.mtu.probe_lost(size, now);
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
    use super::{Jumbo, Mtu, ProbeCtx};

    /// The state of the machine.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MtuView {
        /// The datagram size the path carries.
        pub current: u16,
        /// The probe in flight.
        pub inflight: Option<u16>,
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
        pub fn target(&self, allowed: bool, interface_mtu: u16, low_latency: bool, now: u64) -> Option<u16> {
            self.0.target(
                ProbeCtx {
                    allowed,
                    interface_mtu,
                    low_latency,
                },
                now,
            )
        }

        /// A probe of `size` left.
        pub fn probe_sent(&mut self, size: u16) {
            self.0.probe_sent(size);
        }

        /// A probe of `size` was acknowledged or echoed; the new size if it rose.
        pub fn raise(&mut self, size: u16) -> Option<u16> {
            self.0.raise(size)
        }

        /// A probe of `size` was lost.
        pub fn probe_lost(&mut self, size: u16, now: u64) {
            self.0.probe_lost(size, now);
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
