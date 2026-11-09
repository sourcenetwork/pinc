//! Path datagram size: one probe of 1452 bytes after the handshake, and on a path under 2 ms one probe at the
//! interface size up to 8952 when that is above 2904, each a PING plus PADDING packet of exactly the probed size.
//!
//! Only direct (UDP) paths are probed, never on a thin node, and not for 10 s after a wake or a link return. A path
//! is probed once: a lost probe is not retried, it waits for the next path event (a re-join that worked, a link
//! return, a new address, a re-validation) or for 10 minutes. When a probe-timeout PING is acknowledged while a
//! full-size packet sent before it still is not one round trip later, the path drops to 1200, because the signature
//! is a path that carries small packets only.
//!
//! Invariants: at most one probe is in flight per path; a lost probe is not a congestion signal (recovery is told the
//! packet is a probe); the datagram size only rises to a size the peer confirmed (an acknowledgement or an echo) and
//! falls back to 1200 on the black-hole signature.

use vinc_crypto::Provider;

use super::Connection;
use super::config::{JUMBO_FLOOR, JUMBO_MTU, JUMBO_RTT, MIN_MTU, PROBE_MTU};
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

conn_impl! {
    /// The next size to probe on path `i`, if one is due now.
    pub(super) fn mtu_target(&self, i: usize, now: u64) -> Option<u16> {
        let p = self.paths.get(i)?;
        if !self.cfg.probe_mtu
            || self.cfg.thin
            || p.info.kind != PathKind::Direct
            || !p.mtu.started
            || p.mtu.inflight.is_some()
            || p.mtu.retry_at > now
            || now < self.life.qr_until
        {
            return None;
        }
        if !p.mtu.probed {
            return (p.info.interface_mtu >= PROBE_MTU && p.mtu.current < PROBE_MTU).then_some(PROBE_MTU);
        }
        let low_latency = self.rec.rtt().min_rtt().is_some_and(|r| r < JUMBO_RTT);
        let jumbo = p.info.interface_mtu.min(JUMBO_MTU);
        (p.mtu.jumbo == Jumbo::Untried && p.mtu.current == PROBE_MTU && low_latency && jumbo > JUMBO_FLOOR)
            .then_some(jumbo)
    }

    /// Note that a probe of `size` left on path `i`.
    pub(super) fn mtu_probe_sent(&mut self, i: usize, size: u16) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.mtu.inflight = Some(size);
        if size == PROBE_MTU && !p.mtu.probed {
            p.mtu.probed = true;
        } else {
            p.mtu.jumbo = Jumbo::Done;
        }
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
        if p.mtu.inflight == Some(size) {
            p.mtu.inflight = None;
        }
        if size > p.mtu.current {
            p.mtu.current = size;
            if active {
                self.rec.set_max_datagram_size(u64::from(size));
            }
        }
    }

    /// A probe of `size` was lost: it waits for the next path event or [`REPROBE_AFTER`].
    pub(super) fn mtu_probe_lost(&mut self, i: usize, size: u16, now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.mtu.inflight == Some(size) {
            p.mtu.inflight = None;
        }
        p.mtu.retry_at = now.saturating_add(REPROBE_AFTER);
        if size > PROBE_MTU {
            p.mtu.jumbo = Jumbo::Done;
        }
    }

    /// A path event happened on path `i`: probe it again.
    pub(super) fn mtu_event(&mut self, i: usize) {
        let Some(p) = self.paths.get_mut(i) else { return };
        p.mtu.probed = false;
        p.mtu.jumbo = Jumbo::Untried;
        p.mtu.retry_at = 0;
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
        let Some(big) = p.mtu.ping_big else { return };
        if p.mtu.current <= MIN_MTU || p.mtu.big_acked.is_some_and(|a| a >= big) {
            return;
        }
        p.mtu.suspect = Some((big, now.saturating_add(rtt)));
    }

    /// Settle a black-hole suspicion once its round trip has passed: if no full-size packet at or after the suspect one
    /// was acknowledged, the path carries small packets only. Drop the active path to the minimum size.
    pub(super) fn mtu_black_hole_check(&mut self, now: u64) {
        let Some(p) = self.paths.active_mut() else { return };
        let Some((big, at)) = p.mtu.suspect else { return };
        if p.mtu.big_acked.is_some_and(|a| a >= big) || p.mtu.current <= MIN_MTU {
            p.mtu.suspect = None;
            return;
        }
        if now < at {
            return;
        }
        p.mtu.suspect = None;
        p.mtu.current = MIN_MTU;
        p.mtu.inflight = None;
        p.mtu.last_big = None;
        p.mtu.ping_big = None;
        p.mtu.retry_at = now.saturating_add(REPROBE_AFTER);
        p.mtu.probed = true;
        p.mtu.jumbo = Jumbo::Done;
        self.rec.set_max_datagram_size(u64::from(MIN_MTU));
        self.shed_extensions();
    }

    /// Start discovery on every path once the handshake is done.
    pub(super) fn mtu_start(&mut self) {
        for p in self.paths.slots.iter_mut().flatten() {
            p.mtu.started = true;
        }
    }
}
