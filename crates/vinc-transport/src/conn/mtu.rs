//! Path MTU discovery (DPLPMTUD): probe 1452 after the handshake, and on a path under 2 ms also the interface size
//! up to 8952, with a PING plus PADDING packet of exactly the probed size.
//!
//! Invariants: at most one probe is in flight per path; a lost probe is not a congestion signal (recovery is told the
//! packet is a probe) and after 3 losses of one size that size is never probed again on the path; the datagram size
//! only rises to a size the peer confirmed (an acknowledgement or an echo) and falls back to 1200 after 3 probe
//! timeouts in a row on full-size packets.

use vinc_crypto::Provider;

use super::Connection;
use super::config::{JUMBO_MTU, JUMBO_RTT, MIN_MTU, PROBE_MTU};
use crate::recovery::MS;
use crate::stream::StreamSource;

/// Probe losses of one size before it is given up on.
const PROBE_TRIES: u8 = 3;
/// The wait before probing again after a loss.
const PROBE_RETRY: u64 = 200 * MS;
/// Probe timeouts in a row on full-size packets that mean a black hole.
const BLACK_HOLE_PTOS: u32 = 3;

conn_impl! {
    /// The next size to probe on path `i`, if any.
    pub(super) fn mtu_target(&self, i: usize) -> Option<u16> {
        let p = self.paths.get(i)?;
        if !self.cfg.probe_mtu || !p.mtu.started || p.mtu.inflight.is_some() {
            return None;
        }
        let low_latency = p.min_rtt.or(p.rtt).is_some_and(|r| r < JUMBO_RTT);
        let jumbo = p.info.interface_mtu.min(JUMBO_MTU);
        [PROBE_MTU, jumbo]
            .into_iter()
            .filter(|s| *s == PROBE_MTU || low_latency)
            .find(|s| *s > p.mtu.current && *s < p.mtu.ceiling && *s <= p.info.interface_mtu)
    }

    /// A probe of `size` was acknowledged or echoed: the path carries it.
    pub(super) fn mtu_raise(&mut self, i: usize, size: u16) {
        let active = i == self.paths.active;
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.mtu.inflight == Some(size) {
            p.mtu.inflight = None;
        }
        p.mtu.failures = 0;
        if size > p.mtu.current && size < p.mtu.ceiling {
            p.mtu.current = size;
            if active {
                self.rec.set_max_datagram_size(u64::from(size));
            }
        }
    }

    /// A probe of `size` was lost.
    pub(super) fn mtu_probe_lost(&mut self, i: usize, size: u16, now: u64) {
        let Some(p) = self.paths.get_mut(i) else { return };
        if p.mtu.inflight == Some(size) {
            p.mtu.inflight = None;
        }
        p.mtu.failures += 1;
        p.mtu.next_at = now.saturating_add(PROBE_RETRY);
        if p.mtu.failures >= PROBE_TRIES {
            p.mtu.ceiling = p.mtu.ceiling.min(size);
            p.mtu.failures = 0;
        }
    }

    /// After a probe timeout: if full-size packets keep timing out, fall back to the minimum size.
    pub(super) fn mtu_black_hole_check(&mut self) {
        if self.rec.pto_count() < BLACK_HOLE_PTOS {
            return;
        }
        let Some(p) = self.paths.active_mut() else { return };
        if p.mtu.current > MIN_MTU && p.mtu.last_size > MIN_MTU {
            p.mtu.ceiling = p.mtu.current;
            p.mtu.current = MIN_MTU;
            p.mtu.inflight = None;
            self.rec.set_max_datagram_size(u64::from(MIN_MTU));
        }
    }

    /// Start discovery on every path once the handshake is done.
    pub(super) fn mtu_start(&mut self) {
        for p in self.paths.slots.iter_mut().flatten() {
            p.mtu.started = true;
        }
    }
}
