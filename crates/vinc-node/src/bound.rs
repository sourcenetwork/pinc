//! How long a path may stay silent before the transport gives it up.
//!
//! The transport declares a path dead after ten probe timeouts and a silence of at least eight smoothed round trips
//! (twenty seconds on a slow or thin path). A hub heard again after longer than that means the partition healed and
//! the session's own state was reset. The bound here sums the same ten timeouts from the smoothed round trip with
//! the transport's own caps, so it follows the path instead of a fixed minute.
//!
//! Invariants: the bound grows with the smoothed round trip, never drops below the transport's silence rule, and an
//! unsampled path is treated as the transport's seeded round trip.

use crate::config::Nanos;

const MS: Nanos = 1_000_000;
const S: Nanos = 1_000_000_000;
/// The round trip the transport assumes before a sample.
const SEED_RTT: Nanos = 333 * MS;
/// Probe timeouts before the transport gives a path up.
const GIVE_UP_PTOS: u32 = 10;
/// The transport's silence rule on a slow or thin path.
const SLOW_SILENCE: Nanos = 20 * S;
/// The transport's silence rule in round trips.
const SILENCE_RTTS: Nanos = 8;
/// The ordinary cap of one probe timeout.
const PTO_CAP: Nanos = 2 * S;
/// The doubling stops after this many timeouts.
const PTO_MAX_SHIFT: u32 = 6;
/// A smoothed round trip of this much or more raises the cap of a timeout.
const SLOW_SRTT: Nanos = S;
/// The receiver's delay allowed for in a timeout.
const MAX_ACK_DELAY: Nanos = 25 * MS;

// vertexia: the transport owns these caps and does not export the bound; one shared function in the transport
// replaces this copy when it does. The round trip variation is taken as half the smoothed round trip, as the
// transport seeds it.
/// The silence after which the transport gives up a path whose smoothed round trip is `srtt` (0 if unsampled).
pub fn give_up(srtt: Nanos, thin: bool) -> Nanos {
    let srtt = if srtt == 0 { SEED_RTT } else { srtt };
    let base = srtt
        .saturating_add((srtt / 2).saturating_mul(4).max(MS))
        .saturating_add(MAX_ACK_DELAY);
    let wide = PTO_CAP.max(srtt.saturating_mul(2));
    let slow = srtt >= SLOW_SRTT;
    let cap = if slow { wide } else { PTO_CAP };
    let mut sum: Nanos = 0;
    for k in 0..GIVE_UP_PTOS {
        let shifted = base
            .saturating_mul(1u64 << k.min(PTO_MAX_SHIFT))
            .min(wide.saturating_mul(4));
        sum = sum.saturating_add(shifted.min(cap));
    }
    let need = if slow || thin { SLOW_SILENCE } else { 0 }.max(srtt.saturating_mul(SILENCE_RTTS));
    sum.max(need)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grows_with_the_round_trip() {
        let mut last = 0;
        for srtt in [0, 10 * MS, 50 * MS, 200 * MS, S, 3 * S] {
            let b = give_up(srtt, false);
            assert!(b >= last, "{srtt}: {b} < {last}");
            last = b;
        }
    }

    #[test]
    fn a_fast_path_gives_up_well_before_a_minute() {
        let b = give_up(50 * MS, false);
        assert!(b > 5 * S && b < 30 * S, "{b}");
    }

    #[test]
    fn never_below_the_silence_rule() {
        assert!(give_up(2 * S, false) >= 16 * S);
        assert!(give_up(10 * MS, true) >= 20 * S);
        assert_eq!(give_up(0, false), give_up(SEED_RTT, false));
    }
}
