//! Node round trips: what the endpoint remembers about how long a round trip takes, and what it hands to every
//! connection.
//!
//! The node keeps three numbers and a floor. `krtt` is the handshake round trip of each peer (at most
//! [`PEER_RTTS`] peers, none replaced once the table is full). `lrtt` is the node average of handshake round trips, an
//! exponentially weighted mean with weight 7/8 on the old value. `tgr` is the node peak: after every sample it becomes
//! `max(sample, tgr - tgr / 32)`. The handshake floor `hs_floor` rises after a dial times out, `min(8 s, max(500 ms, 2 x
//! floor))`, and falls to zero only when a handshake answered at its first flight gives a sample: a new round trip peak
//! of a session does not reset it. A node, or a session, is thin when the largest of these numbers is at least 250 ms;
//! a session with no sample at all counts as thin.
//!
//! The first resend of a dial waits `max(500 ms, 2 x r, hs_floor)`, `r` being the peer's `krtt` else `lrtt`; a ticket
//! resume to a hub the node has just restarted towards waits `max(300 ms, 1.5 x krtt + 20 ms)` instead.
//!
//! Invariants: every update is a pure function of the previous values and the sample; nothing here reads a clock.

use pinc_crypto::NodeId;

use crate::table::Table;

/// The most peers whose handshake round trip is remembered.
pub const PEER_RTTS: usize = 256;
/// The round trip from which a node or a session is thin (250 ms).
pub const SLOW_RTT: u64 = 250_000_000;
/// The shortest first resend of a dial (500 ms).
pub const FIRST_RESEND: u64 = 500_000_000;
/// The highest the handshake floor rises (8 s).
pub const FLOOR_MAX: u64 = 8_000_000_000;
/// The shortest first resend of a ticket resume towards a restarted hub (300 ms).
pub const HUB_RESEND: u64 = 300_000_000;

/// The round trips of a node.
#[derive(Debug)]
pub struct NodeRtt {
    krtt: Table<NodeId, u64, PEER_RTTS>,
    lrtt: u64,
    tgr: u64,
    hs_floor: u64,
}

impl NodeRtt {
    crate::store::store_fn! {
    /// No round trip known yet; the table hash is keyed by `seed`.
    pub fn new(seed: u64) -> Self {
        Self {
            krtt: Table::new(seed),
            lrtt: 0,
            tgr: 0,
            hs_floor: 0,
        }
    }
    }

    /// A handshake to `peer` took `rtt` nanoseconds without a resend (0 means no sample). Zero is ignored;
    /// otherwise the peer's entry is stored (a new peer only while there is room), the floor drops to zero and the
    /// node average moves.
    pub fn note_handshake(&mut self, peer: NodeId, rtt: u64) {
        if rtt == 0 {
            return;
        }
        self.krtt.insert_room(peer, rtt);
        self.hs_floor = 0;
        self.lrtt = if self.lrtt == 0 {
            rtt
        } else {
            (self.lrtt.saturating_mul(7).saturating_add(rtt)) / 8
        };
    }

    /// Remember `rtt` for `peer` from persisted state, without touching the node average. A new peer is refused when
    /// the table is full. Returns whether it was stored.
    pub fn restore_peer(&mut self, peer: NodeId, rtt: u64) -> bool {
        self.krtt.insert_room(peer, rtt)
    }

    /// A connection took a round trip sample whose peak, after its own decay, is `peak`: the node peak follows.
    pub fn note_peak(&mut self, peak: u64) {
        self.tgr = peak.max(self.tgr - (self.tgr >> 5));
    }

    /// A dial timed out: the floor rises.
    pub fn note_timeout(&mut self) {
        self.hs_floor = FLOOR_MAX.min(FIRST_RESEND.max(self.hs_floor.saturating_mul(2)));
    }

    /// The remembered handshake round trip of `peer`.
    pub fn krtt(&self, peer: &NodeId) -> Option<u64> {
        self.krtt.get(peer).copied()
    }

    /// The node average handshake round trip (0 before the first).
    pub const fn lrtt(&self) -> u64 {
        self.lrtt
    }

    /// The node peak round trip (0 before the first).
    pub const fn tgr(&self) -> u64 {
        self.tgr
    }

    /// The handshake floor.
    pub const fn hs_floor(&self) -> u64 {
        self.hs_floor
    }

    /// The first resend delay of a dial to `peer`: `max(500 ms, 2 x r, hs_floor)`.
    pub fn first_resend(&self, peer: &NodeId) -> u64 {
        let r = self.krtt(peer).filter(|r| *r > 0).unwrap_or(self.lrtt);
        FIRST_RESEND.max(r.saturating_mul(2)).max(self.hs_floor)
    }

    /// The remembered round trip to give a connection so its own formula `max(500 ms, 2 x r)` yields
    /// [`first_resend`](Self::first_resend): the peer's round trip, else the node average, raised to half the floor. `None`
    /// when there is nothing to remember.
    pub fn remembered_for(&self, peer: &NodeId) -> Option<u64> {
        let r = self
            .krtt(peer)
            .filter(|r| *r > 0)
            .unwrap_or(self.lrtt)
            .max(self.hs_floor.div_ceil(2));
        (r > 0).then_some(r)
    }

    /// The first resend of a ticket resume to a hub after a late start: `max(300 ms, 3 * r0 / 2 + 20 ms)` with `r0`
    /// the peer's `krtt`, the product taken first; `None` without one.
    pub fn hub_resend(&self, peer: &NodeId) -> Option<u64> {
        let r0 = self.krtt(peer).filter(|r| *r > 0)?;
        // `r0 + r0 / 2` is `3 * r0 / 2` rounded down, without a product that could overflow.
        Some(HUB_RESEND.max(r0.saturating_add(r0 / 2).saturating_add(20_000_000)))
    }

    /// Whether the node is on a constrained link: the largest of `tgr` and `lrtt` is at least 250 ms.
    pub fn thin_node(&self) -> bool {
        self.tgr.max(self.lrtt) >= SLOW_RTT
    }

    /// Whether a session is thin: it has no sample, or the largest of the node peak, the node average, its smallest
    /// round trip and half its smoothed round trip is at least 250 ms.
    pub fn thin(&self, srtt: u64, min_rtt: u64) -> bool {
        srtt == 0 || self.tgr.max(self.lrtt).max(min_rtt).max(srtt >> 1) >= SLOW_RTT
    }

    /// The peers with a remembered round trip, oldest first.
    pub fn peers(&self) -> impl Iterator<Item = (&NodeId, &u64)> {
        self.krtt.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use pinc_crypto::IdentityAlg;

    fn n(b: u8) -> NodeId {
        NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [b; 32],
        }
    }

    #[test]
    fn the_average_weighs_seven_eighths_and_the_peak_decays() {
        let mut r = NodeRtt::new(1);
        r.note_handshake(n(1), 80_000_000);
        assert_eq!(r.lrtt(), 80_000_000);
        r.note_handshake(n(2), 160_000_000);
        assert_eq!(r.lrtt(), (7 * 80_000_000 + 160_000_000) / 8);
        r.note_peak(320_000_000);
        assert_eq!(r.tgr(), 320_000_000);
        r.note_peak(10);
        assert_eq!(r.tgr(), 320_000_000 - (320_000_000 >> 5));
    }

    #[test]
    fn the_floor_doubles_to_eight_seconds_and_only_a_handshake_sample_resets_it() {
        let mut r = NodeRtt::new(1);
        let seen: std::vec::Vec<u64> = (0..6)
            .map(|_| {
                r.note_timeout();
                r.hs_floor()
            })
            .collect();
        assert_eq!(
            seen,
            [
                500_000_000,
                1_000_000_000,
                2_000_000_000,
                4_000_000_000,
                8_000_000_000,
                8_000_000_000
            ]
        );
        assert_eq!(r.first_resend(&n(1)), 8_000_000_000);
        assert_eq!(r.remembered_for(&n(1)), Some(4_000_000_000));
        // A new round trip peak is not a handshake sample: the floor stays.
        r.note_peak(300_000_000);
        assert_eq!(r.hs_floor(), 8_000_000_000);
        r.note_handshake(n(1), 10_000_000);
        assert_eq!(r.hs_floor(), 0);
        assert_eq!(r.first_resend(&n(1)), FIRST_RESEND);
    }

    #[test]
    fn first_resend_uses_the_peer_then_the_node() {
        let mut r = NodeRtt::new(1);
        r.note_handshake(n(1), 600_000_000);
        assert_eq!(r.first_resend(&n(1)), 1_200_000_000);
        assert_eq!(r.first_resend(&n(2)), 1_200_000_000);
        r.note_handshake(n(2), 10_000_000);
        assert_eq!(r.first_resend(&n(2)), FIRST_RESEND);
        assert_eq!(r.hub_resend(&n(2)), Some(HUB_RESEND));
        assert_eq!(r.hub_resend(&n(1)), Some(920_000_000));
        assert_eq!(r.hub_resend(&n(9)), None);
    }

    #[test]
    fn the_hub_resend_of_an_odd_round_trip_multiplies_before_it_halves() {
        let mut r = NodeRtt::new(1);
        r.note_handshake(n(1), 600_000_001);
        // 3 * 600_000_001 / 2 = 900_000_001, one more than three halves of 600_000_000.
        assert_eq!(r.hub_resend(&n(1)), Some(920_000_001));
        // Three halves of a round trip near the top of the clock: exact while it fits, the ceiling beyond.
        r.note_handshake(n(2), 12_000_000_000_000_000_001);
        assert_eq!(r.hub_resend(&n(2)), Some(18_000_000_000_020_000_001));
        r.note_handshake(n(3), u64::MAX);
        assert_eq!(r.hub_resend(&n(3)), Some(u64::MAX));
    }

    #[test]
    fn thin_classification() {
        let mut r = NodeRtt::new(1);
        assert!(r.thin(0, 0));
        assert!(!r.thin(40_000_000, 30_000_000));
        assert!(r.thin(500_000_000, 0));
        assert!(!r.thin_node());
        r.note_peak(250_000_000);
        assert!(r.thin_node());
        assert!(r.thin(10_000_000, 0));
    }

    #[test]
    fn a_full_table_keeps_its_peers() {
        let mut r = NodeRtt::new(1);
        for i in 0..=PEER_RTTS as u32 {
            let mut id = [0u8; 32];
            id[..4].copy_from_slice(&i.to_be_bytes());
            r.note_handshake(
                NodeId {
                    alg: IdentityAlg::Ed25519,
                    bytes: id,
                },
                1_000_000,
            );
        }
        assert_eq!(r.peers().count(), PEER_RTTS);
        let mut last = [0u8; 32];
        last[..4].copy_from_slice(&(PEER_RTTS as u32).to_be_bytes());
        assert_eq!(
            r.krtt(&NodeId {
                alg: IdentityAlg::Ed25519,
                bytes: last
            }),
            None
        );
    }
}
