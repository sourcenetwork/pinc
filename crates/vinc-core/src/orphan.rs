//! Handshake fragments that arrive ahead of the first one.
//!
//! A first handshake message can span datagrams, and a path may deliver them out of order. The datagram that starts
//! the message creates the session; one that carries a later part of it, if it comes first, names an id no session
//! holds yet. Dropping it costs the dialer a full resend delay, so the endpoint keeps a few such datagrams for a short
//! while and gives them to the session once the first datagram has created it.
//!
//! The sender is not authenticated, so the table is small and fixed, for the whole endpoint and not per source: at
//! most [`ORPHANS`] datagrams of at most [`ORPHAN_MAX`] bytes, in the endpoint's own memory. A new datagram takes a free
//! entry, else one older than [`ORPHAN_LIFE`], else the oldest. A held datagram is given out at most once, only while
//! it is younger than [`ORPHAN_LIFE`], and only to the session that the first part of the same message (the same
//! destination id and message length) from the same address created. Holding a datagram never sends anything.
//!
//! Invariants: `held = replayed + expired + evicted + waiting` after every call; nothing is allocated.

use core::net::SocketAddr;

use vinc_security::ConnId;

/// The most datagrams held.
pub(crate) const ORPHANS: usize = 4;
/// The largest datagram held: a fragment of a first flight is cut to the datagram size of a path not probed yet.
pub(crate) const ORPHAN_MAX: usize = 1500;
/// How long a held datagram stays useful (1 s): a reordered fragment trails its neighbours by far less than that.
pub(crate) const ORPHAN_LIFE: u64 = 1_000_000_000;

/// What a held datagram names, where it came from and when.
#[derive(Debug, Clone, Copy)]
struct Held {
    at: u64,
    order: u64,
    dcid: ConnId,
    total: u64,
    local: SocketAddr,
    remote: SocketAddr,
    len: usize,
}

/// What the table did, for [`NodeStats`](crate::NodeStats).
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct OrphanCounts {
    pub(crate) held: u64,
    pub(crate) replayed: u64,
    pub(crate) expired: u64,
    pub(crate) evicted: u64,
}

/// The held datagrams.
pub(crate) struct Orphans {
    held: [Option<Held>; ORPHANS],
    data: [[u8; ORPHAN_MAX]; ORPHANS],
    order: u64,
    pub(crate) counts: OrphanCounts,
}

impl Orphans {
    pub(crate) const fn new() -> Self {
        Self {
            held: [None; ORPHANS],
            data: [[0; ORPHAN_MAX]; ORPHANS],
            order: 0,
            counts: OrphanCounts {
                held: 0,
                replayed: 0,
                expired: 0,
                evicted: 0,
            },
        }
    }

    /// Let go of every datagram older than [`ORPHAN_LIFE`] at `now`.
    pub(crate) fn expire(&mut self, now: u64) {
        for h in &mut self.held {
            if h.is_some_and(|x| now.saturating_sub(x.at) > ORPHAN_LIFE) {
                *h = None;
                self.counts.expired += 1;
            }
        }
    }

    /// Hold `buf`, a later part of a message of `total` bytes for `dcid` that arrived at `now` on `local` from
    /// `remote`. Returns false, holding nothing, for a datagram longer than [`ORPHAN_MAX`].
    pub(crate) fn hold(
        &mut self,
        now: u64,
        dcid: ConnId,
        total: u64,
        local: SocketAddr,
        remote: SocketAddr,
        buf: &[u8],
    ) -> bool {
        if buf.len() > ORPHAN_MAX {
            return false;
        }
        self.expire(now);
        let k = if let Some(k) = self.held.iter().position(Option::is_none) {
            k
        } else {
            self.counts.evicted += 1;
            self.held
                .iter()
                .enumerate()
                .min_by_key(|(_, h)| h.map_or(0, |x| x.order))
                .map_or(0, |(k, _)| k)
        };
        let dst = self.data.get_mut(k).and_then(|d| d.get_mut(..buf.len()));
        let (Some(slot), Some(dst)) = (self.held.get_mut(k), dst) else {
            return false;
        };
        dst.copy_from_slice(buf);
        *slot = Some(Held {
            at: now,
            order: self.order,
            dcid,
            total,
            local,
            remote,
            len: buf.len(),
        });
        self.order += 1;
        self.counts.held += 1;
        true
    }

    /// Give out the oldest fresh datagram that came from `remote` with a part of the message of `total` bytes for
    /// `dcid`: its bytes are copied into `out`; returns the local address it arrived on and its length.
    pub(crate) fn take(
        &mut self,
        now: u64,
        dcid: &ConnId,
        total: u64,
        remote: &SocketAddr,
        out: &mut [u8; ORPHAN_MAX],
    ) -> Option<(SocketAddr, usize)> {
        self.expire(now);
        let (k, _) = self
            .held
            .iter()
            .enumerate()
            .filter_map(|(k, h)| {
                h.filter(|x| x.dcid == *dcid && x.total == total && x.remote == *remote)
                    .map(|x| (k, x.order))
            })
            .min_by_key(|(_, order)| *order)?;
        let h = self.held.get_mut(k)?.take()?;
        let src = self.data.get(k)?.get(..h.len)?;
        out.get_mut(..h.len)?.copy_from_slice(src);
        self.counts.replayed += 1;
        Some((h.local, h.len))
    }

    /// How many datagrams are held now.
    pub(crate) fn waiting(&self) -> usize {
        self.held.iter().flatten().count()
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "test assertions")]
mod tests {
    use super::*;

    fn addr(i: u8) -> SocketAddr {
        SocketAddr::from(([10, 0, 0, i], 9))
    }

    fn cid(i: u8) -> ConnId {
        ConnId::new(&[i; 4]).unwrap()
    }

    fn balanced(o: &Orphans) -> bool {
        let c = o.counts;
        c.held == c.replayed + c.expired + c.evicted + o.waiting() as u64
    }

    #[test]
    fn a_flood_keeps_the_newest_four_and_counts_the_rest() {
        let mut o = Orphans::new();
        for i in 0..100u8 {
            assert!(o.hold(u64::from(i), cid(i), 2000, addr(1), addr(i), &[i; 1200]));
            assert!(o.waiting() <= ORPHANS && balanced(&o));
        }
        assert_eq!((o.counts.held, o.counts.evicted, o.waiting()), (100, 96, 4));
        let mut out = [0u8; ORPHAN_MAX];
        for i in 0..96u8 {
            assert!(
                o.take(100, &cid(i), 2000, &addr(i), &mut out).is_none(),
                "an evicted datagram came back"
            );
        }
        for i in 96..100u8 {
            assert_eq!(o.take(100, &cid(i), 2000, &addr(i), &mut out), Some((addr(1), 1200)));
            assert!(out[..1200].iter().all(|b| *b == i));
        }
        assert!(balanced(&o) && o.waiting() == 0);
    }

    #[test]
    fn a_free_entry_is_taken_before_any_is_evicted() {
        let mut o = Orphans::new();
        for i in 0..4u8 {
            assert!(o.hold(0, cid(i), 2000, addr(1), addr(i), &[i]));
        }
        let mut out = [0u8; ORPHAN_MAX];
        assert!(o.take(0, &cid(2), 2000, &addr(2), &mut out).is_some());
        assert!(o.hold(0, cid(9), 2000, addr(1), addr(9), &[9]));
        assert_eq!(o.counts.evicted, 0);
        for i in [0u8, 1, 3, 9] {
            assert!(o.take(0, &cid(i), 2000, &addr(i), &mut out).is_some());
        }
    }

    #[test]
    fn only_the_same_message_from_the_same_address_is_given_out() {
        let mut o = Orphans::new();
        assert!(o.hold(0, cid(1), 2000, addr(1), addr(5), &[1, 2, 3]));
        let mut out = [0u8; ORPHAN_MAX];
        assert!(o.take(0, &cid(2), 2000, &addr(5), &mut out).is_none(), "another id");
        assert!(
            o.take(0, &cid(1), 1999, &addr(5), &mut out).is_none(),
            "another message length"
        );
        assert!(
            o.take(0, &cid(1), 2000, &addr(6), &mut out).is_none(),
            "another address"
        );
        assert_eq!(o.take(0, &cid(1), 2000, &addr(5), &mut out), Some((addr(1), 3)));
        assert_eq!(out[..3], [1, 2, 3]);
        assert!(
            o.take(0, &cid(1), 2000, &addr(5), &mut out).is_none(),
            "given out twice"
        );
        assert!(balanced(&o));
    }

    #[test]
    fn several_parts_come_out_oldest_first() {
        let mut o = Orphans::new();
        for (t, b) in [(0, 1u8), (1, 2), (2, 3)] {
            assert!(o.hold(t, cid(1), 4000, addr(1), addr(5), &[b]));
        }
        let mut out = [0u8; ORPHAN_MAX];
        for want in 1..=3u8 {
            assert!(o.take(3, &cid(1), 4000, &addr(5), &mut out).is_some());
            assert_eq!(out[0], want);
        }
    }

    #[test]
    fn a_datagram_expires_after_a_second_and_is_never_given_out() {
        let mut o = Orphans::new();
        assert!(o.hold(0, cid(1), 2000, addr(1), addr(5), &[1]));
        let mut out = [0u8; ORPHAN_MAX];
        assert!(
            o.take(ORPHAN_LIFE, &cid(1), 2000, &addr(5), &mut out).is_some(),
            "still fresh at the bound"
        );
        assert!(o.hold(0, cid(1), 2000, addr(1), addr(5), &[1]));
        assert!(o.take(ORPHAN_LIFE + 1, &cid(1), 2000, &addr(5), &mut out).is_none());
        assert_eq!((o.counts.expired, o.waiting()), (1, 0));
        assert!(balanced(&o));
        // An expired entry is reused before any live one is evicted.
        for i in 2..6u8 {
            assert!(o.hold(10, cid(i), 2000, addr(1), addr(5), &[i]));
        }
        assert!(o.hold(2 * ORPHAN_LIFE, cid(9), 2000, addr(1), addr(5), &[9]));
        assert_eq!((o.counts.expired, o.counts.evicted, o.waiting()), (5, 0, 1));
        assert!(balanced(&o));
    }

    #[test]
    fn a_datagram_longer_than_the_bound_is_not_held() {
        let mut o = Orphans::new();
        assert!(!o.hold(0, cid(1), 4000, addr(1), addr(5), &[0; ORPHAN_MAX + 1]));
        assert!(o.hold(0, cid(1), 4000, addr(1), addr(5), &[0; ORPHAN_MAX]));
        assert_eq!((o.counts.held, o.waiting()), (1, 1));
    }
}
