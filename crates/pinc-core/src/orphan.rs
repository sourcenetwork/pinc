//! Handshake fragments that arrive ahead of the first one, and first-message starts that no session took.
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
//! A start (the part at offset 0 of a first message) that every session holding its id already had as a repeat of its
//! own first message is held too, flagged: it is never replayed, and a later part that no session agrees with makes a
//! session of its own from it ([`Orphans::start_of`]), so a forged first message that took the id first cannot keep
//! the genuine one out. A part a new session refuses stays held (`next` and `done`).
//!
//! Invariants: `held = replayed + expired + evicted + waiting` after every call; nothing is allocated.

use core::net::SocketAddr;

use pinc_security::ConnId;

use crate::rx::fragment;

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
    /// The datagram starts the message (offset 0) instead of continuing it.
    start: bool,
}

/// Whether the fragments in the datagrams `a` and `b` of one message carry the same bytes at every offset both cover.
fn agree(a: &[u8], b: &[u8]) -> bool {
    fn at(d: &[u8], o: u64, lo: u64, hi: u64) -> Option<&[u8]> {
        let (from, to) = (usize::try_from(lo - o).ok()?, usize::try_from(hi - o).ok()?);
        d.get(from..to)
    }
    let (Some((_, total, ao, ad)), Some((_, _, bo, bd))) = (fragment(a), fragment(b)) else {
        return false;
    };
    let end = |o: u64, d: &[u8]| o.saturating_add(d.len() as u64);
    let (lo, hi) = (ao.max(bo), end(ao, ad).min(end(bo, bd)).min(total));
    if lo >= hi {
        return true;
    }
    at(ad, ao, lo, hi).is_some_and(|x| Some(x) == at(bd, bo, lo, hi))
}

/// What the table did, for [`NodeStats`](crate::NodeStats).
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct OrphanCounts {
    pub(crate) held: u64,
    pub(crate) replayed: u64,
    pub(crate) expired: u64,
    pub(crate) evicted: u64,
    /// Starts held (counted in `held` too).
    pub(crate) starts_held: u64,
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
                starts_held: 0,
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
        self.put(now, dcid, total, local, remote, buf, false)
    }

    /// Hold `buf`, the start of a message of `total` bytes for `dcid`, unless the same bytes from `remote` are held
    /// already (a repeat of a start adds nothing).
    pub(crate) fn hold_start(
        &mut self,
        now: u64,
        dcid: ConnId,
        total: u64,
        local: SocketAddr,
        remote: SocketAddr,
        buf: &[u8],
    ) -> bool {
        if self.held.iter().enumerate().any(|(k, h)| {
            h.is_some_and(|x| {
                x.start
                    && x.dcid == dcid
                    && x.total == total
                    && x.remote == remote
                    && x.len == buf.len()
                    && now.saturating_sub(x.at) <= ORPHAN_LIFE
                    && self.data.get(k).and_then(|d| d.get(..x.len)) == Some(buf)
            })
        }) {
            return true;
        }
        let ok = self.put(now, dcid, total, local, remote, buf, true);
        self.counts.starts_held += u64::from(ok);
        ok
    }

    #[allow(clippy::too_many_arguments, reason = "the fields of one entry")]
    fn put(
        &mut self,
        now: u64,
        dcid: ConnId,
        total: u64,
        local: SocketAddr,
        remote: SocketAddr,
        buf: &[u8],
        start: bool,
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
            start,
        });
        self.order += 1;
        self.counts.held += 1;
        true
    }

    /// Copy the oldest fresh part (not a start) from `remote` of the message of `total` bytes for `dcid` whose order
    /// is at least `min_order` into `out`, and leave it held: returns its order, the local address it arrived on and
    /// its length. [`Self::done`] lets it go once a session took it.
    pub(crate) fn next(
        &mut self,
        now: u64,
        dcid: &ConnId,
        total: u64,
        remote: &SocketAddr,
        min_order: u64,
        out: &mut [u8; ORPHAN_MAX],
    ) -> Option<(u64, SocketAddr, usize)> {
        self.expire(now);
        let (k, _) = self
            .held
            .iter()
            .enumerate()
            .filter_map(|(k, h)| {
                h.filter(|x| {
                    !x.start && x.order >= min_order && x.dcid == *dcid && x.total == total && x.remote == *remote
                })
                .map(|x| (k, x.order))
            })
            .min_by_key(|(_, order)| *order)?;
        let h = self.held.get(k).copied().flatten()?;
        let src = self.data.get(k)?.get(..h.len)?;
        out.get_mut(..h.len)?.copy_from_slice(src);
        Some((h.order, h.local, h.len))
    }

    /// Let go of the part of order `order`: a session took it.
    pub(crate) fn done(&mut self, order: u64) {
        if let Some(h) = self.held.iter_mut().find(|h| h.is_some_and(|x| x.order == order)) {
            *h = None;
            self.counts.replayed += 1;
        }
    }

    /// Copy the newest fresh start from `remote` of the message of `total` bytes for `dcid` that agrees with `part`
    /// (a datagram with a later part of that message) into `out`, leaving it held; returns the local address it
    /// arrived on and its length. A start agrees when it carries the same bytes as the part at every offset both
    /// cover: every resend of the genuine message carries the same bytes at the same offsets, so a forged start that
    /// differs from the part is not the one the part belongs to.
    pub(crate) fn start_of(
        &mut self,
        now: u64,
        dcid: &ConnId,
        total: u64,
        remote: &SocketAddr,
        part: &[u8],
        out: &mut [u8; ORPHAN_MAX],
    ) -> Option<(SocketAddr, usize)> {
        self.expire(now);
        let (k, _) = self
            .held
            .iter()
            .enumerate()
            .filter_map(|(k, h)| {
                h.filter(|x| {
                    x.start
                        && x.dcid == *dcid
                        && x.total == total
                        && x.remote == *remote
                        && self
                            .data
                            .get(k)
                            .and_then(|d| d.get(..x.len))
                            .is_some_and(|d| agree(d, part))
                })
                .map(|x| (k, x.order))
            })
            .max_by_key(|(_, order)| *order)?;
        let h = self.held.get(k).copied().flatten()?;
        out.get_mut(..h.len)?.copy_from_slice(self.data.get(k)?.get(..h.len)?);
        Some((h.local, h.len))
    }

    /// Whether a fresh datagram from `remote` with a part of the message of `total` bytes for `dcid` is held.
    pub(crate) fn holds(&self, now: u64, dcid: &ConnId, total: u64, remote: &SocketAddr) -> bool {
        self.held.iter().flatten().any(|x| {
            !x.start
                && x.dcid == *dcid
                && x.total == total
                && x.remote == *remote
                && now.saturating_sub(x.at) <= ORPHAN_LIFE
        })
    }

    /// How many datagrams are held now.
    pub(crate) fn waiting(&self) -> usize {
        self.held.iter().flatten().count()
    }
}

/// Test-only driver of the table, for trace validation (cargo feature `trace`, off by default).
#[cfg(feature = "trace")]
pub(crate) mod trace {
    use core::net::SocketAddr;

    use pinc_security::ConnId;

    use super::{ORPHAN_LIFE, ORPHAN_MAX, ORPHANS, Orphans};

    /// What one entry of the table holds, beside the bytes.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct OrphanEntry {
        /// When the datagram arrived.
        pub at: u64,
        /// Its place in the order of arrival.
        pub order: u64,
        /// The destination id it names.
        pub dcid: ConnId,
        /// The length of the message it is a part of.
        pub total: u64,
        /// The local address it arrived on.
        pub local: SocketAddr,
        /// The address it came from.
        pub remote: SocketAddr,
        /// Its length.
        pub len: usize,
    }

    impl Orphans {
        /// Entry `k` of the table, beside the bytes (cargo feature `trace`).
        pub(crate) fn entry(&self, k: usize) -> Option<OrphanEntry> {
            let h = self.held.get(k).copied().flatten()?;
            Some(OrphanEntry {
                at: h.at,
                order: h.order,
                dcid: h.dcid,
                total: h.total,
                local: h.local,
                remote: h.remote,
                len: h.len,
            })
        }
    }

    /// A table of held datagrams of its own, with its state readable after every call.
    pub struct OrphanProbe {
        o: Orphans,
    }

    impl Default for OrphanProbe {
        fn default() -> Self {
            Self::new()
        }
    }

    impl OrphanProbe {
        /// The most datagrams held.
        pub const SLOTS: usize = ORPHANS;
        /// The largest datagram held.
        pub const MAX: usize = ORPHAN_MAX;
        /// How long a held datagram stays useful.
        pub const LIFE: u64 = ORPHAN_LIFE;

        /// An empty table.
        #[must_use]
        pub const fn new() -> Self {
            Self { o: Orphans::new() }
        }

        /// Let go of every datagram older than [`LIFE`](Self::LIFE) at `now`, as the endpoint's timer does.
        pub fn expire(&mut self, now: u64) {
            self.o.expire(now);
        }

        /// Hold a datagram, as the endpoint does for a later part of a first message that names no session.
        pub fn hold(
            &mut self,
            now: u64,
            dcid: ConnId,
            total: u64,
            local: SocketAddr,
            remote: SocketAddr,
            buf: &[u8],
        ) -> bool {
            self.o.hold(now, dcid, total, local, remote, buf)
        }

        /// Give out one held datagram, as the endpoint does for the session the start of the message created.
        pub fn take(
            &mut self,
            now: u64,
            dcid: &ConnId,
            total: u64,
            remote: &SocketAddr,
            out: &mut [u8; ORPHAN_MAX],
        ) -> Option<(SocketAddr, usize)> {
            let (order, local, n) = self.o.next(now, dcid, total, remote, 0, out)?;
            self.o.done(order);
            Some((local, n))
        }

        /// Entry `k` of the table.
        #[must_use]
        pub fn slot(&self, k: usize) -> Option<OrphanEntry> {
            self.o.entry(k)
        }

        /// The bytes entry `k` holds, empty for a free entry.
        #[must_use]
        pub fn bytes(&self, k: usize) -> &[u8] {
            let len = self.o.held.get(k).copied().flatten().map_or(0, |h| h.len);
            self.o.data.get(k).and_then(|d| d.get(..len)).unwrap_or(&[])
        }

        /// The place in the order of arrival the next datagram held takes.
        #[must_use]
        pub const fn order(&self) -> u64 {
            self.o.order
        }

        /// The counters: held, given out, expired, evicted.
        #[must_use]
        pub const fn counts(&self) -> [u64; 4] {
            let c = self.o.counts;
            [c.held, c.replayed, c.expired, c.evicted]
        }

        /// How many datagrams are held now.
        #[must_use]
        pub fn waiting(&self) -> usize {
            self.o.waiting()
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "test assertions")]
mod tests {
    use super::*;

    impl Orphans {
        /// The oldest fresh part, given out once.
        fn take(
            &mut self,
            now: u64,
            dcid: &ConnId,
            total: u64,
            remote: &SocketAddr,
            out: &mut [u8; ORPHAN_MAX],
        ) -> Option<(SocketAddr, usize)> {
            let (order, local, n) = self.next(now, dcid, total, remote, 0, out)?;
            self.done(order);
            Some((local, n))
        }
    }

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

    /// A long Handshake datagram for `cid(1)` carrying `data` at `off` of a message of `total` bytes.
    fn fragment_of(total: u64, off: u64, data: &[u8]) -> std::vec::Vec<u8> {
        use pinc_transport::packet::{LongHeader, LongType};
        let mut body = [0u8; 64];
        let mut w = pinc_wire::Writer::new(&mut body);
        w.put_varint(total).unwrap();
        w.put_varint(off).unwrap();
        w.put_slice(data).unwrap();
        let n = w.written().len();
        let h = LongHeader {
            ty: LongType::Handshake,
            dcid: cid(1),
            scid: cid(2),
            body_len: n,
        };
        let mut d = std::vec![0u8; h.header_len() + n];
        let mut w = pinc_wire::Writer::new(&mut d);
        h.write(&mut w, 0).unwrap();
        w.put_slice(&body[..n]).unwrap();
        d
    }

    #[test]
    fn the_start_a_part_continues_is_the_newest_that_agrees_with_it() {
        let mut o = Orphans::new();
        let (real, forged) = (
            fragment_of(8, 0, &[1, 2, 3, 4]),
            fragment_of(8, 0, &[1, 2, 3, 9, 9, 9, 9, 9]),
        );
        assert!(o.hold_start(0, cid(1), 8, addr(1), addr(5), &real));
        assert!(o.hold_start(1, cid(1), 8, addr(1), addr(5), &forged));
        let mut out = [0u8; ORPHAN_MAX];
        // A part that contradicts the newer start (byte 4 of the real message) continues the older one.
        let part = fragment_of(8, 4, &[5, 6, 7, 8]);
        assert_eq!(
            o.start_of(2, &cid(1), 8, &addr(5), &part, &mut out),
            Some((addr(1), real.len()))
        );
        // A part both starts agree with continues the newest.
        let part = fragment_of(8, 4, &[9, 9, 9, 9]);
        assert_eq!(
            o.start_of(2, &cid(1), 8, &addr(5), &part, &mut out),
            Some((addr(1), forged.len()))
        );
        // A part no start agrees with continues none.
        let part = fragment_of(8, 2, &[0, 0]);
        assert_eq!(o.start_of(2, &cid(1), 8, &addr(5), &part, &mut out), None);
    }
}
