//! `REACH_OUT` bodies received from peers, held until the application reads them.
//!
//! The body is the peer's candidate addresses, encoded by the layer above; the endpoint only carries it. A ring of
//! [`REACH_SLOTS`] bodies holds the latest per session; a body of a session not held yet takes a free slot, else the slot of the body that was
//! put longest ago (a refresh of a session counts as a put), so a host that reads on
//! [`Event::ReachOut`](crate::Event::ReachOut) never misses one and a host that falls behind loses the oldest. Every
//! body the ring loses is counted by its caller.
//!
//! Invariants: a body longer than [`REACH_BODY_MAX`] is never stored; the ring never grows; the body evicted is the
//! one put longest ago.

use crate::api::SessionId;

/// The longest `REACH_OUT` body: a count byte and eight addresses of 19 bytes.
pub const REACH_BODY_MAX: usize = 1 + 8 * 19;
/// Bodies held at once.
pub(crate) const REACH_SLOTS: usize = 4;

#[derive(Debug, Clone, Copy)]
struct Held {
    session: SessionId,
    len: usize,
    /// The ring's put counter when this body was put.
    stamp: u64,
    body: [u8; REACH_BODY_MAX],
}

#[derive(Debug)]
pub(crate) struct ReachRing {
    items: [Option<Held>; REACH_SLOTS],
    clock: u64,
}

impl ReachRing {
    pub(crate) const fn new() -> Self {
        Self {
            items: [None; REACH_SLOTS],
            clock: 0,
        }
    }

    /// Keep `body` as the latest of `session`. Returns how many bodies were lost: 1 if `body` is too long to keep or
    /// the ring was full and gave up the body put longest ago, else 0.
    pub(crate) fn put(&mut self, session: SessionId, body: &[u8]) -> u64 {
        self.clock = self.clock.wrapping_add(1);
        let mut held = Held {
            session,
            len: body.len(),
            stamp: self.clock,
            body: [0; REACH_BODY_MAX],
        };
        let Some(dst) = held.body.get_mut(..body.len()) else {
            return 1;
        };
        dst.copy_from_slice(body);
        let same = self.items.iter().position(|h| h.is_some_and(|h| h.session == session));
        let Some(at) = same
            .or_else(|| self.items.iter().position(Option::is_none))
            .or_else(|| {
                self.items
                    .iter()
                    .enumerate()
                    .min_by_key(|(_, h)| h.map_or(0, |h| h.stamp))
                    .map(|(i, _)| i)
            })
        else {
            return 1;
        };
        let lost = u64::from(same.is_none() && self.items.get(at).is_some_and(Option::is_some));
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(held);
        }
        lost
    }

    pub(crate) fn get(&self, session: SessionId) -> Option<&[u8]> {
        self.items
            .iter()
            .flatten()
            .find(|h| h.session == session)
            .and_then(|h| h.body.get(..h.len))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(i: u64) -> SessionId {
        SessionId(i)
    }

    #[test]
    fn the_body_put_longest_ago_is_evicted_first() {
        let mut r = ReachRing::new();
        for (i, b) in [(1, b'A'), (2, b'B'), (3, b'C'), (4, b'D'), (2, b'b'), (5, b'E')] {
            r.put(s(i), &[b]);
        }
        // E took A's slot; the refreshed B is the youngest but one.
        assert_eq!(r.get(s(1)), None);
        r.put(s(6), b"F");
        assert_eq!(r.get(s(2)), Some(&b"b"[..]));
        assert_eq!(r.get(s(3)), None, "C was older than the refreshed B");
        assert_eq!(r.get(s(4)), Some(&b"D"[..]));
        assert_eq!(r.get(s(5)), Some(&b"E"[..]));
        assert_eq!(r.get(s(6)), Some(&b"F"[..]));
    }

    #[test]
    fn a_refresh_loses_nothing_and_an_overflow_or_a_long_body_counts() {
        let mut r = ReachRing::new();
        for i in 1..=REACH_SLOTS as u64 {
            assert_eq!(r.put(s(i), &[1]), 0);
        }
        assert_eq!(r.put(s(1), &[2]), 0, "a refresh replaces its own body");
        assert_eq!(r.put(s(9), &[3]), 1, "a full ring gives up one");
        assert_eq!(r.put(s(1), &[0; REACH_BODY_MAX + 1]), 1, "a body too long is lost");
    }
}

#[cfg(feature = "trace")]
pub(crate) mod trace {
    use super::{REACH_BODY_MAX, REACH_SLOTS, ReachRing};
    use crate::api::SessionId;

    /// A ring of its own, with its state readable after every call.
    pub struct ReachProbe {
        r: ReachRing,
    }

    impl Default for ReachProbe {
        fn default() -> Self {
            Self::new()
        }
    }

    impl ReachProbe {
        /// The places of the ring.
        pub const SLOTS: usize = REACH_SLOTS;
        /// The longest body kept.
        pub const BODY_MAX: usize = REACH_BODY_MAX;

        /// An empty ring.
        #[must_use]
        pub const fn new() -> Self {
            Self { r: ReachRing::new() }
        }

        /// Keep `body` as the latest of `session`; how many bodies were lost.
        pub fn put(&mut self, session: u64, body: &[u8]) -> u64 {
            self.r.put(SessionId(session), body)
        }

        /// The body held for `session`.
        #[must_use]
        pub fn get(&self, session: u64) -> Option<&[u8]> {
            self.r.get(SessionId(session))
        }

        /// The session, length and first byte of the body in place `k`.
        #[must_use]
        pub fn cell(&self, k: usize) -> Option<(u64, usize, u8)> {
            let h = self.r.items.get(k).copied().flatten()?;
            Some((h.session.0, h.len, h.body.first().copied().unwrap_or(0)))
        }
    }
}
