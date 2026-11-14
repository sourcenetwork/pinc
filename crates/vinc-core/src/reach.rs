//! `REACH_OUT` bodies received from peers, held until the application reads them.
//!
//! The body is the peer's candidate addresses, encoded by the layer above; the endpoint only carries it. A ring of
//! [`REACH_SLOTS`] bodies holds the latest per session, oldest overwritten first, so a host that reads on
//! [`Event::ReachOut`](crate::Event::ReachOut) never misses one and a host that falls behind loses the oldest.
//!
//! Invariants: a body longer than [`REACH_BODY_MAX`] is never stored; the ring never grows.

use crate::api::SessionId;

/// The longest `REACH_OUT` body: a count byte and eight addresses of 19 bytes.
pub const REACH_BODY_MAX: usize = 1 + 8 * 19;
/// Bodies held at once.
pub(crate) const REACH_SLOTS: usize = 4;

#[derive(Debug, Clone, Copy)]
struct Held {
    session: SessionId,
    len: usize,
    body: [u8; REACH_BODY_MAX],
}

#[derive(Debug)]
pub(crate) struct ReachRing {
    items: [Option<Held>; REACH_SLOTS],
    next: usize,
}

impl ReachRing {
    pub(crate) const fn new() -> Self {
        Self {
            items: [None; REACH_SLOTS],
            next: 0,
        }
    }

    /// Keep `body` as the latest of `session`.
    pub(crate) fn put(&mut self, session: SessionId, body: &[u8]) {
        let mut held = Held {
            session,
            len: body.len(),
            body: [0; REACH_BODY_MAX],
        };
        let Some(dst) = held.body.get_mut(..body.len()) else {
            return;
        };
        dst.copy_from_slice(body);
        let at = self
            .items
            .iter()
            .position(|h| h.is_some_and(|h| h.session == session))
            .unwrap_or(self.next);
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(held);
        }
        if at == self.next {
            self.next = (self.next + 1) % REACH_SLOTS;
        }
    }

    pub(crate) fn get(&self, session: SessionId) -> Option<&[u8]> {
        self.items
            .iter()
            .flatten()
            .find(|h| h.session == session)
            .and_then(|h| h.body.get(..h.len))
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

        /// Keep `body` as the latest of `session`.
        pub fn put(&mut self, session: u64, body: &[u8]) {
            self.r.put(SessionId(session), body);
        }

        /// The body held for `session`.
        #[must_use]
        pub fn get(&self, session: u64) -> Option<&[u8]> {
            self.r.get(SessionId(session))
        }

        /// The place the next new session takes.
        #[must_use]
        pub const fn next(&self) -> usize {
            self.r.next
        }

        /// The session, length and first byte of the body in place `k`.
        #[must_use]
        pub fn cell(&self, k: usize) -> Option<(u64, usize, u8)> {
            let h = self.r.items.get(k).copied().flatten()?;
            Some((h.session.0, h.len, h.body.first().copied().unwrap_or(0)))
        }
    }
}
