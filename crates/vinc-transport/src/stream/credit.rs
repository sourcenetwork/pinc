//! Stream admission credit: how many streams the peer will admit, so an opener never sends a stream the receiver has
//! no room for.
//!
//! The credit is a cumulative limit like a flow-control limit: `limit` is the number of streams the opener may have
//! opened in all, of every kind. The receiver derives it as the streams it admitted so far plus the room it has now
//! (slots, the live-stream cap, and first charges that fit the pool beside one for each open stream), tells the
//! opener the first value in the handshake (`max_streams` of the credit record) and raises it with a `MAX_STREAMS`
//! frame. A limit only grows: a shrinking pool is not taken back, the receiver holds back the surplus stream instead.
//!
//! Invariants: `limit` and `adv` never decrease; a frame is queued only when `adv` grew; a raise of less than an
//! eighth of the credit last given waits unless the opener has used up all of it.

/// The credit state of both directions of a stream table.
#[derive(Debug, Clone, Copy, Default)]
pub(super) struct Admit {
    /// As opener: the most streams we may have opened in all, as the peer last said.
    pub(super) limit: u64,
    /// As receiver: the limit last advertised, the handshake value first.
    pub(super) adv: u64,
    /// The streams admitted when `adv` was set.
    pub(super) adv_at: u64,
    /// A `MAX_STREAMS` frame with `adv` is waiting to be sent.
    pub(super) pend: bool,
    /// The receiver side is on: credit is given and kept in the pool.
    pub(super) on: bool,
    /// Opens may pass `limit`, which the peer has not stated yet: they wait for it to cover them.
    pub(super) early: bool,
}

impl Admit {
    pub(super) const NEW: Self = Self {
        limit: 0,
        adv: 0,
        adv_at: 0,
        pend: false,
        on: true,
        early: false,
    };

    /// The peer raised the limit on what we may open.
    pub(super) fn raise_limit(&mut self, limit: u64) {
        self.limit = self.limit.max(limit);
    }

    /// Whether a stream may be opened when `opened` have been in all.
    pub(super) const fn allows(&self, opened: u64) -> bool {
        opened < self.limit
    }

    /// The receiver admitted `admitted` streams in all and has room for `room` more now: queue a raise of the
    /// advertised limit when it grew by an eighth of the credit last given (one stream at least), or by anything once
    /// the opener has used all it was given.
    pub(super) fn update(&mut self, admitted: u64, room: u64) {
        let now = admitted.saturating_add(room);
        if !self.on || now <= self.adv {
            return;
        }
        let used_up = self.adv <= admitted;
        let step = (self.adv.saturating_sub(self.adv_at) / 8).max(1);
        if used_up || now - self.adv >= step {
            self.adv = now;
            self.adv_at = admitted;
            self.pend = true;
        }
    }

    /// Take the frame to send, if one waits.
    pub(super) fn take(&mut self) -> Option<u64> {
        core::mem::take(&mut self.pend).then_some(self.adv)
    }

    /// A frame with `limit` was lost: send the current limit again unless a later one superseded it.
    pub(super) fn lost(&mut self, limit: u64) {
        if limit >= self.adv {
            self.pend = true;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn receiver(first: u64) -> Admit {
        Admit {
            adv: first,
            ..Admit::NEW
        }
    }

    #[test]
    fn the_opener_may_open_up_to_the_limit_and_the_limit_only_grows() {
        let mut a = Admit::NEW;
        assert!(!a.allows(0));
        a.raise_limit(4);
        assert!(a.allows(3) && !a.allows(4));
        a.raise_limit(2);
        assert!(!a.allows(4), "a smaller limit does not take credit back");
        a.raise_limit(9);
        assert!(a.allows(8) && !a.allows(9));
    }

    #[test]
    fn a_small_raise_waits_and_a_used_up_credit_is_raised_at_once() {
        // 16 streams of credit given at the start: a raise of 1 is under an eighth (2), so it waits.
        let mut r = receiver(16);
        r.update(10, 7);
        assert_eq!(r.take(), None);
        // A raise of 2 reaches the eighth.
        r.update(10, 8);
        assert_eq!(r.take(), Some(18));
        assert_eq!(r.take(), None, "a frame is taken once");
        // The opener used up all 18: any growth is sent.
        r.update(18, 1);
        assert_eq!(r.take(), Some(19));
    }

    #[test]
    fn no_growth_and_no_shrink_queue_nothing() {
        let mut r = receiver(8);
        r.update(0, 8);
        r.update(3, 2);
        assert_eq!(r.take(), None);
        assert_eq!(r.adv, 8, "the advertised limit never drops");
    }

    #[test]
    fn a_lost_frame_is_sent_again_unless_superseded() {
        let mut r = receiver(4);
        r.update(4, 4);
        assert_eq!(r.take(), Some(8));
        r.lost(8);
        assert_eq!(r.take(), Some(8));
        r.update(8, 4);
        r.lost(8);
        assert_eq!(r.take(), Some(12), "the newer limit goes out, not the old one");
        assert_eq!(r.take(), None);
    }
}
