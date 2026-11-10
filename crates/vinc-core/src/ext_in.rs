//! Extension frames received for the application, held until it reads them.
//!
//! The endpoint itself consumes the sub-session open and `REACH_OUT` frames; every other extension frame (a range
//! proof, for one) goes into a ring of [`EXT_SLOTS`] frames in arrival order, and the host reads them oldest first
//! with [`Endpoint::read_extension`](crate::Endpoint::read_extension). A frame the application protocol loses is
//! asked for again by that protocol, so a host that falls behind loses the oldest frame, never the newest.
//!
//! Invariants: a body longer than [`EXT_BODY_MAX`] is never stored; the ring never grows; frames leave in the order
//! they arrived.

use crate::api::SessionId;

/// The longest extension body held for the application.
pub const EXT_BODY_MAX: usize = 1200;
/// Frames held at once.
pub(crate) const EXT_SLOTS: usize = 8;

#[derive(Debug, Clone, Copy)]
struct Held {
    session: SessionId,
    ty: u64,
    len: usize,
    body: [u8; EXT_BODY_MAX],
}

#[derive(Debug)]
pub(crate) struct ExtRing {
    items: [Option<Held>; EXT_SLOTS],
    head: usize,
    len: usize,
}

impl ExtRing {
    pub(crate) const fn new() -> Self {
        Self {
            items: [None; EXT_SLOTS],
            head: 0,
            len: 0,
        }
    }

    /// Keep a frame; a full ring drops its oldest. False if the body is too long to keep.
    pub(crate) fn put(&mut self, session: SessionId, ty: u64, body: &[u8]) -> bool {
        let mut held = Held {
            session,
            ty,
            len: body.len(),
            body: [0; EXT_BODY_MAX],
        };
        let Some(dst) = held.body.get_mut(..body.len()) else {
            return false;
        };
        dst.copy_from_slice(body);
        if self.len == EXT_SLOTS {
            self.head = (self.head + 1) % EXT_SLOTS;
            self.len -= 1;
        }
        let at = (self.head + self.len) % EXT_SLOTS;
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(held);
            self.len += 1;
        }
        true
    }

    /// Copy the oldest frame into `out` and remove it: its session, type and length. `Err(len)` if it does not fit
    /// `out` (it stays held).
    pub(crate) fn take(&mut self, out: &mut [u8]) -> Result<Option<(SessionId, u64, usize)>, usize> {
        if self.len == 0 {
            return Ok(None);
        }
        let Some(h) = self.items.get(self.head).copied().flatten() else {
            return Ok(None);
        };
        let dst = out.get_mut(..h.len).ok_or(h.len)?;
        dst.copy_from_slice(h.body.get(..h.len).unwrap_or_default());
        if let Some(s) = self.items.get_mut(self.head) {
            *s = None;
        }
        self.head = (self.head + 1) % EXT_SLOTS;
        self.len -= 1;
        Ok(Some((h.session, h.ty, h.len)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frames_leave_in_order_and_a_full_ring_drops_the_oldest() {
        let mut r = ExtRing::new();
        let mut out = [0u8; EXT_BODY_MAX];
        for i in 0..=EXT_SLOTS as u8 {
            assert!(r.put(SessionId(1), 0x49, &[i; 3]));
        }
        for i in 1..=EXT_SLOTS as u8 {
            assert_eq!(r.take(&mut out), Ok(Some((SessionId(1), 0x49, 3))));
            assert_eq!(out[..3], [i; 3]);
        }
        assert_eq!(r.take(&mut out), Ok(None));
    }

    #[test]
    fn a_body_too_long_is_refused_and_one_that_does_not_fit_the_buffer_stays() {
        let mut r = ExtRing::new();
        assert!(!r.put(SessionId(1), 0x49, &[0; EXT_BODY_MAX + 1]));
        assert!(r.put(SessionId(2), 0x4f, &[7; 10]));
        assert_eq!(r.take(&mut [0u8; 4]), Err(10));
        assert_eq!(r.take(&mut [0u8; 10]), Ok(Some((SessionId(2), 0x4f, 10))));
    }
}
