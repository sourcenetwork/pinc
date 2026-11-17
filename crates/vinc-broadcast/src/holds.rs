//! The slots that hold messages set aside until a decision arrives (the access hold and the floor hold).
//!
//! One zeroed block is made at start, `slots` slots of `slot_len` bytes each, with a free list of slot indices and a
//! flag per slot. Taking a slot, writing into it and giving it back touch no allocator, so a held message costs the
//! heap nothing. The block is not written until a slot is used, so the system maps it as it is needed.
//!
//! Invariants: a slot is either free (on the free list, flag clear) or live (flag set, off the list); a slot is
//! given back at most once per take; a read returns exactly the bytes the take wrote, never the tail of an earlier
//! message; the table never holds more live slots than it has.

use alloc::boxed::Box;
use alloc::vec;

/// The slot table. See the module docs.
#[derive(Debug, Default)]
pub(crate) struct Holds {
    buf: Box<[u8]>,
    /// Where a slot read out is staged, so that the slot can be free while its message is offered again.
    stage: Box<[u8]>,
    slot_len: usize,
    free: Box<[u16]>,
    nfree: usize,
    live: Box<[bool]>,
}

impl Holds {
    /// A table of `slots` slots of `slot_len` bytes each (`slots` at most 65,535).
    pub(crate) fn new(slots: usize, slot_len: usize) -> Self {
        let slots = slots.min(usize::from(u16::MAX));
        Self {
            buf: vec![0; slots.saturating_mul(slot_len)].into_boxed_slice(),
            stage: vec![0; slot_len].into_boxed_slice(),
            slot_len,
            free: (0..u16::try_from(slots).unwrap_or(u16::MAX)).rev().collect(),
            nfree: slots,
            live: vec![false; slots].into_boxed_slice(),
        }
    }

    /// Whether an entry of `len` bytes fits a slot.
    pub(crate) const fn fits(&self, len: usize) -> bool {
        len <= self.slot_len
    }

    /// Write `topic_len | topic | head | body` into a free slot; its index and length, or `None` for a topic over 255
    /// bytes, an entry larger than a slot, or no free slot.
    pub(crate) fn put(&mut self, topic: &[u8], head: &[u8], body: &[u8]) -> Option<(u16, u32)> {
        let tl = u8::try_from(topic.len()).ok()?;
        let len = 1usize
            .checked_add(topic.len())?
            .checked_add(head.len())?
            .checked_add(body.len())?;
        if !self.fits(len) || self.nfree == 0 {
            return None;
        }
        let slot = *self.free.get(self.nfree - 1)?;
        let at = usize::from(slot) * self.slot_len;
        let dst = self.buf.get_mut(at..at + len)?;
        let (first, rest) = dst.split_first_mut()?;
        *first = tl;
        let (t, rest) = rest.split_at_mut(topic.len());
        t.copy_from_slice(topic);
        let (hd, bd) = rest.split_at_mut(head.len());
        hd.copy_from_slice(head);
        bd.copy_from_slice(body);
        self.nfree -= 1;
        *self.live.get_mut(usize::from(slot))? = true;
        Some((slot, u32::try_from(len).ok()?))
    }

    /// Give `slot` back; false if it is not live (a slot given back twice, or one that was never taken).
    pub(crate) fn give(&mut self, slot: u16) -> bool {
        let Some(live) = self.live.get_mut(usize::from(slot)).filter(|l| **l) else {
            return false;
        };
        *live = false;
        let Some(place) = self.free.get_mut(self.nfree) else {
            return false;
        };
        *place = slot;
        self.nfree += 1;
        true
    }

    /// Read the `len` bytes of live `slot` into the stage and give the slot back, so the message can be offered while
    /// its slot is free for the next hold. The staged bytes come back as a box that [`Holds::restage`] returns; `None`
    /// if the slot is not live or its entry is longer than `len` allows. The slot is given back in either case.
    pub(crate) fn take_out(&mut self, slot: u16, len: u32) -> Option<Box<[u8]>> {
        let len = usize::try_from(len).ok()?;
        let at = usize::from(slot) * self.slot_len;
        let live = self.live.get(usize::from(slot)).copied().unwrap_or(false);
        let src = live.then(|| self.buf.get(at..at + len)).flatten();
        let staged = match (src, self.stage.get_mut(..len)) {
            (Some(s), Some(d)) => {
                d.copy_from_slice(s);
                true
            }
            _ => false,
        };
        self.give(slot);
        if !staged {
            return None;
        }
        Some(core::mem::take(&mut self.stage))
    }

    /// Hand back the box [`Holds::take_out`] returned.
    pub(crate) fn restage(&mut self, stage: Box<[u8]>) {
        self.stage = stage;
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// A slot is taken, read back whole and given back; the table then has the slot again.
    #[test]
    fn a_slot_is_taken_and_given_back() {
        let mut h = Holds::new(2, 32);
        let (slot, len) = h.put(b"t", b"hh", b"body").unwrap();
        assert_eq!(len, 1 + 1 + 2 + 4);
        let st = h.take_out(slot, len).unwrap();
        assert_eq!(st.get(..len as usize), Some(&b"\x01thhbody"[..]));
        h.restage(st);
        assert!(h.put(b"t", b"", b"x").is_some() && h.put(b"t", b"", b"y").is_some());
    }

    /// No slot is left: the third entry is refused, and a slot given back is taken again.
    #[test]
    fn a_full_table_refuses_and_a_given_back_slot_is_reused() {
        let mut h = Holds::new(2, 16);
        let (a, _) = h.put(b"t", b"", b"1").unwrap();
        h.put(b"t", b"", b"2").unwrap();
        assert!(h.put(b"t", b"", b"3").is_none());
        assert!(h.give(a));
        assert_eq!(h.put(b"t", b"", b"3").unwrap().0, a);
    }

    /// An entry larger than a slot, and a topic over 255 bytes, are refused.
    #[test]
    fn an_entry_larger_than_a_slot_is_refused() {
        let mut h = Holds::new(1, 8);
        assert!(h.fits(8) && !h.fits(9));
        assert!(h.put(b"t", b"", &[0; 6]).is_some());
        let mut h = Holds::new(1, 8);
        assert!(h.put(b"t", b"", &[0; 8]).is_none());
        let mut h = Holds::new(1, 1000);
        assert!(h.put(&[0; 256], b"", b"").is_none());
    }

    /// A slot given back twice is refused the second time, and one never taken is refused too.
    #[test]
    fn a_slot_given_back_twice_is_refused() {
        let mut h = Holds::new(2, 8);
        let (a, _) = h.put(b"t", b"", b"1").unwrap();
        assert!(h.give(a));
        assert!(!h.give(a));
        assert!(!h.give(1));
        assert!(!h.give(9));
        // The free list holds each slot once: two takes, then full.
        assert!(h.put(b"t", b"", b"1").is_some() && h.put(b"t", b"", b"2").is_some());
        assert!(h.put(b"t", b"", b"3").is_none());
    }

    /// A read of a freed slot yields nothing, and a shorter entry in a reused slot reads without the tail of the
    /// longer one before it.
    #[test]
    fn the_bytes_of_a_freed_slot_are_never_read_as_another_message() {
        let mut h = Holds::new(1, 32);
        let (slot, len) = h.put(b"t", b"", b"long old body").unwrap();
        let st = h.take_out(slot, len).unwrap();
        h.restage(st);
        assert!(h.take_out(slot, len).is_none(), "a freed slot reads nothing");
        let (slot2, len2) = h.put(b"t", b"", b"new").unwrap();
        assert_eq!(slot2, slot);
        let st = h.take_out(slot2, len2).unwrap();
        assert_eq!(st.get(..len2 as usize), Some(&b"\x01tnew"[..]));
        h.restage(st);
        assert!(h.take_out(slot2, len2).is_none());
    }
}
