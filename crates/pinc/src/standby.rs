//! The futures of the facade that wait, and how each is woken.
//!
//! Every facade future that cannot finish yet holds a [`Ticket`] in a [`Standby`] slab: its waker, kept current on every
//! poll. A wait on a thing (a stream's bytes, a session's accept queue) is a ticket listed under that thing, and the code
//! that changes the thing calls [`Standby::notify`] with the ticket. The same tickets are the candidates for the driving
//! role: when the future that drives the endpoint ends, [`Standby::baton`] wakes the oldest waiting ticket, which takes
//! the role if it is still waiting.
//!
//! Invariants: a ticket names its slot and the slot's generation, so a notify for a ticket whose future is gone does
//! nothing; a slot is released exactly once, by the future that allocated it; the queue holds whole tickets, at most one
//! per live future, so a future that reuses a released slot queues behind the ones already waiting and the baton skips
//! the entry of a released one; stale entries are dropped when the queue outgrows twice the slab, so it stays within that
//! size, and the slab never outgrows the most futures that waited at once. A stale entry never names a live ticket
//! again, whatever the calls (the slot is released unarmed or not): the release that brings a slot's generation round
//! drops every stale entry, so one of an earlier round cannot match the generation of a new ticket.

use alloc::collections::VecDeque;
use alloc::vec::Vec;
use core::task::Waker;

/// A future's place in the slab.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Ticket {
    idx: u32,
    gen_: u32,
}

#[derive(Default)]
struct Slot {
    gen_: u32,
    waker: Option<Waker>,
    queued: bool,
    live: bool,
}

/// The slab of tickets and the queue of those waiting for the driving role.
#[derive(Default)]
pub(crate) struct Standby {
    slots: Vec<Slot>,
    free: Vec<u32>,
    queue: VecDeque<Ticket>,
    /// Whether the marks of the waiters probe are logged (`trace_waits`).
    #[cfg(feature = "trace")]
    pub(crate) traced: bool,
}

impl Standby {
    /// A new ticket.
    pub(crate) fn alloc(&mut self) -> Ticket {
        if let Some(idx) = self.free.pop()
            && let Some(s) = self.slots.get_mut(idx as usize)
        {
            s.live = true;
            return Ticket { idx, gen_: s.gen_ };
        }
        let idx = u32::try_from(self.slots.len()).unwrap_or(u32::MAX);
        self.slots.push(Slot {
            live: true,
            ..Slot::default()
        });
        // The queue never outgrows twice the slab, so arming allocates nothing once the slab has its size.
        self.queue
            .reserve((self.slots.len().saturating_mul(2) + 1).saturating_sub(self.queue.len()));
        Ticket { idx, gen_: 0 }
    }

    fn slot(&mut self, t: Ticket) -> Option<&mut Slot> {
        self.slots
            .get_mut(t.idx as usize)
            .filter(|s| s.live && s.gen_ == t.gen_)
    }

    /// Keep `waker` as the one to wake for `t`, and make `t` a candidate for the driving role.
    pub(crate) fn arm(&mut self, t: Ticket, waker: &Waker) {
        let Some(s) = self.slot(t) else { return };
        if !s.waker.as_ref().is_some_and(|w| w.will_wake(waker)) {
            s.waker = Some(waker.clone());
        }
        if !s.queued {
            s.queued = true;
            if self.queue.len() >= self.slots.len().saturating_mul(2) {
                self.drop_stale();
            }
            self.queue.push_back(t);
        }
    }

    /// Drop the queue entries whose future is gone.
    fn drop_stale(&mut self) {
        let slots = &self.slots;
        self.queue
            .retain(|t| slots.get(t.idx as usize).is_some_and(|s| s.live && s.gen_ == t.gen_));
    }

    /// Wake `t`'s future if it is armed.
    pub(crate) fn notify(&mut self, t: Ticket) {
        if let Some(w) = self.slot(t).and_then(|s| s.waker.take()) {
            w.wake();
        }
    }

    /// Wake the oldest armed ticket, to offer it the driving role.
    pub(crate) fn baton(&mut self) {
        while let Some(t) = self.queue.pop_front() {
            let Some(s) = self.slot(t) else { continue };
            s.queued = false;
            if let Some(w) = s.waker.take() {
                w.wake();
                return;
            }
        }
    }

    /// Wake every armed ticket (an event the endpoint dropped may have been for any of them).
    pub(crate) fn notify_all(&mut self) {
        for s in &mut self.slots {
            if s.live
                && let Some(w) = s.waker.take()
            {
                w.wake();
            }
        }
    }

    /// Give the ticket's slot back.
    pub(crate) fn release(&mut self, t: Ticket) {
        let idx = t.idx;
        let Some(s) = self.slot(t) else { return };
        s.live = false;
        let wraps = s.gen_ == u32::MAX;
        s.gen_ = s.gen_.wrapping_add(1);
        s.waker = None;
        s.queued = false;
        self.free.push(idx);
        // The one release in 2^32 of a slot that brings its generation back round: no entry of an earlier round may
        // outlive it, or it would name the slot's next ticket.
        if wraps {
            self.drop_stale();
        }
    }
}

/// A slab of its own for the trace check, driven call by call with tickets and wakers named by numbers.
#[cfg(feature = "trace")]
pub(crate) mod trace {
    use alloc::sync::Arc;
    use alloc::task::Wake;
    use alloc::vec::Vec;
    use core::task::Waker;
    use std::sync::{Mutex, PoisonError};

    use super::{Standby, Ticket};

    /// A waker that writes its number into the log when it is woken.
    struct Named {
        id: u32,
        log: Arc<Mutex<Vec<u32>>>,
    }

    impl Wake for Named {
        fn wake(self: Arc<Self>) {
            self.wake_by_ref();
        }
        fn wake_by_ref(self: &Arc<Self>) {
            self.log.lock().unwrap_or_else(PoisonError::into_inner).push(self.id);
        }
    }

    /// What one slot of the slab holds.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct StandbySlot {
        /// The generation a ticket must name.
        pub generation: u32,
        /// The number of the waker kept, `None` if none is.
        pub waker: Option<u32>,
        /// The slot is in the queue of those waiting for the driving role.
        pub queued: bool,
        /// A future holds the slot.
        pub live: bool,
    }

    /// A slab of tickets with its state readable after every call; a waker is named by a number, and every call
    /// returns the numbers of the wakers it woke, in the order it woke them.
    pub struct StandbyProbe {
        s: Standby,
        log: Arc<Mutex<Vec<u32>>>,
        wakers: Vec<Waker>,
    }

    impl Default for StandbyProbe {
        fn default() -> Self {
            Self::new()
        }
    }

    impl StandbyProbe {
        /// An empty slab.
        #[must_use]
        pub fn new() -> Self {
            Self {
                s: Standby::default(),
                log: Arc::new(Mutex::new(Vec::new())),
                wakers: Vec::new(),
            }
        }

        fn waker(&mut self, id: u32) -> Waker {
            while self.wakers.len() <= id as usize {
                let id = u32::try_from(self.wakers.len()).unwrap_or(u32::MAX);
                self.wakers.push(Waker::from(Arc::new(Named {
                    id,
                    log: Arc::clone(&self.log),
                })));
            }
            self.wakers
                .get(id as usize)
                .cloned()
                .unwrap_or_else(|| Waker::noop().clone())
        }

        fn woken(&self) -> Vec<u32> {
            std::mem::take(&mut *self.log.lock().unwrap_or_else(PoisonError::into_inner))
        }

        /// A new ticket, as its slot and generation.
        pub fn alloc(&mut self) -> (u32, u32) {
            let t = self.s.alloc();
            (t.idx, t.gen_)
        }

        /// Arm the ticket `(idx, generation)` with the waker numbered `waker`; what it woke (nothing).
        pub fn arm(&mut self, idx: u32, generation: u32, waker: u32) -> Vec<u32> {
            let w = self.waker(waker);
            self.s.arm(Ticket { idx, gen_: generation }, &w);
            self.woken()
        }

        /// Notify the ticket `(idx, generation)`; the waker it woke, if any.
        pub fn notify(&mut self, idx: u32, generation: u32) -> Vec<u32> {
            self.s.notify(Ticket { idx, gen_: generation });
            self.woken()
        }

        /// Offer the driving role; the waker it woke, if any.
        pub fn baton(&mut self) -> Vec<u32> {
            self.s.baton();
            self.woken()
        }

        /// Wake every armed ticket; the wakers woken, in the order of their slots.
        pub fn notify_all(&mut self) -> Vec<u32> {
            self.s.notify_all();
            self.woken()
        }

        /// Release the ticket `(idx, generation)`; what it woke (nothing).
        pub fn release(&mut self, idx: u32, generation: u32) -> Vec<u32> {
            self.s.release(Ticket { idx, gen_: generation });
            self.woken()
        }

        /// The slots, in order.
        pub fn slots(&self) -> Vec<StandbySlot> {
            self.s
                .slots
                .iter()
                .map(|s| StandbySlot {
                    generation: s.gen_,
                    waker: s.waker.as_ref().and_then(|w| {
                        self.wakers
                            .iter()
                            .position(|m| m.will_wake(w))
                            .and_then(|i| u32::try_from(i).ok())
                    }),
                    queued: s.queued,
                    live: s.live,
                })
                .collect()
        }

        /// The free slots, as the code's stack holds them (the last is taken first).
        pub fn free(&self) -> Vec<u32> {
            self.s.free.clone()
        }

        /// The queue of those waiting for the driving role as tickets (slot and generation), front first; the entry of a
        /// released ticket stays until the baton or a compaction drops it.
        pub fn queue(&self) -> Vec<(u32, u32)> {
            self.s.queue.iter().map(|t| (t.idx, t.gen_)).collect()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Set the generation of slot 0, as the releases of that many rounds leave it.
    fn set_gen(st: &mut Standby, gen_: u32) {
        if let Some(s) = st.slots.get_mut(0) {
            s.gen_ = gen_;
        }
    }

    /// The witness of the model: alloc, arm, release, alloc, release, alloc, the generation brought round to the one
    /// the first entry names by the releases between. The stale entry must not be the new ticket's place.
    #[test]
    fn a_stale_entry_does_not_name_the_ticket_a_wrapped_generation_hands_out() {
        let mut st = Standby::default();
        let w = Waker::noop();
        st.alloc();
        set_gen(&mut st, u32::MAX);
        let first = Ticket { idx: 0, gen_: u32::MAX };
        st.arm(first, w);
        st.release(first);
        let second = st.alloc();
        assert_eq!(second.gen_, 0, "the release wrapped the generation");
        st.release(second);
        // 2^32 - 2 more releases of the slot bring its generation back to the one the first entry names
        set_gen(&mut st, u32::MAX);
        let third = st.alloc();
        assert_eq!(third, first, "the slot hands out the generation the first entry names");
        st.arm(third, w);
        assert_eq!(
            st.queue.iter().filter(|q| **q == third).count(),
            1,
            "the future has one live entry in the queue"
        );
        assert!(
            st.queue.len() <= 2 * st.slots.len(),
            "the queue stays within twice the slab"
        );
    }
}
