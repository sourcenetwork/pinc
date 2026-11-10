//! The futures of the facade that wait, and how each is woken.
//!
//! Every facade future that cannot finish yet holds a [`Ticket`] in a [`Standby`] slab: its waker, kept current on every
//! poll. A wait on a thing (a stream's bytes, a session's accept queue) is a ticket listed under that thing, and the code
//! that changes the thing calls [`Standby::notify`] with the ticket. The same tickets are the candidates for the driving
//! role: when the future that drives the endpoint ends, [`Standby::baton`] wakes the oldest waiting ticket, which takes
//! the role if it is still waiting.
//!
//! Invariants: a ticket names its slot and the slot's generation, so a notify for a ticket whose future is gone does
//! nothing; a slot is released exactly once, by the future that allocated it; the queue holds each slot at most once, so
//! it never outgrows the slab, and the slab never outgrows the most futures that waited at once.

use std::collections::VecDeque;
use std::task::Waker;

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
    queue: VecDeque<u32>,
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
            self.queue.push_back(t.idx);
        }
    }

    /// Wake `t`'s future if it is armed.
    pub(crate) fn notify(&mut self, t: Ticket) {
        if let Some(w) = self.slot(t).and_then(|s| s.waker.take()) {
            w.wake();
        }
    }

    /// Wake the oldest armed ticket, to offer it the driving role.
    pub(crate) fn baton(&mut self) {
        while let Some(idx) = self.queue.pop_front() {
            let Some(s) = self.slots.get_mut(idx as usize) else {
                continue;
            };
            s.queued = false;
            if s.live
                && let Some(w) = s.waker.take()
            {
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
        if let Some(s) = self.slot(t) {
            s.live = false;
            s.gen_ = s.gen_.wrapping_add(1);
            s.waker = None;
            self.free.push(idx);
        }
    }
}
