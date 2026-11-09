//! The bounded queue of events waiting for the host.
//!
//! Invariants: the queue never holds more than `N` events; when full, a new event that the application can recover by
//! reading state is dropped, and any other new event evicts the oldest recoverable one, or failing that the oldest
//! event; every drop is counted; events leave in the order they entered.

use crate::api::Event;

/// A fixed ring of events.
#[derive(Debug)]
pub(crate) struct EventRing<const N: usize> {
    items: [Option<Event>; N],
    head: usize,
    len: usize,
    pub(crate) dropped: u64,
}

impl<const N: usize> EventRing<N> {
    pub(crate) const fn new() -> Self {
        Self {
            items: [None; N],
            head: 0,
            len: 0,
            dropped: 0,
        }
    }

    fn at(&self, i: usize) -> usize {
        (self.head + i) % N
    }

    pub(crate) fn push(&mut self, ev: Event) {
        if self.len == N {
            self.dropped += 1;
            if ev.lossy() {
                return;
            }
            let victim = (0..self.len)
                .find(|i| {
                    self.items
                        .get(self.at(*i))
                        .copied()
                        .flatten()
                        .is_some_and(|e| e.lossy())
                })
                .unwrap_or(0);
            for i in (0..victim).rev() {
                let (from, to) = (self.at(i), self.at(i + 1));
                let moved = self.items.get(from).copied().flatten();
                if let Some(s) = self.items.get_mut(to) {
                    *s = moved;
                }
            }
            self.head = (self.head + 1) % N;
            self.len -= 1;
        }
        let at = self.at(self.len);
        if let Some(s) = self.items.get_mut(at) {
            *s = Some(ev);
            self.len += 1;
        }
    }

    pub(crate) fn pop(&mut self) -> Option<Event> {
        if self.len == 0 {
            return None;
        }
        let e = self.items.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % N;
        self.len -= 1;
        e
    }
}
