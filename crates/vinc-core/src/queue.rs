//! The bounded queue of events waiting for the host.
//!
//! The ring holds `4 * K + EVENT_BASE` events for a table of `K` sessions: its memory grows with the table, as an
//! array of `K`-event rows, so it needs no allocation and no extra type parameter.
//!
//! Invariants: the queue never holds more than that many events; events leave in the order they entered; every drop is
//! counted. A full queue drops a new event the application can recover by reading state, and for any other new event
//! evicts the oldest recoverable one. An event the application cannot recover is evicted only if the queue holds
//! nothing else, which the endpoint prevents: while [`EventRing::stalled`], that is while fewer than `2 * K + 64`
//! places remain beyond the unrecoverable events queued, it starts no session, holds timers and dials back, refuses the
//! packets that would raise events and parks the work it could not finish until the host reads events. One step
//! the endpoint takes without checking the queue again (one connection event, one timer, one command) emits at most
//! one event per session twice over and a few more, which the headroom covers for any `K`.

use crate::api::Event;
use crate::store::{Store, filled, store_fn};

/// The places of the event queue besides the four rows of `K`.
pub const EVENT_BASE: usize = 1024;

/// How many events an endpoint with a table of `sessions` sessions can leave unread.
pub const fn event_queue(sessions: usize) -> usize {
    4 * sessions + EVENT_BASE
}

/// The places the endpoint keeps free of unrecoverable events for a table of `sessions` sessions.
pub const fn event_headroom(sessions: usize) -> usize {
    2 * sessions + 64
}

/// A fixed ring of events for a table of `K` sessions.
#[derive(Debug)]
pub(crate) struct EventRing<const K: usize> {
    base: Store<Option<Event>, EVENT_BASE>,
    rows: [Store<Option<Event>, K>; 4],
    head: usize,
    len: usize,
    /// How many of the queued events the application can recover by reading state.
    lossy_len: usize,
    pub(crate) dropped: u64,
    /// Unrecoverable events dropped because the queue held nothing else to give up.
    pub(crate) lost: u64,
}

impl<const K: usize> EventRing<K> {
    const CAP: usize = event_queue(K);

    store_fn! {
    pub(crate) fn new() -> Self {
        const { assert!(event_queue(K) >= 2 * event_headroom(K)) };
        Self {
            base: filled(None),
            rows: [filled(None), filled(None), filled(None), filled(None)],
            head: 0,
            len: 0,
            lossy_len: 0,
            dropped: 0,
            lost: 0,
        }
    }
    }

    /// The place of the `i`th queued event, counting from the oldest.
    fn at(&self, i: usize) -> usize {
        (self.head + i) % Self::CAP
    }

    fn get(&self, p: usize) -> Option<Event> {
        match p.checked_sub(EVENT_BASE) {
            None => self.base.get(p).copied().flatten(),
            Some(q) => self.rows.get(q.checked_div(K)?)?.get(q % K).copied().flatten(),
        }
    }

    fn cell(&mut self, p: usize) -> Option<&mut Option<Event>> {
        match p.checked_sub(EVENT_BASE) {
            None => self.base.get_mut(p),
            Some(q) => self.rows.get_mut(q.checked_div(K)?)?.get_mut(q % K),
        }
    }

    /// Whether the queued events that cannot be recovered leave less than the headroom.
    pub(crate) const fn stalled(&self) -> bool {
        self.len - self.lossy_len + event_headroom(K) > Self::CAP
    }

    pub(crate) fn push(&mut self, ev: Event) {
        if self.len == Self::CAP {
            self.dropped += 1;
            if ev.lossy() {
                return;
            }
            let victim = (0..self.len).find(|i| self.get(self.at(*i)).is_some_and(|e| e.lossy()));
            self.lost += u64::from(victim.is_none());
            let victim = victim.unwrap_or(0);
            if self.get(self.at(victim)).is_some_and(|e| e.lossy()) {
                self.lossy_len -= 1;
            }
            for i in (0..victim).rev() {
                let (from, to) = (self.at(i), self.at(i + 1));
                let moved = self.get(from);
                if let Some(s) = self.cell(to) {
                    *s = moved;
                }
            }
            self.head = (self.head + 1) % Self::CAP;
            self.len -= 1;
        }
        let at = self.at(self.len);
        if let Some(s) = self.cell(at) {
            *s = Some(ev);
            self.len += 1;
            self.lossy_len += usize::from(ev.lossy());
        }
    }

    pub(crate) fn pop(&mut self) -> Option<Event> {
        if self.len == 0 {
            return None;
        }
        let head = self.head;
        let e = self.cell(head).and_then(Option::take);
        self.head = (self.head + 1) % Self::CAP;
        self.len -= 1;
        self.lossy_len -= usize::from(e.is_some_and(|e| e.lossy()));
        e
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unwrap_used)]

    use std::vec::Vec;

    use proptest::prelude::*;
    use vinc_crypto::{IdentityAlg, NodeId};
    use vinc_security::Alpn;

    use super::*;

    const K_T: usize = 256;
    use crate::api::{ConnectFailure, EndReason, SessionId};

    fn event(kind: u8, n: u64) -> Event {
        let session = SessionId::new(n as usize % 9, 1);
        let node = NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [n as u8; 32],
        };
        let alpn = Alpn::new(b"vinc/a").unwrap();
        match kind {
            0 => Event::Connected {
                session,
                node,
                alpn,
                resumed: n.is_multiple_of(2),
            },
            1 => Event::Incoming { session, node, alpn },
            2 => Event::ConnectFailed {
                node,
                alpn,
                reason: ConnectFailure::Timeout,
            },
            3 => Event::Closed {
                session,
                reason: EndReason::Orphaned,
            },
            4 => Event::StreamOpened { session, stream: n },
            5 => Event::StreamReset {
                session,
                stream: n,
                error: n,
            },
            6 => Event::DatagramReceived { session },
            7 => Event::KeyRequest { session },
            8 => Event::AcpCheck { check: n, node, alpn },
            9 => Event::StreamReadable { session, stream: n },
            _ => Event::StreamWritable { session, stream: n },
        }
    }

    #[derive(Debug, Clone)]
    enum Op {
        /// One input (a datagram, a timer round) that emits this many events of these kinds.
        Input(Vec<u8>),
        Poll(u8),
    }

    fn ops() -> impl Strategy<Value = Vec<Op>> {
        prop::collection::vec(
            prop_oneof![
                4 => prop::collection::vec(0..11u8, 1..event_headroom(K_T)).prop_map(Op::Input),
                1 => (1..40u8).prop_map(Op::Poll),
            ],
            0..120,
        )
    }

    proptest! {
        #[test]
        fn nothing_that_cannot_be_recovered_is_dropped_while_the_endpoint_honours_the_stall(ops in ops()) {
            let mut ring: EventRing<K_T> = EventRing::new();
            let (mut offered, mut delivered) = (Vec::new(), Vec::new());
            let mut n = 0u64;
            for op in ops {
                match op {
                    Op::Input(kinds) => {
                        if ring.stalled() {
                            continue;
                        }
                        for k in kinds {
                            n += 1;
                            let ev = event(k, n);
                            if !ev.lossy() {
                                offered.push(ev);
                            }
                            ring.push(ev);
                        }
                    }
                    Op::Poll(k) => {
                        for _ in 0..k {
                            if let Some(e) = ring.pop() && !e.lossy() {
                                delivered.push(e);
                            }
                        }
                    }
                }
            }
            while let Some(e) = ring.pop() {
                if !e.lossy() {
                    delivered.push(e);
                }
            }
            prop_assert_eq!(delivered, offered, "an event that cannot be recovered was lost or reordered");
        }
    }

    #[test]
    fn the_stall_leaves_headroom_and_ignores_events_that_can_be_recovered() {
        let mut ring: EventRing<K_T> = EventRing::new();
        for n in 0..event_queue(K_T) as u64 {
            ring.push(event(9, n));
        }
        assert!(!ring.stalled(), "recoverable events alone never stall the endpoint");
        for n in 0..(event_queue(K_T) - event_headroom(K_T)) as u64 {
            assert!(!ring.stalled());
            ring.push(event(0, n));
        }
        assert!(!ring.stalled(), "exactly the headroom is left");
        ring.push(event(0, 0));
        assert!(ring.stalled());
    }
}
