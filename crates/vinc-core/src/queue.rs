//! The bounded queue of events waiting for the host.
//!
//! Invariants: the queue never holds more than `N` events; events leave in the order they entered; every drop is
//! counted. A full queue drops a new event the application can recover by reading state, and for any other new event
//! evicts the oldest recoverable one. An event the application cannot recover is evicted only if the queue holds
//! nothing else, which the endpoint prevents: it stops reading datagrams while [`EventRing::stalled`], that is while
//! fewer than [`EVENT_HEADROOM`] places remain beyond the unrecoverable events queued.

use crate::api::Event;

/// The places kept free of unrecoverable events, enough for what one datagram, one timer round or the release of one
/// session's held events (at most 64) can emit.
pub const EVENT_HEADROOM: usize = 128;

/// A fixed ring of events.
#[derive(Debug)]
pub(crate) struct EventRing<const N: usize> {
    items: [Option<Event>; N],
    head: usize,
    len: usize,
    /// How many of the queued events the application can recover by reading state.
    lossy_len: usize,
    pub(crate) dropped: u64,
}

impl<const N: usize> EventRing<N> {
    pub(crate) const fn new() -> Self {
        Self {
            items: [None; N],
            head: 0,
            len: 0,
            lossy_len: 0,
            dropped: 0,
        }
    }

    fn at(&self, i: usize) -> usize {
        (self.head + i) % N
    }

    /// Whether the queued events that cannot be recovered leave less than [`EVENT_HEADROOM`] places.
    pub(crate) const fn stalled(&self) -> bool {
        self.len - self.lossy_len + EVENT_HEADROOM > N
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
            if self
                .items
                .get(self.at(victim))
                .copied()
                .flatten()
                .is_some_and(|e| e.lossy())
            {
                self.lossy_len -= 1;
            }
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
            self.lossy_len += usize::from(ev.lossy());
        }
    }

    pub(crate) fn pop(&mut self) -> Option<Event> {
        if self.len == 0 {
            return None;
        }
        let e = self.items.get_mut(self.head).and_then(Option::take);
        self.head = (self.head + 1) % N;
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
                4 => prop::collection::vec(0..11u8, 1..EVENT_HEADROOM).prop_map(Op::Input),
                1 => (1..40u8).prop_map(Op::Poll),
            ],
            0..120,
        )
    }

    proptest! {
        #[test]
        fn nothing_that_cannot_be_recovered_is_dropped_while_the_endpoint_honours_the_stall(ops in ops()) {
            let mut ring: EventRing<512> = EventRing::new();
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
        let mut ring: EventRing<512> = EventRing::new();
        for n in 0..512 {
            ring.push(event(9, n));
        }
        assert!(!ring.stalled(), "recoverable events alone never stall the endpoint");
        for n in 0..(512 - EVENT_HEADROOM) as u64 {
            assert!(!ring.stalled());
            ring.push(event(0, n));
        }
        assert!(!ring.stalled(), "exactly the headroom is left");
        ring.push(event(0, 0));
        assert!(ring.stalled());
    }
}
