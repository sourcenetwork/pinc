//! Subscribers a hub has not caught up yet: a place in the topic's log in place of a queue of copies.
//!
//! A hub stores every message in the topic's log and pushes it to each subscriber at once. A subscriber whose stream
//! has no room for the push (a burst faster than its path) is not sent a copy to hold, and the message is not
//! dropped: the hub notes the sequence number of that message as the subscriber's place and pushes it nothing more.
//! When the host says the stream has room again ([`Topics::peer_writable`]) the hub sends the logged messages from
//! that place, in order, until the stream is full again or the subscriber has everything, and then pushes live
//! again.
//!
//! The log must not evict what a subscriber is still owed, or a message the publisher heard acknowledged is lost.
//! So a store that would evict an owed message is refused ([`Topics::room_to_store`]): the hub does not acknowledge
//! it and the publisher retries it. One subscriber must not pace the topic for ever, so a subscriber whose stream took
//! nothing for [`PUSH_STALL_MS`], or that is owed a message older than [`PUSH_OWED_MAX`], is let go: it is held, no
//! longer counts for the refusal, and keeps being served from the log. If the log evicted anything it was owed, it is
//! told with RESTORED once it has caught up, as a member whose held subscription comes back is. The notice is owed
//! like a message: a stream with no room for it keeps the place until it has. A subscriber whose session ends while it
//! is behind loses its place, and the topic keeps the span (`Topic::forgot`), so it is told when it subscribes again
//! from a time that does not reach back to what it was owed.
//!
//! A subscriber is put behind the same way when a repair it asked for (a GET, or the replay of a SUB) does not fit
//! its stream (`gap.rs`): it is let go from the start, so a repair never paces the topic.
//!
//! What it costs is one small record for each subscriber that is behind in a topic.
//!
//! Invariants: a subscriber is in a topic's `behind` only while it is a live subscriber of that topic; it is sent the
//! logged messages in log order, each at most once from here, and none it published itself; the log evicts no
//! message owed to a subscriber that is behind and not held; a subscriber that skipped evicted messages is told, on
//! this session or when it subscribes on its next.

use pinc_membership::{Nanos, NodeId};

use crate::consts::{PUSH_OWED_MAX, PUSH_STALL_MS};
use crate::host::{Event, Host, Lane};
use crate::log::HubLog;
use crate::node::Topics;
use crate::wire::{self, Head, ty};

/// A hub's place in a topic's log for one subscriber that is behind.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Behind {
    /// The sequence number of the first logged message it has not been sent.
    pub(crate) next: u64,
    /// When its stream last took a message from here, or it fell behind (the hub's wall clock, milliseconds).
    pub(crate) progress_ms: u64,
    /// Let go: it no longer holds back the log, which may evict what it is owed.
    pub(crate) held: bool,
    /// The log evicted a message it was owed: it is told with RESTORED once caught up.
    pub(crate) lost: bool,
}

/// What became of a subscriber's place after a turn.
enum Place {
    /// The stream is full again: go on from here at the next call.
    Keep,
    /// Everything logged was sent.
    Caught,
    /// The session is gone; its next subscribe repairs the rest.
    Gone,
}

impl Topics {
    /// The streams of `peers` had no room for the message just logged in `topic`: each continues from it later.
    pub(crate) fn fall_behind(&mut self, topic: &[u8], peers: &[NodeId], wall_ms: u64) {
        let Some(st) = self.topics.get_mut(topic) else { return };
        let Some(last) = st.log.as_ref().and_then(|l| l.end().checked_sub(1)) else {
            return;
        };
        for p in peers {
            st.behind.insert(
                *p,
                Behind {
                    next: last,
                    progress_ms: wall_ms,
                    held: false,
                    lost: false,
                },
            );
            self.lagging.insert(*p);
        }
    }

    /// Whether `log` may take a message of `n` bytes: it may unless that evicts a message still owed to a subscriber
    /// that is behind and not held. A subscriber that stalled or is owed too old a message is let go first.
    pub(crate) fn room_to_store(
        behind: &mut alloc::collections::BTreeMap<NodeId, Behind>,
        log: &HubLog,
        n: usize,
        now: Nanos,
        wall_ms: u64,
    ) -> bool {
        let first_kept = log.base() + u64::try_from(log.evicts(n)).unwrap_or(u64::MAX);
        let blocks = |b: &Behind| !b.held && b.next < first_kept;
        if !behind.values().any(blocks) {
            return true;
        }
        for b in behind.values_mut() {
            let stalled = wall_ms.saturating_sub(b.progress_ms) > PUSH_STALL_MS;
            let old = log
                .logged_at(b.next)
                .is_none_or(|at| now.saturating_sub(at) > PUSH_OWED_MAX);
            if blocks(&*b) && (stalled || old) {
                b.held = true;
            }
        }
        !behind.values().any(blocks)
    }

    /// The stream of `peer` has room again. A publisher hands its hub the publishes that waited for room, oldest first;
    /// a hub sends the subscriber the logged messages it is behind on, in order, in every topic; each until the stream
    /// is full again; a hub sends a recipient whose stream refused a subscriber list the whole list. The host calls
    /// this whenever a stream it reported as [`backlogged`](Host::backlogged) took more bytes; calling it at any other
    /// time is harmless.
    pub fn peer_writable<H: Host>(&mut self, h: &mut H, now: Nanos, peer: &NodeId) {
        self.send_unsent(h, now, peer);
        self.subs_writable(h, peer);
        if !self.lagging.contains(peer) {
            return;
        }
        let wall = h.wall_ms();
        let (mut still, mut advanced) = (false, false);
        for (topic, st) in &mut self.topics {
            let Some(mut b) = st.behind.get(peer).copied() else {
                continue;
            };
            let from = b.next;
            let place = loop {
                let Some(log) = st.log.as_ref() else { break Place::Gone };
                // Messages that left the log are missed: go on from the oldest one still here, and tell the subscriber.
                if b.next < log.base() {
                    b.lost = true;
                    b.next = log.base();
                }
                let Some(l) = log.at(b.next) else { break Place::Caught };
                if let Ok((head, _)) = Head::parse(l)
                    && head.origin != peer
                    && crate::reach::reaches(&self.reach, head.origin, peer)
                    && wire::build(&mut self.scratch, ty::MSG, topic, &[l]).is_ok()
                {
                    if !h.send(peer, Lane::Reply, &self.scratch) {
                        break if h.backlogged(peer, self.scratch.len()) {
                            Place::Keep
                        } else {
                            Place::Gone
                        };
                    }
                    self.sent.note(peer, head.ts, head.origin);
                }
                b.next += 1;
            };
            if b.next > from {
                b.progress_ms = wall;
                advanced = true;
            }
            match place {
                Place::Keep => {
                    st.behind.insert(*peer, b);
                    still = true;
                }
                Place::Caught => {
                    if !b.lost
                        || wire::build(&mut self.scratch, ty::RESTORED, topic, &[]).is_err()
                        || h.send(peer, Lane::Reply, &self.scratch)
                    {
                        st.behind.remove(peer);
                    } else if h.backlogged(peer, self.scratch.len()) {
                        // The notice is owed like a message: it waits for room, at the end of the log.
                        st.behind.insert(*peer, b);
                        still = true;
                    } else {
                        st.forget_place(peer, wall);
                    }
                }
                Place::Gone => st.forget_place(peer, wall),
            }
        }
        if !still {
            self.lagging.remove(peer);
        }
        if advanced {
            self.tell_room(h);
        }
    }

    /// A hub whose own publish found no room in a log is told to publish again, once for each refusal.
    pub(crate) fn tell_room<H: Host>(&mut self, h: &mut H) {
        if self.room_at.take().is_some() {
            h.event(Event::PublishRoom);
        }
    }

    /// The subscribers of `topic` this hub is serving from the log because their stream had no room, for tests and
    /// counters.
    pub fn behind_count(&self, topic: &[u8]) -> usize {
        self.topics.get(topic).map_or(0, |st| st.behind.len())
    }
}
