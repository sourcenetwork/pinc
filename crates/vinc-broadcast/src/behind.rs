//! Subscribers a hub has not caught up yet: a place in the topic's log in place of a queue of copies.
//!
//! A hub stores every message in the topic's log and pushes it to each subscriber at once. A subscriber whose stream
//! has no room for the push (a burst faster than its path) is not sent a copy to hold, and the message is not
//! dropped: the hub notes the sequence number of that message as the subscriber's place and pushes it nothing more.
//! When the host says the stream has room again ([`Topics::peer_writable`]) the hub sends the logged messages from
//! that place, in order, until the stream is full again or the subscriber has everything, and then pushes live
//! again.
//!
//! What it costs is one number for each subscriber that is behind in a topic. What still bounds it is the log: a
//! subscriber that falls further behind than the log holds continues from the oldest message the log still has, and
//! learns of the ones before it as any subscriber that was away does, through the gap repair.
//!
//! Invariants: a subscriber is in a topic's `behind` only while it is a live subscriber of that topic; it is sent the
//! logged messages in log order, each at most once from here, and none it published itself; a place never points
//! before the oldest logged message when it is used.

use vinc_membership::NodeId;

use crate::host::{Host, Lane};
use crate::node::Topics;
use crate::wire::{self, Head, ty};

/// What became of a subscriber's place after a turn.
enum Place {
    /// The stream is full again: go on from here at the next call.
    Keep,
    /// Everything logged was sent, or the session is gone and its next subscribe repairs the rest.
    Done,
}

impl Topics {
    /// The streams of `peers` had no room for the message just logged in `topic`: each continues from it later.
    pub(crate) fn fall_behind(&mut self, topic: &[u8], peers: &[NodeId]) {
        let Some(st) = self.topics.get_mut(topic) else { return };
        let Some(last) = st.log.as_ref().and_then(|l| l.end().checked_sub(1)) else {
            return;
        };
        for p in peers {
            st.behind.insert(*p, last);
            self.lagging.insert(*p);
        }
    }

    /// The stream of `peer` has room again. A hub sends the subscriber the logged messages it is behind on, in order,
    /// in every topic, until the stream is full again. The host calls this whenever a stream it reported as
    /// [`backlogged`](Host::backlogged) took more bytes; calling it at any other time is harmless.
    pub fn peer_writable<H: Host>(&mut self, h: &mut H, peer: &NodeId) {
        if !self.lagging.contains(peer) {
            return;
        }
        let mut still = false;
        for (topic, st) in &mut self.topics {
            let Some(mut next) = st.behind.get(peer).copied() else {
                continue;
            };
            let place = loop {
                let Some(log) = st.log.as_ref() else { break Place::Done };
                // Messages that left the log are the gap repair's: go on from the oldest one still here.
                next = next.max(log.base());
                let Some(l) = log.at(next) else { break Place::Done };
                if let Ok((head, _)) = Head::parse(l)
                    && head.origin != peer
                    && wire::build(&mut self.scratch, ty::MSG, topic, &[l]).is_ok()
                {
                    if !h.send(peer, Lane::Reply, &self.scratch) {
                        break if h.backlogged(peer, self.scratch.len()) {
                            Place::Keep
                        } else {
                            Place::Done
                        };
                    }
                    self.sent.note(peer, head.ts, head.origin);
                }
                next += 1;
            };
            match place {
                Place::Keep => {
                    st.behind.insert(*peer, next);
                    still = true;
                }
                Place::Done => {
                    st.behind.remove(peer);
                }
            }
        }
        if !still {
            self.lagging.remove(peer);
        }
    }

    /// The subscribers of `topic` this hub is serving from the log because their stream had no room, for tests and
    /// counters.
    pub fn behind_count(&self, topic: &[u8]) -> usize {
        self.topics.get(topic).map_or(0, |st| st.behind.len())
    }
}
