//! Timers: publish retries, the expiry of the dedupe sets and the logs, the hub-to-hub id exchange, the periodic gap
//! check, the end of the floor gathering, and telling a hub whose own publish found no room to publish again.
//!
//! The host asks [`Topics::poll_timeout`] for the next deadline and calls [`Topics::on_timer`] when it passes (or
//! sooner; every call is safe at any time). Deadlines are exact: a retry is due [`PUB_RETRY`] after the previous
//! one, a publish is given up the instant it is older than [`PUB_GIVEUP`], an id leaves the dedupe set the instant
//! it is older than [`SEEN_TTL`], a message leaves a log the instant it is older than [`LOG_WINDOW`].
//!
//! Invariants: nothing here depends on how often the host calls, only on the time it passes.

use alloc::vec::Vec;
use vinc_membership::Nanos;

use crate::consts::FLOOR_WAIT;
use crate::event::Reject;
use crate::host::Host;
use crate::node::Topics;

impl Topics {
    /// When the host should next call [`Topics::on_timer`], if anything is waiting.
    pub fn poll_timeout(&self) -> Option<Nanos> {
        let mut at = self.pending_deadline();
        let mut soon = |t: Nanos| at = Some(at.map_or(t, |a| a.min(t)));
        for st in self.topics.values() {
            if let Some(t) = st.seen.next_expiry() {
                soon(t);
            }
            if let Some(log) = &st.log {
                if let Some(t) = log.next_expiry() {
                    soon(t);
                }
                if self.is_hub && log.len() > 0 {
                    soon(self.next_ae);
                }
            }
            if !self.is_hub && st.sub {
                soon(self.next_gap);
            }
        }
        if self.gather.gathering() {
            soon(self.born.saturating_add(FLOOR_WAIT).saturating_add(1));
        }
        if let Some(t) = self.room_at {
            soon(t);
        }
        if let Some(t) = self.reach_deadline() {
            soon(t);
        }
        at
    }

    /// Run whatever is due at `now`.
    pub fn on_timer<H: Host>(&mut self, h: &mut H, now: Nanos) {
        self.pub_retry(h, now);
        self.sweep(now);
        self.hub_ae(h, now);
        self.gap_ae(h, now);
        if self.gather.gathering() {
            self.floor_check(h, now);
        }
        if self.room_at.is_some_and(|t| now >= t) {
            self.tell_room(h);
        }
        self.reach_timer(h, now);
    }

    /// Expire the dedupe sets and the logs; a message leaving a log stays in the dedupe set, so a late copy is not
    /// delivered again.
    fn sweep(&mut self, now: Nanos) {
        // Ids the set could not take back (the probe bound), counted below; unallocated in the usual case.
        let mut lost: Vec<u64> = Vec::new();
        for st in self.topics.values_mut() {
            st.seen.expire(now);
            let seen = &mut st.seen;
            if let Some(log) = st.log.as_mut() {
                log.expire(now, |old| {
                    if !seen.contains(old, now) && seen.insert(old, now, true).is_err() {
                        lost.push(old);
                    }
                });
            }
        }
        for old in lost {
            self.note_reject(old.to_le_bytes(), Reject::ProbeLimit);
        }
    }
}
