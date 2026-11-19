//! The deterministic trace: every input the machine acts on and every decision it takes, in order.
//!
//! The queue is bounded. When it is full the newest record is dropped and counted, and the count is delivered as
//! [`Trace::Lost`] before the next record, so a consumer never mistakes a gap for silence. Topics appear as a
//! [`Tag`], the first eight bytes of their hash, so a record is `Copy` and fixed-size.

use pinc_membership::NodeId;

/// The first eight bytes of the hash of a topic.
pub type Tag = [u8; 8];

/// The tag of `topic`.
pub fn topic_tag(topic: &[u8]) -> Tag {
    blake3::hash(topic)
        .as_bytes()
        .first_chunk::<8>()
        .copied()
        .unwrap_or([0; 8])
}

/// How a publish was handed on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PublishMode {
    /// Every hub was up: FANP to the primary, FAN to the others.
    Fan,
    /// PUB to the primary.
    Single,
    /// The node is a hub and stored it itself.
    Local,
}

/// Why a message was not accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Reject {
    /// The head or the frame did not parse.
    BadHead,
    /// The signature does not cover this topic, id and body.
    BadSignature,
    /// Already seen or logged.
    Duplicate,
    /// The origin is revoked.
    Revoked,
    /// The dedupe set of the topic is full.
    SeenFull,
    /// The topic table is full.
    TopicsFull,
    /// The log could not take it.
    LogFull,
    /// Older than the replay floor.
    Old,
    /// The messages held for an access answer are at their limit; the message is left unseen so the gap repair
    /// brings it again.
    HeldFull,
    /// A hub holds the id for another message (the print of the signature differs from the stored one, also after
    /// the log let the message go), so the publish is not acknowledged. A copy due no acknowledgement is a
    /// [`Reject::Duplicate`] and is compared with nothing.
    IdTaken,
    /// The frame came from a sender the node does not take that kind of frame from (a publish at a node that is not a
    /// hub, a hub message from a node that is not a boot node). Counted and not traced.
    NotAllowed,
}

/// The position of each [`Reject`] in [`RejectStats`] and the list of them all, from one table: the `match` is
/// exhaustive, so a reason added to the enum does not compile until it has a position here, and the size of the
/// counters follows from the table.
macro_rules! reject_positions {
    ($($pos:literal => $why:ident),+ $(,)?) => {
        impl Reject {
            /// Every reason, in the order [`RejectStats`] counts them.
            pub const ALL: [Self; [$($pos),+].len()] = [$(Self::$why),+];

            const fn position(self) -> usize {
                match self {
                    $(Self::$why => $pos),+
                }
            }
        }
    };
}

reject_positions! {
    0 => BadHead,
    1 => BadSignature,
    2 => Duplicate,
    3 => Revoked,
    4 => SeenFull,
    5 => TopicsFull,
    6 => LogFull,
    7 => Old,
    8 => HeldFull,
    9 => IdTaken,
    10 => NotAllowed,
}

/// How many messages each [`Reject`] reason turned away, and how many long walks the id tables made. Counted whether or
/// not tracing is on ([`Topics::reject_stats`](crate::Topics::reject_stats)).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RejectStats {
    counts: [u64; Reject::ALL.len()],
    long_walks: u64,
}

impl RejectStats {
    /// How many messages were turned away for `why`.
    pub fn count(&self, why: Reject) -> u64 {
        self.counts.get(why.position()).copied().unwrap_or(0)
    }

    /// How many messages were turned away, for any reason.
    pub fn total(&self) -> u64 {
        self.counts.iter().fold(0, |a, n| a.saturating_add(*n))
    }

    /// How many walks in the dedupe sets and the hub logs read 128 slots or more: with ids placed by a secret key it
    /// is rare, so a count that grows says a sender knows the key.
    pub const fn long_walks(&self) -> u64 {
        self.long_walks
    }

    #[cfg(feature = "alloc")]
    pub(crate) fn note(&mut self, why: Reject) {
        if let Some(n) = self.counts.get_mut(why.position()) {
            *n = n.saturating_add(1);
        }
    }

    #[cfg(feature = "alloc")]
    pub(crate) const fn with_long_walks(mut self, n: u64) -> Self {
        self.long_walks = n;
        self
    }
}

/// Why a SUBS frame changed nothing.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubsDrop {
    /// The frame did not parse, or names a kind this node does not take.
    Malformed,
    /// An ASK at a node that is not a hub, or from a node the hub does not tell the list.
    NotRecipient,
    /// A list from a node that is not a hub.
    NotHub,
    /// A change from a hub other than the one the member's list came from; from the member's primary it also makes the
    /// primary the source, and the member asks it for the whole list.
    OtherHub,
    /// A change on a version the member does not hold, or a removal from a list the member cut below its hub's; it
    /// asks for the whole list once.
    OffBase,
    /// A change at or below the version the member holds (from an old session): ignored, the member keeps its version.
    Old,
    /// The topic table is full.
    TopicsFull,
}

/// Why a message waits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HoldWhy {
    /// For the access-control answer on its origin.
    Acp,
    /// For the replay floors of the hubs.
    Floor,
}

/// A trace record.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trace {
    /// A message was published.
    Published {
        /// The topic.
        topic: Tag,
        /// The id.
        mid: [u8; 8],
        /// How it went out.
        mode: PublishMode,
    },
    /// A PUB went to a hub on a retry.
    PubRetry {
        /// The hub.
        hub: NodeId,
        /// The id.
        mid: [u8; 8],
    },
    /// A hub acknowledged a publish.
    PubAcked {
        /// The id.
        mid: [u8; 8],
    },
    /// A publish was given up.
    PubGaveUp {
        /// The id.
        mid: [u8; 8],
    },
    /// A hub logged a message.
    Stored {
        /// The topic.
        topic: Tag,
        /// The id.
        mid: [u8; 8],
        /// It came fanned, so it was not mirrored.
        fanned: bool,
    },
    /// A message was refused.
    Rejected {
        /// The id, zero if the head did not parse.
        mid: [u8; 8],
        /// Why.
        why: Reject,
    },
    /// A message was delivered.
    Delivered {
        /// The topic.
        topic: Tag,
        /// The id.
        mid: [u8; 8],
    },
    /// A message is held.
    Held {
        /// The id.
        mid: [u8; 8],
        /// Why.
        why: HoldWhy,
    },
    /// An access check was asked.
    AcpAsked {
        /// The check.
        id: u32,
    },
    /// An access check was answered.
    AcpAnswered {
        /// The check.
        id: u32,
        /// The verdict.
        allow: bool,
    },
    /// A SUB went to a hub.
    SubSent {
        /// The hub.
        hub: NodeId,
        /// The topic.
        topic: Tag,
        /// The point in time asked for (wall milliseconds).
        since_ms: u64,
        /// `REPLAY_PUSH` was asked.
        replay: bool,
    },
    /// A HAVE went out.
    HaveSent {
        /// The peer.
        peer: NodeId,
        /// The topic.
        topic: Tag,
        /// How many ids.
        count: u16,
    },
    /// A GET went out.
    GetSent {
        /// The peer.
        peer: NodeId,
        /// The topic.
        topic: Tag,
        /// How many ids.
        count: u16,
    },
    /// A requested message arrived.
    Repaired {
        /// The topic.
        topic: Tag,
        /// The id.
        mid: [u8; 8],
    },
    /// A hub reported its replay floor.
    FloorReported {
        /// The hub.
        hub: NodeId,
    },
    /// The floor gathering ended.
    FloorDone {
        /// The floors were used (false: the wait ran out).
        used: bool,
    },
    /// A message went straight to a subscriber.
    FallbackSent {
        /// The id.
        mid: [u8; 8],
        /// The subscriber.
        to: NodeId,
    },
    /// A hub kept a member's subscriptions for its lease.
    SubsHeld {
        /// The member.
        member: NodeId,
    },
    /// A hub made a member's held subscriptions live and told it.
    SubsRestored {
        /// The member.
        member: NodeId,
        /// How many topics.
        topics: u16,
    },
    /// A hub could not give a subscriber every message it asked for and told it, or owes it the notice.
    Short {
        /// The subscriber.
        peer: NodeId,
        /// The topic.
        topic: Tag,
    },
    /// A hub forgot a member's subscriptions.
    SubsReleased {
        /// The member.
        member: NodeId,
    },
    /// A member heard that its subscription was restored.
    RestoredSeen {
        /// The hub.
        hub: NodeId,
        /// The topic.
        topic: Tag,
    },
    /// A SUBS frame was dropped.
    SubsDropped {
        /// The sender.
        from: NodeId,
        /// The topic.
        topic: Tag,
        /// Why.
        why: SubsDrop,
    },
    /// The primary hub changed.
    Primary {
        /// The new primary.
        hub: NodeId,
    },
    /// This many trace records were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}

#[cfg(all(test, feature = "alloc"))]
mod tests {
    use super::*;

    #[test]
    #[allow(clippy::indexing_slicing, reason = "the test asserts")]
    fn every_reason_has_its_own_counter() {
        let mut s = RejectStats::default();
        for (i, why) in Reject::ALL.iter().enumerate() {
            for _ in 0..=i {
                s.note(*why);
            }
        }
        for (i, why) in Reject::ALL.iter().enumerate() {
            assert_eq!(s.count(*why), i as u64 + 1, "{why:?}");
        }
        // The positions are a permutation of 0..N: no two reasons share a counter.
        let mut seen = [false; Reject::ALL.len()];
        for why in Reject::ALL {
            assert!(!core::mem::replace(&mut seen[why.position()], true), "{why:?}");
        }
        assert_eq!(s.total(), (1..=Reject::ALL.len() as u64).sum::<u64>());
        assert_eq!(s.with_long_walks(7).long_walks(), 7);
    }
}
