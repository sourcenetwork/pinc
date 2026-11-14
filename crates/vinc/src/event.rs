//! What an endpoint tells the host about topics: who joined, who left, and the messages.
//!
//! Events queue in a bounded buffer. When it is full the newest is dropped and counted, and the count comes out as
//! [`Event::Lost`] before the next event, so a gap never reads as silence.

use vinc_crypto::NodeId;

/// The id of a published message.
pub type MessageId = [u8; 8];

/// Something that happened on a topic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Event {
    /// A member of the topic this endpoint has a session with appeared.
    NeighborUp {
        /// The topic.
        topic: Vec<u8>,
        /// The neighbour.
        peer: NodeId,
    },
    /// A neighbour left the topic or its last session ended.
    NeighborDown {
        /// The topic.
        topic: Vec<u8>,
        /// The former neighbour.
        peer: NodeId,
    },
    /// A message arrived on a topic this endpoint joined; its signature by `origin` over exactly these bytes verified.
    Message {
        /// The topic.
        topic: Vec<u8>,
        /// Who published it.
        origin: NodeId,
        /// The peer whose session delivered it, as the handshake authenticated it.
        hop: NodeId,
        /// Whether it came straight from the publisher, with no hub between.
        direct: bool,
        /// The bytes published.
        payload: Vec<u8>,
    },
    /// A hub holds this endpoint's subscription to `topic`, the first time since it joined: a message published to the
    /// topic through that hub from now on arrives. A join returns before any hub knows of it.
    Joined {
        /// The topic.
        topic: Vec<u8>,
        /// The hub.
        hub: NodeId,
    },
    /// With [`Builder::connected_topics`](crate::Builder::connected_topics): the hubs were not told every peer this
    /// endpoint holds sessions with, so they reach it from part of its component only. `named` is how many they were
    /// told: the first [`ADJ_MAX`](vinc_broadcast::consts::ADJ_MAX) when there are more, or `None` when the record
    /// could not be signed. The hubs then keep the last record named and the endpoint tries again on the next change of
    /// sessions. A short record can lose an edge both ends hold: two endpoints with more than
    /// [`ADJ_MAX`](vinc_broadcast::consts::ADJ_MAX) peers each may name different subsets, and a hub keeps an edge only
    /// when both name it, so their component may split there.
    AdjacencyShort {
        /// The peers of the endpoint's sessions.
        sessions: u32,
        /// How many of them the hubs were told.
        named: Option<u32>,
    },
    /// On a hub: `node`'s record did not fit its adjacency table's bytes and was refused (see
    /// [`Builder::connected_topics`](crate::Builder::connected_topics)); `node` is alone at this hub until a record of
    /// it fits. See [`Endpoint::reach_stats`](crate::Endpoint::reach_stats).
    ReachRefused {
        /// The endpoint whose record was refused.
        node: NodeId,
    },
    /// On a hub: its adjacency table closed. Until it opens again ([`Event::ReachOpened`]) every endpoint without a
    /// record, connected topics or not, hears only the hubs through this hub.
    ReachClosed,
    /// On a hub: its closed adjacency table opened again: every endpoint it refused has a record, was
    /// revoked or was released.
    ReachOpened,
    /// This many events were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}
