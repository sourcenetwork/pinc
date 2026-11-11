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
    /// This many events were dropped because the queue was full.
    Lost {
        /// How many.
        count: u32,
    },
}
