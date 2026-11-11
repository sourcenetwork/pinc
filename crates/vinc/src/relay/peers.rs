//! The relay mesh: a protected carrier between every pair of relays that name each other as peers, carrying the relays'
//! own frames (forwarded packets, record replicas, pings) so that a member whose relay is not the relay of the node it
//! looks for is still found and reached.
//!
//! The relay with the lower node id dials the other, over the carrier kind the peer is listed with and with the peer
//! protocol name; the other end tells the carrier from a member's by that name and accepts it only from a node it lists
//! as a peer. An open carrier makes the other relay a peer relay, and its frames go to the machine's peer entry. A
//! carrier that ends, or a dial that fails, is dialed again after [`REDIAL_NS`]. A relay never peers with itself, so the
//! same list can be given to every relay of a mesh.
//!
//! Invariants: at most one carrier per peer is kept (the newest); a peer is removed from the machine when its current
//! carrier ends; a relay dials only a peer with a higher node id and only while it is running.

use core::net::SocketAddr;

use vinc_crypto::NodeId;

use super::store::node_key;
use crate::carrier::CarrierKind;

/// How long a peer relay waits before it is dialed again (the wait the simulator's relay mesh uses).
pub(crate) const REDIAL_NS: u64 = 3_000_000_000;

/// A peer relay: its node id and the carrier addresses it listens on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Peer {
    /// The relay's node id.
    pub id: NodeId,
    /// Its TCP carrier address.
    pub tcp: Option<SocketAddr>,
    /// Its WebSocket carrier address.
    pub ws: Option<SocketAddr>,
    /// The host's WebSocket delivers whole messages, as a browser's does: the kind is
    /// [`CarrierKind::WsMessages`] instead of [`CarrierKind::Ws`].
    pub messages: bool,
}

impl Peer {
    /// A peer with no address: the relay accepts its carrier but never dials it.
    pub const fn new(id: NodeId) -> Self {
        Self {
            id,
            tcp: None,
            ws: None,
            messages: false,
        }
    }

    /// Set the TCP carrier address.
    #[must_use]
    pub const fn with_tcp(mut self, addr: SocketAddr) -> Self {
        self.tcp = Some(addr);
        self
    }

    /// Set the WebSocket carrier address.
    #[must_use]
    pub const fn with_ws(mut self, addr: SocketAddr) -> Self {
        self.ws = Some(addr);
        self
    }

    /// The host's WebSocket delivers whole messages (a browser).
    #[must_use]
    pub const fn with_messages(mut self) -> Self {
        self.messages = true;
        self
    }

    /// The kind to dial: TCP if the peer has a TCP address, else a WebSocket.
    pub(crate) const fn kind(&self) -> Option<CarrierKind> {
        match (self.tcp.is_some(), self.ws.is_some(), self.messages) {
            (true, _, _) => Some(CarrierKind::Tcp),
            (false, true, false) => Some(CarrierKind::Ws),
            (false, true, true) => Some(CarrierKind::WsMessages),
            (false, false, _) => None,
        }
    }
}

/// Whether `me` dials `peer`: the lower node id does.
pub(crate) fn dials(me: &NodeId, peer: &NodeId) -> bool {
    node_key(me) < node_key(peer)
}

/// Where the carrier to a peer stands.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Link {
    /// No carrier; dial at the given time.
    Idle(u64),
    /// The host is opening the stream.
    Opening,
    /// A stream is open (handshaking or up).
    Open,
}

/// A peer and the state of its carrier.
#[derive(Debug, Clone, Copy)]
pub(crate) struct Slot {
    pub(crate) peer: Peer,
    pub(crate) link: Link,
}
