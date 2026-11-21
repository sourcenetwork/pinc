//! Application streams for the rust-libp2p adapter: a network behaviour and a connection handler that open every
//! requested outbound stream at once.
//!
//! The `libp2p-stream` crate negotiates one outbound stream per connection at a time, so a path with a round trip
//! of 20 ms opens 50 streams a second however many requests are in flight. That is a property of that helper, not of
//! rust-libp2p's transport, so this adapter carries its own: the handler puts every requested open into negotiation
//! without waiting for an earlier one, and each negotiation carries the channel of the open it answers. A control is
//! cloneable and opens streams (`open_stream`) or accepts the inbound streams of one protocol (`accept`).
//!
//! Invariants: at most [`MAX_OPENING`] opens negotiate on one connection (an open beyond that fails at once), and the
//! queue of inbound streams of a protocol holds a bounded number of them (a stream beyond that is dropped).

use std::collections::HashMap;
use std::convert::Infallible;
use std::io;
use std::pin::Pin;
use std::sync::{Arc, Mutex, MutexGuard};
use std::task::{Context, Poll};

use futures::channel::{mpsc, oneshot};
use futures::{SinkExt, StreamExt};
use libp2p::PeerId;
use libp2p::core::upgrade::{InboundUpgrade, OutboundUpgrade, UpgradeInfo};
use libp2p::core::{Endpoint, Multiaddr, transport::PortUse};
use libp2p::swarm::behaviour::{ConnectionClosed, ConnectionEstablished};
use libp2p::swarm::dial_opts::{DialOpts, PeerCondition};
use libp2p::swarm::handler::{ConnectionEvent, DialUpgradeError, FullyNegotiatedInbound, FullyNegotiatedOutbound};
use libp2p::swarm::{
    ConnectionDenied, ConnectionHandler, ConnectionHandlerEvent, ConnectionId, DialError, DialFailure, FromSwarm,
    NetworkBehaviour, Stream, StreamProtocol, StreamUpgradeError, SubstreamProtocol, THandler, THandlerInEvent,
    THandlerOutEvent, ToSwarm,
};

/// The most outbound opens negotiating at once on one connection; the request test keeps at most 256 in flight.
pub const MAX_OPENING: usize = 1024;

/// The inbound streams of a protocol that may wait for the application to accept them.
const INBOUND_QUEUE: usize = 1024;

type Opened = oneshot::Sender<io::Result<Stream>>;

/// A request to a connection's handler to open one outbound stream.
struct NewStream {
    protocol: StreamProtocol,
    opened: Opened,
}

/// The state a [`Control`], the behaviour and the handlers share.
struct Shared {
    inbound: HashMap<StreamProtocol, mpsc::Sender<(PeerId, Stream)>>,
    connections: HashMap<ConnectionId, PeerId>,
    senders: HashMap<ConnectionId, mpsc::Sender<NewStream>>,
    /// The channel of a peer being dialed, which the first connection to it takes over.
    pending: HashMap<PeerId, (mpsc::Sender<NewStream>, mpsc::Receiver<NewStream>)>,
    dial: mpsc::Sender<PeerId>,
}

fn lock(shared: &Mutex<Shared>) -> MutexGuard<'_, Shared> {
    shared.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
}

impl Shared {
    fn protocols(&mut self) -> Vec<StreamProtocol> {
        self.inbound.retain(|_, tx| !tx.is_closed());
        self.inbound.keys().cloned().collect()
    }

    fn on_inbound(&mut self, peer: PeerId, stream: Stream, protocol: &StreamProtocol) {
        // A full or closed queue drops the stream, which resets it for the dialer.
        if let Some(tx) = self.inbound.get_mut(protocol)
            && tx.try_send((peer, stream)).is_err_and(|e| e.is_disconnected())
        {
            self.inbound.remove(protocol);
        }
    }

    fn on_dial_failure(&mut self, peer: PeerId, reason: &str) {
        let Some((_, mut rx)) = self.pending.remove(&peer) else {
            return;
        };
        while let Ok(new) = rx.try_recv() {
            let _ = new
                .opened
                .send(Err(io::Error::new(io::ErrorKind::NotConnected, reason.to_owned())));
        }
    }

    /// The channel to a connection of the peer, dialing it when there is none.
    fn sender(&mut self, peer: PeerId) -> mpsc::Sender<NewStream> {
        let existing = self
            .connections
            .iter()
            .find(|(_, p)| **p == peer)
            .and_then(|(c, _)| self.senders.get(c));
        if let Some(tx) = existing {
            return tx.clone();
        }
        let (tx, _) = self.pending.entry(peer).or_insert_with(|| mpsc::channel(0));
        let tx = tx.clone();
        let _ = self.dial.try_send(peer);
        tx
    }

    fn receiver(&mut self, peer: PeerId, connection: ConnectionId) -> mpsc::Receiver<NewStream> {
        let (tx, rx) = self.pending.remove(&peer).unwrap_or_else(|| mpsc::channel(0));
        self.senders.insert(connection, tx);
        rx
    }
}

/// The network behaviour: it hands every connection a handler and dials a peer a control asks to open a stream to.
pub struct Behaviour {
    shared: Arc<Mutex<Shared>>,
    dial: mpsc::Receiver<PeerId>,
}

impl Default for Behaviour {
    fn default() -> Self {
        Self::new()
    }
}

impl Behaviour {
    /// A behaviour with no protocol accepted yet.
    pub fn new() -> Self {
        let (dial_tx, dial) = mpsc::channel(0);
        let shared = Shared {
            inbound: HashMap::new(),
            connections: HashMap::new(),
            senders: HashMap::new(),
            pending: HashMap::new(),
            dial: dial_tx,
        };
        Self {
            shared: Arc::new(Mutex::new(shared)),
            dial,
        }
    }

    /// A new control of this behaviour.
    pub fn new_control(&self) -> Control {
        Control {
            shared: self.shared.clone(),
        }
    }

    fn handler(&self, peer: PeerId, connection: ConnectionId) -> Handler {
        Handler {
            peer,
            shared: self.shared.clone(),
            receiver: lock(&self.shared).receiver(peer, connection),
            opening: 0,
        }
    }
}

impl NetworkBehaviour for Behaviour {
    type ConnectionHandler = Handler;
    type ToSwarm = ();

    fn handle_established_inbound_connection(
        &mut self,
        connection: ConnectionId,
        peer: PeerId,
        _: &Multiaddr,
        _: &Multiaddr,
    ) -> Result<THandler<Self>, ConnectionDenied> {
        Ok(self.handler(peer, connection))
    }

    fn handle_established_outbound_connection(
        &mut self,
        connection: ConnectionId,
        peer: PeerId,
        _: &Multiaddr,
        _: Endpoint,
        _: PortUse,
    ) -> Result<THandler<Self>, ConnectionDenied> {
        Ok(self.handler(peer, connection))
    }

    fn on_swarm_event(&mut self, event: FromSwarm) {
        match event {
            FromSwarm::ConnectionEstablished(ConnectionEstablished {
                peer_id, connection_id, ..
            }) => {
                lock(&self.shared).connections.insert(connection_id, peer_id);
            }
            FromSwarm::ConnectionClosed(ConnectionClosed { connection_id, .. }) => {
                let mut shared = lock(&self.shared);
                shared.connections.remove(&connection_id);
                shared.senders.remove(&connection_id);
            }
            FromSwarm::DialFailure(DialFailure {
                peer_id: Some(peer),
                error:
                    error @ (DialError::Transport(_)
                    | DialError::Denied { .. }
                    | DialError::NoAddresses
                    | DialError::WrongPeerId { .. }),
                ..
            }) => lock(&self.shared).on_dial_failure(peer, &error.to_string()),
            _ => {}
        }
    }

    fn on_connection_handler_event(&mut self, _: PeerId, _: ConnectionId, event: THandlerOutEvent<Self>) {
        match event {}
    }

    fn poll(&mut self, cx: &mut Context<'_>) -> Poll<ToSwarm<(), THandlerInEvent<Self>>> {
        match self.dial.poll_next_unpin(cx) {
            Poll::Ready(Some(peer)) => Poll::Ready(ToSwarm::Dial {
                opts: DialOpts::peer_id(peer)
                    .condition(PeerCondition::DisconnectedAndNotDialing)
                    .build(),
            }),
            _ => Poll::Pending,
        }
    }
}

/// The connection handler: it puts each requested open into negotiation as soon as it is requested.
pub struct Handler {
    peer: PeerId,
    shared: Arc<Mutex<Shared>>,
    receiver: mpsc::Receiver<NewStream>,
    /// Opens in negotiation: requested, and neither negotiated nor failed yet.
    opening: usize,
}

impl ConnectionHandler for Handler {
    type FromBehaviour = Infallible;
    type ToBehaviour = Infallible;
    type InboundProtocol = Upgrade;
    type OutboundProtocol = Upgrade;
    type InboundOpenInfo = ();
    // The channel of the open a negotiation answers, so each outcome reaches its own open whatever the order.
    type OutboundOpenInfo = Opened;

    fn listen_protocol(&self) -> SubstreamProtocol<Upgrade> {
        SubstreamProtocol::new(Upgrade(lock(&self.shared).protocols()), ())
    }

    fn poll(&mut self, cx: &mut Context<'_>) -> Poll<ConnectionHandlerEvent<Upgrade, Opened, Infallible>> {
        while let Poll::Ready(Some(new)) = self.receiver.poll_next_unpin(cx) {
            if self.opening >= MAX_OPENING {
                let _ = new
                    .opened
                    .send(Err(io::Error::other("too many streams are opening on this connection")));
                continue;
            }
            self.opening += 1;
            return Poll::Ready(ConnectionHandlerEvent::OutboundSubstreamRequest {
                protocol: SubstreamProtocol::new(Upgrade(vec![new.protocol]), new.opened),
            });
        }
        Poll::Pending
    }

    fn on_behaviour_event(&mut self, event: Infallible) {
        match event {}
    }

    fn on_connection_event(&mut self, event: ConnectionEvent<Upgrade, Upgrade, (), Opened>) {
        match event {
            ConnectionEvent::FullyNegotiatedInbound(FullyNegotiatedInbound {
                protocol: (stream, protocol),
                ..
            }) => {
                lock(&self.shared).on_inbound(self.peer, stream, &protocol);
            }
            ConnectionEvent::FullyNegotiatedOutbound(FullyNegotiatedOutbound {
                protocol: (stream, _),
                info,
            }) => {
                self.opening = self.opening.saturating_sub(1);
                let _ = info.send(Ok(stream));
            }
            ConnectionEvent::DialUpgradeError(DialUpgradeError { error, info }) => {
                self.opening = self.opening.saturating_sub(1);
                let _ = info.send(Err(match error {
                    StreamUpgradeError::Timeout => io::Error::from(io::ErrorKind::TimedOut),
                    StreamUpgradeError::Apply(never) => match never {},
                    StreamUpgradeError::NegotiationFailed => {
                        io::Error::new(io::ErrorKind::Unsupported, "the peer does not support the protocol")
                    }
                    StreamUpgradeError::Io(e) => e,
                }));
            }
            _ => {}
        }
    }
}

/// The protocols a stream may negotiate; a negotiated stream comes out as it is.
pub struct Upgrade(Vec<StreamProtocol>);

impl UpgradeInfo for Upgrade {
    type Info = StreamProtocol;
    type InfoIter = std::vec::IntoIter<StreamProtocol>;

    fn protocol_info(&self) -> Self::InfoIter {
        self.0.clone().into_iter()
    }
}

impl InboundUpgrade<Stream> for Upgrade {
    type Output = (Stream, StreamProtocol);
    type Error = Infallible;
    type Future = std::future::Ready<Result<Self::Output, Infallible>>;

    fn upgrade_inbound(self, stream: Stream, protocol: StreamProtocol) -> Self::Future {
        std::future::ready(Ok((stream, protocol)))
    }
}

impl OutboundUpgrade<Stream> for Upgrade {
    type Output = (Stream, StreamProtocol);
    type Error = Infallible;
    type Future = std::future::Ready<Result<Self::Output, Infallible>>;

    fn upgrade_outbound(self, stream: Stream, protocol: StreamProtocol) -> Self::Future {
        std::future::ready(Ok((stream, protocol)))
    }
}

/// A cloneable handle for opening streams and accepting the inbound streams of a protocol.
#[derive(Clone)]
pub struct Control {
    shared: Arc<Mutex<Shared>>,
}

impl Control {
    /// Open a stream of `protocol` to `peer`, dialing it when there is no connection. Any number of opens may be
    /// pending at once; each is negotiated as soon as it is requested.
    pub async fn open_stream(&mut self, peer: PeerId, protocol: StreamProtocol) -> io::Result<Stream> {
        let (opened, answer) = oneshot::channel();
        let mut tx = lock(&self.shared).sender(peer);
        tx.send(NewStream { protocol, opened })
            .await
            .map_err(|e| io::Error::new(io::ErrorKind::ConnectionReset, e))?;
        answer
            .await
            .map_err(|e| io::Error::new(io::ErrorKind::ConnectionReset, e))?
    }

    /// Accept the inbound streams of `protocol`; drop the result to stop.
    pub fn accept(&mut self, protocol: StreamProtocol) -> io::Result<IncomingStreams> {
        let mut shared = lock(&self.shared);
        shared.inbound.retain(|_, tx| !tx.is_closed());
        if shared.inbound.contains_key(&protocol) {
            return Err(io::Error::new(
                io::ErrorKind::AlreadyExists,
                "the protocol is already accepted",
            ));
        }
        let (tx, rx) = mpsc::channel(INBOUND_QUEUE);
        shared.inbound.insert(protocol, tx);
        Ok(IncomingStreams(rx))
    }
}

/// The inbound streams of one protocol, with the peer each came from.
#[must_use = "streams are dropped unless polled"]
pub struct IncomingStreams(mpsc::Receiver<(PeerId, Stream)>);

impl futures::Stream for IncomingStreams {
    type Item = (PeerId, Stream);

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        self.0.poll_next_unpin(cx)
    }
}
