//! The simulator node that mixes clients and relays, and helpers to place them in a topology.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::missing_panics_doc,
    clippy::must_use_candidate
)]

use std::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_sim::{IfaceEvent, Node, NodeId as SimNode, Sim, StreamEvent, StreamId, StreamKind, StreamOp, Time, Transmit};

use crate::connect_client::{Client, ClientSpec, Cmd, RelaySpec};
use crate::connect_host::Ev;
use crate::connect_relay_node::RelayNode;

pub enum CNode {
    Client(Box<Client>),
    Relay(Box<RelayNode>),
}

impl CNode {
    pub fn client(&self) -> &Client {
        match self {
            Self::Client(c) => c,
            Self::Relay(_) => panic!("not a client"),
        }
    }

    pub fn client_mut(&mut self) -> &mut Client {
        match self {
            Self::Client(c) => c,
            Self::Relay(_) => panic!("not a client"),
        }
    }

    pub fn relay(&self) -> &RelayNode {
        match self {
            Self::Relay(r) => r,
            Self::Client(_) => panic!("not a relay"),
        }
    }

    pub fn relay_mut(&mut self) -> &mut RelayNode {
        match self {
            Self::Relay(r) => r,
            Self::Client(_) => panic!("not a relay"),
        }
    }
}

macro_rules! each {
    ($self:ident, $n:ident => $e:expr) => {
        match $self {
            CNode::Client($n) => $e,
            CNode::Relay($n) => $e,
        }
    };
}

impl Node for CNode {
    type Cmd = Cmd;
    type Event = Ev;

    fn handle_datagram(&mut self, now: Time, local: SocketAddr, remote: SocketAddr, data: &mut [u8]) {
        each!(self, n => n.handle_datagram(now, local, remote, data));
    }

    fn poll_transmit(&mut self, _now: Time, buf: &mut [u8]) -> Option<Transmit> {
        each!(self, n => n.poll_transmit(buf))
    }

    fn poll_timeout(&mut self) -> Option<Time> {
        each!(self, n => n.poll_timeout())
    }

    fn handle_timeout(&mut self, now: Time) {
        each!(self, n => n.handle_timeout(now));
    }

    fn command(&mut self, now: Time, cmd: Cmd) {
        match self {
            Self::Client(c) => c.cmd(now, cmd),
            Self::Relay(_) => panic!("a relay takes no command"),
        }
    }

    fn poll_event(&mut self) -> Option<Ev> {
        each!(self, n => n.events.pop_front())
    }

    fn crash(&mut self, _now: Time) -> Vec<u8> {
        Vec::new()
    }

    fn restart(&mut self, _now: Time, _persisted: &[u8]) {}

    fn suspend(&mut self, _now: Time) {}

    fn resume(&mut self, now: Time) {
        if let Self::Client(c) = self {
            c.resume(now);
        }
    }

    fn iface_event(&mut self, now: Time, event: IfaceEvent) {
        if let Self::Client(c) = self {
            c.iface_event(now, event);
        }
    }

    fn poll_stream(&mut self, _now: Time, buf: &mut [u8]) -> Option<StreamOp> {
        each!(self, n => n.poll_stream(buf))
    }

    fn handle_stream_event(&mut self, now: Time, event: StreamEvent) {
        each!(self, n => n.handle_stream_event(now, event));
    }

    fn handle_stream_record(&mut self, now: Time, stream: StreamId, data: &mut [u8]) {
        each!(self, n => n.handle_stream_record(now, stream, data));
    }
}

pub const fn ip4(a: u8, b: u8, c: u8, d: u8) -> IpAddr {
    IpAddr::V4(Ipv4Addr::new(a, b, c, d))
}

/// A relay at `ip` serving UDP on 4433, TCP on 443 and WebSocket on 8443. Returns the node and how clients reach it.
pub fn add_relay(sim: &mut Sim<CNode>, tag: u8, ip: IpAddr) -> (SimNode, RelaySpec) {
    let udp = SocketAddr::new(ip, 4433);
    let node = RelayNode::new(tag, udp, 0);
    let id = node.id();
    let n = sim.add_node_at(CNode::Relay(Box::new(node)), ip);
    let tcp = SocketAddr::new(ip, 443);
    let ws = SocketAddr::new(ip, 8443);
    sim.listen(n, tcp, StreamKind::Tcp);
    sim.listen(n, ws, StreamKind::Ws);
    (
        n,
        RelaySpec {
            id,
            udp: Some(udp),
            tcp: Some(tcp),
            ws: Some(ws),
        },
    )
}

/// A client spec with the defaults of the scenarios.
pub fn spec(tag: u8, addr: SocketAddr, relays: &[RelaySpec]) -> ClientSpec {
    ClientSpec {
        tag,
        addr,
        relays: relays.to_vec(),
        phone: false,
        keep_learn: false,
        restarted: false,
        start: 0,
    }
}
