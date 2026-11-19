//! Adversaries: an on-path observer that records traffic, spoofed floods, replay of captured datagrams, and an inbound
//! tap that captures, replays and corrupts what reaches the nodes.

use std::net::SocketAddr;

use crate::Time;
use crate::ids::NodeId;

/// One datagram an observer saw.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObsRecord {
    /// When it passed the link.
    pub time: Time,
    /// Source address as the link saw it.
    pub src: SocketAddr,
    /// Destination address as the link saw it.
    pub dst: SocketAddr,
    /// Datagram size in bytes.
    pub size: usize,
    /// The first bytes of the datagram (up to the observer's header length).
    pub header: Vec<u8>,
    /// The whole datagram, kept only when the observer was asked to (replay needs it).
    pub payload: Option<Vec<u8>>,
}

/// An observer on one link direction; it records datagrams the link accepted.
#[derive(Clone, Debug)]
pub struct Observer {
    pub(crate) header_len: usize,
    pub(crate) keep_payload: bool,
    /// What it saw, in order.
    pub records: Vec<ObsRecord>,
}

impl Observer {
    pub(crate) const fn new(header_len: usize, keep_payload: bool) -> Self {
        Self {
            header_len,
            keep_payload,
            records: Vec::new(),
        }
    }

    pub(crate) fn record(&mut self, time: Time, src: SocketAddr, dst: SocketAddr, data: &[u8]) {
        let head = data.get(..self.header_len).unwrap_or(data);
        self.records.push(ObsRecord {
            time,
            src,
            dst,
            size: data.len(),
            header: head.to_vec(),
            payload: self.keep_payload.then(|| data.to_vec()),
        });
    }
}

/// What a flood carries.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FloodPayload {
    /// The same bytes every time.
    Fixed(Vec<u8>),
    /// This many random bytes, fresh for every datagram.
    Random(usize),
}

/// A spoofed flood: datagrams at a steady rate with forged source addresses.
#[derive(Clone, Debug)]
pub struct FloodSpec {
    /// First datagram time.
    pub start: Time,
    /// No datagram at or after this time.
    pub end: Time,
    /// Datagrams per second.
    pub rate_pps: u64,
    /// The victim address.
    pub dst: SocketAddr,
    /// Forged source addresses, used round-robin; must not be empty.
    pub spoof: Vec<SocketAddr>,
    /// The datagram contents.
    pub payload: FloodPayload,
}

pub(crate) struct Flood<R> {
    pub(crate) host: u32,
    pub(crate) spec: FloodSpec,
    pub(crate) sent: u64,
    pub(crate) rng: R,
}

pub(crate) struct Replay {
    pub(crate) host: u32,
    pub(crate) obs: u32,
    pub(crate) next: usize,
    pub(crate) end: usize,
    pub(crate) spacing: Time,
}

/// The inbound adversary: it sees every datagram at the moment it reaches a node (after the NAT, the firewall and the
/// middlebox, so it sits inside the access network), may keep a copy of large first flights, and for the victims may
/// replay a datagram later or flip one bit of it. Install it with [`crate::Sim::tap_inbound`].
///
/// Draw order per datagram, from the adversary's own stream: one draw for the capture decision (only when the datagram
/// is eligible and the capture list is not full), then for a victim one draw choosing replay, modify or neither, then
/// for a replay one draw for its delay, for a modification two draws for the byte and the bit.
#[derive(Clone, Debug)]
pub struct TapSpec {
    /// The nodes whose inbound datagrams are replayed or corrupted.
    pub victims: Vec<NodeId>,
    /// Probability that an inbound datagram at a victim is replayed (delivered now and again after 1 ms plus up to 2 s).
    pub replay: f64,
    /// Probability that an inbound datagram at a victim is delivered with one random bit flipped.
    pub modify: f64,
    /// Datagrams of at least this many bytes are eligible for capture.
    pub capture_min: usize,
    /// Probability that an eligible datagram is captured.
    pub capture_prob: f64,
    /// At most this many datagrams are kept.
    pub capture_max: usize,
    /// Capture only datagrams whose first byte has its high bit set (the long-header form of the first flight of a
    /// QUIC-style handshake).
    pub first_flights_only: bool,
}

/// A datagram the inbound adversary kept.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Captured {
    /// The node it reached.
    pub node: NodeId,
    /// Its source as the node saw it.
    pub src: SocketAddr,
    /// Its destination address on the node.
    pub dst: SocketAddr,
    /// The bytes.
    pub data: Vec<u8>,
}

/// What the inbound adversary did.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TapStats {
    /// Datagrams scheduled for replay.
    pub replayed: u64,
    /// Datagrams delivered with a flipped bit.
    pub modified: u64,
}

pub(crate) struct Tap<R> {
    pub(crate) spec: TapSpec,
    pub(crate) rng: R,
    pub(crate) captured: Vec<Captured>,
    pub(crate) stats: TapStats,
}
