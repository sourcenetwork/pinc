//! Adversaries: an on-path observer that records traffic, spoofed floods, and replay of captured datagrams.

use std::net::SocketAddr;

use crate::Time;

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
