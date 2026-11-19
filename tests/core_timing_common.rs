//! Shared helpers for the `core_timing*` test targets: the sent-time reader, the handshake message type, and a dial.
//!
//! Included with `#[path]`; not a test target itself.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_precision_loss
)]

use pinc_core::{Event, Role, SessionId};
use pinc_tests::*;
use pinc_transport::packet::LongHeader;
use pinc_wire::Reader;

pub const S: u64 = SEC_NS;

pub fn is_connected(e: &Event) -> bool {
    matches!(e, Event::Connected { .. })
}

/// The sends of node `n` between `from` and `to`, as times in seconds relative to `base`.
pub fn sends(net: &CoreNet, n: usize, base: u64, from: f64, to: f64) -> Vec<f64> {
    net.nodes[n]
        .sent
        .iter()
        .map(|(t, _, _)| (*t as f64 - base as f64) / S as f64)
        .filter(|t| *t >= from && *t < to)
        .collect()
}

/// The handshake message type a datagram carries, if it is the start of one.
pub fn message_type(d: &[u8]) -> Option<u8> {
    let (h, len) = LongHeader::parse(d).ok()?;
    let mut r = Reader::new(d.get(len..len + h.body_len)?);
    r.read_varint().ok()?;
    if r.read_varint().ok()? != 0 {
        return None;
    }
    r.read_u8().ok()
}

/// The handshake message types node `from` sent to node `to` after the first `marker` captured datagrams, in order.
pub fn flights(net: &CoreNet, marker: usize, from: usize, to: usize) -> Vec<u8> {
    let (src, dst) = (net.nodes[from].addr, net.nodes[to].addr);
    net.captured[marker..]
        .iter()
        .filter(|(f, t, d)| *f == src && *t == dst && d[0] & 0x80 != 0)
        .filter_map(|(_, _, d)| message_type(d))
        .collect()
}

pub fn dial(net: &mut CoreNet, a: usize, b: usize, alpn: &[u8], role: Role) -> SessionId {
    let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(now, peer, alpn, to, role).unwrap();
    net.nodes[a].session(&rep)
}
