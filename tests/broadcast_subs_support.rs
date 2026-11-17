//! Helpers of the subscriber-list tests: nodes a hub cannot write to, hand-built SUBS payloads, and what a member holds.
//!
//! Included by the `broadcast_subs*` test targets with `#[path]`, after `broadcast_common`; not a test target itself.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::cell::Cell;
use std::rc::Rc;

use crate::common::{Ev, Net, SEC, ty};
use vinc_broadcast::consts::SUBS_PIECE;
use vinc_broadcast::{Limits, SubsDrop, Trace};
use vinc_crypto::IdentityAlg;
use vinc_membership::NodeId;

pub const T: &[u8] = b"roster";

pub fn resubscribe(net: &mut Net, i: usize) {
    let (now, hub) = (net.now, net.id(0));
    let n = &mut net.nodes[i];
    n.t.resubscribe(&mut n.h, now, &hub);
    net.pump();
}

/// Hand node `to` the SUBS payload `rest` as if `from` sent it, and return the drop reasons it traced.
pub fn inject(net: &mut Net, from: usize, to: usize, rest: &[u8]) -> Vec<SubsDrop> {
    let (now, fid) = (net.now, net.id(from));
    let n = &mut net.nodes[to];
    while n.t.poll_trace().is_some() {}
    n.t.frame(&mut n.h, now, &fid, ty::SUBS, T, rest);
    let mut why = Vec::new();
    while let Some(t) = n.t.poll_trace() {
        if let Trace::SubsDropped { why: w, .. } = t {
            why.push(w);
        }
    }
    why
}

/// A SUBS piece payload: kind 0, the version, the rank of the first id, the length of the whole list, the ids.
pub fn piece(ver: (u64, u32), first: u16, total: u16, ids: &[NodeId]) -> Vec<u8> {
    let mut b = vec![0u8];
    b.extend_from_slice(&ver.0.to_be_bytes());
    b.extend_from_slice(&ver.1.to_be_bytes());
    b.extend_from_slice(&first.to_be_bytes());
    b.extend_from_slice(&total.to_be_bytes());
    b.extend_from_slice(&(ids.len() as u16).to_be_bytes());
    b.extend_from_slice(ids.as_flattened());
    b
}

/// A node that is not in anyone's reach: a send to it is refused.
pub fn fake(i: u32) -> NodeId {
    let mut id = [0xEE; 32];
    id[..4].copy_from_slice(&i.to_be_bytes());
    id
}

/// Hand hub 0 a SUB from each of `ids`, as if they subscribed from a session the hub cannot write to.
pub fn hand(net: &mut Net, ids: &[NodeId]) {
    let now = net.now;
    let hub = &mut net.nodes[0];
    hub.h.tick(now);
    for id in ids {
        hub.t.frame(&mut hub.h, now, id, ty::SUB, T, &0u64.to_be_bytes());
    }
    net.pump();
}

/// A hub and `members` attached members, with room for 512 subscribers in a list.
pub fn wide_net(members: usize) -> Net {
    let limits = Limits {
        max_subscribers: 512,
        ..Limits::default()
    };
    let mut net = Net::with_limits(&vec![IdentityAlg::Ed25519; 1 + members], 1, SEC, limits);
    for i in 1..=members {
        net.attach(i);
    }
    net
}

/// Hand hub 0 `n` subscribers it cannot reach.
pub fn synth(net: &mut Net, n: u32) -> Vec<NodeId> {
    let ids: Vec<NodeId> = (0..n).map(fake).collect();
    hand(net, &ids);
    ids
}

/// The kind of a SUBS frame in flight and, for a piece, the rank of its first id.
pub fn subs_kind(bytes: &[u8]) -> Option<(u8, u16)> {
    let at = 6 + T.len();
    let kind = *bytes.get(at).filter(|_| bytes.get(4) == Some(&ty::SUBS))?;
    let first = bytes
        .get(at + 13..at + 15)
        .map_or(0, |b| u16::from_be_bytes([b[0], b[1]]));
    Some((kind, first))
}

pub fn holds(net: &Net, i: usize, want: &[NodeId]) -> bool {
    net.nodes[i].t.known_subscribers(T) == want
}

pub fn subscribed(net: &Net, i: usize) -> bool {
    net.events(i).iter().any(|e| matches!(e, Ev::Subscribed { .. }))
}

/// The gaps node `i` traced since the last call.
pub fn gaps(net: &mut Net, i: usize) -> usize {
    let mut n = 0;
    while let Some(t) = net.nodes[i].t.poll_trace() {
        n += usize::from(matches!(t, Trace::SubsDropped { why: SubsDrop::Gap, .. }));
    }
    n
}

pub fn sorted(mut ids: Vec<NodeId>) -> Vec<NodeId> {
    ids.sort_unstable();
    ids
}

/// What a node's stream holds when nothing is queued on it: the node crate's default.
pub const HOLDS: usize = 1 << 20;

/// The bytes of a list of `n` ids on the wire: its piece frames, length prefixes included.
pub fn wire_bytes(n: usize) -> usize {
    32 * n + n.div_ceil(SUBS_PIECE).max(1) * (25 + T.len())
}

/// Count the pieces of a list that reach node `to`.
pub fn count_pieces(net: &mut Net, to: usize) -> Rc<Cell<usize>> {
    let pieces = Rc::new(Cell::new(0usize));
    let p = Rc::clone(&pieces);
    net.filter = Some(Box::new(move |_, t, bytes| {
        p.set(p.get() + usize::from(t == to && matches!(subs_kind(bytes), Some((0, _)))));
        true
    }));
    pieces
}

/// The host of hub 0 says the stream of `peer` has room again.
pub fn writable(net: &mut Net, peer: &NodeId) {
    let now = net.now;
    let hub = &mut net.nodes[0];
    hub.t.peer_writable(&mut hub.h, now, peer);
    net.pump();
}
