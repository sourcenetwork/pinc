//! Helpers of the `broadcast_reach*` targets: name a node's peers, open and close sessions, hand a hub a frame.
//!
//! Included with `#[path]`; not a test target itself.
#![allow(dead_code, unreachable_pub, clippy::unwrap_used, clippy::indexing_slicing)]

use crate::common::{Net, ty};
use pinc_membership::NodeId;

pub const T: &[u8] = b"reach";

/// Node `i` names `peers` (by index) as the peers it holds sessions with.
pub fn adj(net: &mut Net, i: usize, peers: &[usize]) {
    let ids: Vec<NodeId> = peers.iter().map(|p| net.id(*p)).collect();
    let now = net.now;
    let n = &mut net.nodes[i];
    n.h.tick(now);
    n.t.set_adjacent(&mut n.h, now, &ids).unwrap();
    net.pump();
}

/// A session between `a` and `b` as both ends report it.
pub fn session(net: &mut Net, edges: &mut Vec<(usize, usize)>, a: usize, b: usize, up: bool) {
    if up {
        edges.push((a, b));
    } else {
        edges.retain(|e| *e != (a, b) && *e != (b, a));
    }
    for i in [a, b] {
        let peers: Vec<usize> = edges
            .iter()
            .filter_map(|(x, y)| {
                if *x == i {
                    Some(*y)
                } else if *y == i {
                    Some(*x)
                } else {
                    None
                }
            })
            .collect();
        adj(net, i, &peers);
    }
}

pub fn got(net: &Net, i: usize, mid: [u8; 8]) -> bool {
    net.delivered(i).contains(&mid)
}

/// `from` publishes `body`; whether `to` delivered it.
pub fn sends(net: &mut Net, from: usize, to: usize, body: &[u8]) -> bool {
    let mid = net.publish(from, T, body);
    got(net, to, mid)
}

/// What `hub` sends `to` for a frame `t` with `rest` that `to` hands it.
pub fn ask(net: &mut Net, hub: usize, to: usize, t: u8, rest: &[u8]) -> Vec<Vec<u8>> {
    let (now, asker) = (net.now, net.id(to));
    let n = &mut net.nodes[hub];
    n.h.out.clear();
    n.h.tick(now);
    n.t.frame(&mut n.h, now, &asker, t, T, rest);
    let out =
        n.h.out
            .iter()
            .filter(|o| o.to == asker)
            .map(|o| o.bytes.clone())
            .collect();
    n.h.out.clear();
    out
}

/// The ids every HAVE frame of `frames` offers.
pub fn offered(frames: &[Vec<u8>]) -> Vec<[u8; 8]> {
    frames
        .iter()
        .filter(|f| f.get(4) == Some(&ty::HAVE))
        .flat_map(|f| f[6 + T.len()..].as_chunks::<8>().0.to_vec())
        .collect()
}

/// Node `i`'s next record, kept from the hubs and returned as the frame's rest.
pub fn capture(net: &mut Net, i: usize, peers: &[usize]) -> Vec<u8> {
    let rec = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let r = rec.clone();
    net.filter = Some(Box::new(move |from, _, b: &mut Vec<u8>| {
        if from == i && b.get(4) == Some(&ty::ADJ) {
            r.borrow_mut().clone_from(b);
            return false;
        }
        true
    }));
    adj(net, i, peers);
    net.filter = None;
    rec.borrow()[6..].to_vec()
}

/// A hub table's bytes for `records` records of no peers and an Ed25519 signature, and 8 peers named between them: one
/// more record of no peers does not fit.
pub fn room(records: usize) -> usize {
    records * (pinc_broadcast::consts::REACH_RECORD_BASE + 64) + 8 * 32
}
