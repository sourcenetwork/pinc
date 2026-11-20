//! Fixtures of the sub-session tests (`core_sub`, `core_sub_probe`): dials, writes, and pairs whose parent session went
//! quiet, was closed, or whose peer restarted.
#![allow(
    clippy::unwrap_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::missing_panics_doc
)]

use pinc_core::{Answer, Command, Event, Query, Reply, Role, SessionId, Value};

use crate::{ALPN_A, CoreNet, MS_NS, SEC_NS, TNode};

/// Whether `e` reports a session connected.
pub fn is_connected(e: &Event) -> bool {
    matches!(e, Event::Connected { .. })
}

/// Dial `b` from `a` for `alpn` at the net's time: the session id and the reply.
pub fn dial(net: &mut CoreNet, a: usize, b: usize, alpn: &[u8]) -> (SessionId, Reply) {
    let (peer, to, now) = (net.nodes[b].node, net.nodes[b].addr, net.now);
    let rep = net.nodes[a].connect(now, peer, alpn, to, Role::Other).unwrap();
    (net.nodes[a].session(&rep), rep)
}

/// Open a stream on session `s` of node `n`, write `data` and finish it.
pub fn write_new(net: &mut CoreNet, n: usize, s: SessionId, data: &[u8]) {
    let now = net.now;
    let Value::Stream(id) = net.nodes[n]
        .cmd(
            now,
            Command::OpenStream {
                session: s,
                bidi: false,
            },
        )
        .unwrap()
        .value
    else {
        panic!()
    };
    net.nodes[n]
        .cmd(
            now,
            Command::Write {
                session: s,
                stream: id,
                data,
            },
        )
        .unwrap();
    net.nodes[n]
        .cmd(now, Command::Finish { session: s, stream: id })
        .unwrap();
}

/// Two connected nodes whose parent session has not heard its peer for 25 seconds, with the session still up.
pub fn silent_parent() -> (CoreNet, usize, usize) {
    let mut net = CoreNet::new(10 * MS_NS);
    net.capture = true;
    let (a, b) = (net.add(1), net.add(2));
    net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let silent = net.nodes[b].addr;
    net.loss = Some(Box::new(move |f, _, _| f == silent));
    net.run_for(25 * SEC_NS);
    net.loss = None;
    assert_eq!(net.nodes[a].ep.sessions().count(), 1);
    (net, a, b)
}

/// Two nodes whose session the dialer closed a moment ago: no parent is left, and the peer's access answer is still
/// cached, so the next dial is an optimistic handshake.
pub fn closed_parent() -> (CoreNet, usize, usize) {
    let mut net = CoreNet::new(10 * MS_NS);
    net.capture = true;
    let (a, b) = (net.add(1), net.add(2));
    let (parent, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let now = net.now;
    net.nodes[a]
        .cmd(
            now,
            Command::Close {
                session: parent,
                error: 0,
            },
        )
        .unwrap();
    net.run_for(2 * SEC_NS);
    assert_eq!(net.nodes[a].ep.sessions().count(), 0);
    (net, a, b)
}

/// Whether a datagram with a long header left since `marker`: a handshake started.
pub fn handshake_since(net: &CoreNet, marker: usize) -> bool {
    net.captured[marker..].iter().any(|(_, _, d)| d[0] & 0x80 != 0)
}

/// Two connected nodes whose peer restarted (same identity and address, none of the session state) and then stayed
/// quiet: the net, the nodes, and the instant the dialer last heard a datagram from it.
pub fn restarted_peer() -> (CoreNet, usize, usize, u64) {
    let mut net = CoreNet::new(10 * MS_NS);
    net.capture = true;
    let (a, b) = (net.add(1), net.add(2));
    let (parent, _) = net.connect_pair(a, b, ALPN_A, Role::Other);
    net.run_for(SEC_NS);
    let (addr, now) = (net.nodes[b].addr, net.now);
    net.nodes[b] = TNode::new(2, addr, now);
    let Answer::Stats(st) = net.nodes[a].ep.query(Query::Stats(parent)) else {
        panic!()
    };
    (net, a, b, st.heard)
}
