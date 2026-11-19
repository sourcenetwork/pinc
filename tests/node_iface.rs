//! The node passes interface events to its endpoint: a member whose interface changes address has its sessions move to
//! the new address, and the interface table is reachable through the node.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod node_common;

use std::net::SocketAddr;

use node_common::{World, big, ip, secs};
use pinc_core::{Answer, IfaceEvent, IfaceId, Query};

fn local_routes(w: &World, n: pinc_sim::NodeId) -> Vec<SocketAddr> {
    let node = &w.sim.node(n).node;
    (0..)
        .map_while(|i| node.endpoint().query(Query::SessionAt(i)).stats())
        .filter_map(|st| st.route.map(|(l, _)| l))
        .collect()
}

trait Stats {
    fn stats(self) -> Option<pinc_core::SessionStats>;
}

impl Stats for Answer<'_> {
    fn stats(self) -> Option<pinc_core::SessionStats> {
        match self {
            Answer::Stats(s) => Some(s),
            _ => None,
        }
    }
}

#[test]
fn an_address_change_reaches_the_endpoint() {
    big(|| {
        let mut w = World::build(7, 2, 2);
        w.run(secs(20));
        let m = w.members[0];
        let old = w.sim.node(m).addr;
        assert!(
            local_routes(&w, m).iter().all(|a| *a == old),
            "sessions start on the interface"
        );
        let new = SocketAddr::new(ip(198, 51, 100, 200), old.port());
        let t = secs(20);
        w.sim
            .node_mut(m)
            .node
            .iface_event(t, IfaceId(0), IfaceEvent::AddrChange(new));
        assert!(!local_routes(&w, m).is_empty(), "the member keeps its sessions");
        let mut buf = vec![0u8; 2048];
        let mut sent_from_new = false;
        w.sim.node_mut(m).node.handle_timeout(t + 1_000_000);
        let t = t + 1_000_000;
        while let Some(tx) = w.sim.node_mut(m).node.poll_transmit(t, &mut buf) {
            sent_from_new |= tx.local == new;
        }
        assert!(sent_from_new, "the endpoint probes its sessions from the new address");
        let extra = w
            .sim
            .node_mut(m)
            .node
            .add_iface(SocketAddr::new(ip(198, 51, 100, 201), 4433));
        assert!(extra.is_some(), "the interface table takes another interface");
    });
}
