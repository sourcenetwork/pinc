//! The newest session of a peer supersedes the old one: a member that restarts while its old session is still open
//! at the hubs is served on the new session, and the old session's later end does not drop the member.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod node_common;

use node_common::{World, big, secs};
use vinc_node::{Body, NodeTrace};
use vinc_node::trace::tag;

#[test]
fn a_restarted_member_is_served_on_its_new_session() {
    big(|| {
        for seed in [141u64, 142, 143] {
            let mut w = World::build_with(seed, 2, 3, |w| w.trace = true);
            let member = w.members[0];
            let id = w.id(member);
            let mt = tag(&id);
            // Down for two seconds: far shorter than any idle timeout, so the hubs still hold the old session.
            w.sim.crash(secs(40), member);
            w.sim.restart(secs(42), member);
            w.run(secs(260));
            for (h, _) in w.hubs.clone() {
                let ups: Vec<_> = w
                    .sim
                    .node(h)
                    .traces
                    .iter()
                    .filter(|(t, it)| *t >= secs(30) && matches!(it.body, Body::Node(NodeTrace::SessionUp { peer, incoming: 1 }) if peer == mt))
                    .collect();
                assert!(!ups.is_empty(), "seed {seed}: hub {h:?} never saw the new session");
                // The old session ended (idle) after the new one took over; that end must not drop the member.
                let downs = w
                    .sim
                    .node(h)
                    .traces
                    .iter()
                    .filter(|(t, it)| *t > ups[0].0 && matches!(it.body, Body::Node(NodeTrace::SessionDown { peer, .. }) if peer == mt))
                    .count();
                assert_eq!(downs, 0, "seed {seed}: hub {h:?} dropped the member when the old session ended");
            }
            for n in w.hubs.iter().map(|(n, _)| *n).chain(w.members.iter().copied().skip(1)) {
                assert!(w.view(n).contains(&id), "seed {seed}: {n:?} lost the restarted member");
                assert!(w.confirmed_down(n, &id).len() <= 1, "seed {seed}: {n:?} confirmed the member down repeatedly");
            }
        }
    });
}
