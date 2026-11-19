//! A hub whose members filled the session table can still link to the other hubs: the table keeps room for the hub
//! links (two per configured hub), refuses a member's session once only that room is free, and a hub link only when
//! the table is full.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

mod node_script;

use node_script::{ScriptNode, hub_alpn, id_of, node_with};
use pinc_core::{Event, SessionId};
use pinc_crypto::NodeId;
use pinc_node::{HUB_ALPN, NoApps};

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// Queue a session of `peer`; every 512th call runs the node, so the endpoint's queue stays short.
fn incoming(node: &mut ScriptNode<NoApps>, now: &mut u64, session: u64, peer: NodeId) {
    node.endpoint_mut().events.push_back(Event::Incoming {
        session: SessionId(session),
        node: peer,
        alpn: hub_alpn(),
    });
    if session % 512 == 511 {
        node.poll(*now);
        while node.poll_event().is_some() {}
        *now += 1_000_000;
    }
}

#[test]
fn members_cannot_fill_the_room_of_the_hub_links() {
    big(|| {
        let h1 = id_of(0x61);
        let mut node = node_with(true, &[h1], HUB_ALPN, NoApps::default()).unwrap();
        let mut now = 1_000_000_000;
        // Members ask for 4096 sessions, one more than the table can hold.
        for i in 0..4096u64 {
            incoming(&mut node, &mut now, i, id_of(0x41));
        }
        // The other hub's session arrives after: it finds room.
        incoming(&mut node, &mut now, 5000, h1);
        node.poll(now);
        let closed = node.endpoint_mut().closed.clone();
        assert!(
            !closed.contains(&SessionId(5000)),
            "the table the members filled refused the link of the other hub: closed {closed:?}"
        );
        assert_eq!(
            closed,
            [SessionId(4094), SessionId(4095)],
            "the members' sessions past the room kept for hub links are refused"
        );
        // That room is the hub's: a second session of the hub finds it, a third finds the table full.
        incoming(&mut node, &mut now, 5001, h1);
        incoming(&mut node, &mut now, 5002, h1);
        node.poll(now);
        assert_eq!(
            node.endpoint_mut().closed.get(2..),
            Some(&[SessionId(5002)][..]),
            "a hub link is refused only when the table is full"
        );
    });
}
