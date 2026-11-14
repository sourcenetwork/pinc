//! A hub session the full session table refused is not redialed on every duty pass: it gets the dial backoff a closed
//! session gets.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

mod node_script;

use node_script::{hub_alpn, id_of, node_with};
use vinc_core::{Event, SessionId};
use vinc_node::{BACKOFF_FIRST, HUB_ALPN, NoApps};

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

#[test]
fn a_hub_session_refused_for_a_full_table_is_redialed_after_the_backoff() {
    big(|| {
        let (h1, h2) = (id_of(0x61), id_of(0x62));
        let mut node = node_with(false, &[h1, h2], HUB_ALPN, NoApps::default()).unwrap();
        let mut now = 1_000_000_000;
        // 4000 sessions of one member and 96 of the other hub fill the session table.
        for i in 0..4096u64 {
            let peer = if i < 4000 { id_of(0x41) } else { h2 };
            node.endpoint_mut().events.push_back(Event::Incoming {
                session: SessionId(i),
                node: peer,
                alpn: hub_alpn(),
            });
            if i % 512 == 511 {
                node.poll(now);
                while node.poll_event().is_some() {}
                now += 1_000_000;
            }
        }
        assert!(node.endpoint_mut().closed.is_empty(), "the table took every session");
        node.handle_timeout(now);
        let dialed =
            |node: &mut node_script::ScriptNode<NoApps>| node.endpoint_mut().dials.iter().filter(|d| **d == h1).count();
        assert_eq!(dialed(&mut node), 1, "the node dials the hub whose link it has none of");
        let first = node.endpoint_mut().dials.iter().position(|d| *d == h1).unwrap();
        let session = SessionId(node_script::DIALED + first as u64);
        node.endpoint_mut().events.push_back(Event::Connected {
            session,
            node: h1,
            alpn: hub_alpn(),
            resumed: false,
        });
        node.poll(now);
        assert_eq!(
            node.endpoint_mut().closed,
            [session],
            "the full table refuses the hub session"
        );
        // The duty passes that follow, inside the backoff.
        for k in 1..4u64 {
            node.handle_timeout(now + k * (BACKOFF_FIRST - 100_000_000) / 3);
        }
        assert_eq!(dialed(&mut node), 1, "the hub was redialed inside its backoff");
        node.handle_timeout(now + 2 * BACKOFF_FIRST);
        assert_eq!(dialed(&mut node), 2, "the hub is dialed again after its backoff");
    });
}
