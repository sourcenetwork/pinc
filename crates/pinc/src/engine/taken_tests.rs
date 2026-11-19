//! The facade queues only a session the endpoint still holds (pinc#436): an `Incoming` whose session the endpoint does
//! not hold (it ended before the event was read) is `Taken::Gone` and gets no place in the accept queue.

use pinc_core::{Event, SessionId};
use pinc_security::Alpn;

use super::adjacent_tests::{core, peer};

#[test]
fn an_incoming_for_a_session_the_endpoint_does_not_hold_gets_no_place() {
    let mut c = core();
    let alpn = Alpn::new(b"app").unwrap();
    let owed = c.node.endpoint().node_stats().owed;
    c.on_event(
        1,
        Event::Incoming {
            session: SessionId(1),
            node: peer(0),
            alpn,
        },
    );
    assert!(c.sessions.is_empty(), "no session is kept for it");
    assert!(
        c.routes.iter().all(|r| r.queue.is_empty()),
        "no place is taken in a queue"
    );
    assert_eq!(
        c.node.endpoint().node_stats().owed,
        owed,
        "the endpoint's count is unchanged"
    );
}
