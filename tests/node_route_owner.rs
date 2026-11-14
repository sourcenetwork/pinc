//! An event of a hub or layer session reaches only its owner: no stream, room-to-open or datagram event of such a
//! session reaches the application, whether the node recorded the session, refused it for a full table or a layer that
//! is off, or closed it as the duplicate of a simultaneous dial. Its lifecycle events still do.
//!
//! The endpoint is scripted and, unlike a real one, keeps the events it queued for a session the node closed, so the
//! node's own routing is what is tested.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, missing_docs)]

mod node_script;

use node_script::{ScriptNode, hub_alpn, id_of, node_with};
use vinc_core::{Event, SessionId};
use vinc_node::{DTN_ALPN, Enabled, HUB_ALPN, NoApps, NodeEvent, SETS_ALPN, VALUES_ALPN};
use vinc_security::Alpn;
use vinc_tests::LayerApps;

/// A thread with the stack a node needs.
fn big<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap()
}

/// One of each event of a session's data plane.
fn data_events(session: SessionId) -> [Event; 7] {
    [
        Event::StreamOpened { session, stream: 1 },
        Event::StreamReadable { session, stream: 1 },
        Event::StreamWritable { session, stream: 1 },
        Event::StreamReset {
            session,
            stream: 1,
            error: 1,
        },
        Event::StreamStopped {
            session,
            stream: 1,
            error: 1,
        },
        Event::OpenReady { session },
        Event::DatagramReceived { session },
    ]
}

fn is_data_event(e: &Event) -> bool {
    matches!(
        e,
        Event::StreamOpened { .. }
            | Event::StreamReadable { .. }
            | Event::StreamWritable { .. }
            | Event::StreamReset { .. }
            | Event::StreamStopped { .. }
            | Event::OpenReady { .. }
            | Event::DatagramReceived { .. }
    )
}

/// Run the node and return every endpoint event it handed the application.
fn drive<A: vinc_node::Apps<vinc_tests::Caps>>(node: &mut ScriptNode<A>, now: u64) -> Vec<Event> {
    node.poll(now);
    let mut seen = Vec::new();
    while let Some(e) = node.poll_event() {
        if let NodeEvent::Endpoint(ev) = e {
            seen.push(ev);
        }
    }
    seen
}

fn incoming(session: SessionId, peer: u8, alpn: &[u8]) -> Event {
    Event::Incoming {
        session,
        node: id_of(peer),
        alpn: Alpn::new(alpn).unwrap(),
    }
}

#[test]
fn no_data_event_of_a_hub_session_reaches_the_application() {
    big(|| {
        let mut node = node_with(true, &[], HUB_ALPN, NoApps::default()).unwrap();
        let s = SessionId(1);
        node.endpoint_mut().events.push_back(incoming(s, 0x41, HUB_ALPN));
        node.endpoint_mut().events.extend(data_events(s));
        let seen = drive(&mut node, 1_000_000_000);
        assert!(
            seen.iter().any(|e| matches!(e, Event::Incoming { .. })),
            "the lifecycle event of the session reaches the application"
        );
        let leaked: Vec<_> = seen.iter().filter(|e| is_data_event(e)).collect();
        assert!(
            leaked.is_empty(),
            "data events of a hub session reached the application: {leaked:?}"
        );
    });
}

#[test]
fn no_data_event_of_a_layer_session_reaches_the_application() {
    big(|| {
        for alpn in [VALUES_ALPN, SETS_ALPN, DTN_ALPN] {
            let mut node = node_with(true, &[], HUB_ALPN, LayerApps::new(1, Enabled::ALL)).unwrap();
            let s = SessionId(1);
            node.endpoint_mut().events.push_back(incoming(s, 0x41, alpn));
            node.endpoint_mut().events.extend(data_events(s));
            let seen = drive(&mut node, 1_000_000_000);
            assert!(
                seen.iter().any(|e| matches!(e, Event::Incoming { .. })),
                "the lifecycle event of the session reaches the application"
            );
            let leaked: Vec<_> = seen.iter().filter(|e| is_data_event(e)).collect();
            assert!(
                leaked.is_empty(),
                "data events of a session of {} reached the application: {leaked:?}",
                String::from_utf8_lossy(alpn)
            );
        }
    });
}

/// A session the node refused and closed, whose queued events the endpoint still hands over, reaches no one: not a
/// hub session its full table cannot record, not a layer session of a layer that is off, not a duplicate dial.
#[test]
fn no_data_event_of_a_session_closed_before_it_was_recorded_reaches_the_application() {
    big(|| {
        // The hub session table is full: the 4097th session is closed unrecorded.
        let mut node = node_with(true, &[], HUB_ALPN, NoApps::default()).unwrap();
        let mut now = 1_000_000_000;
        for i in 0..4096u64 {
            node.endpoint_mut()
                .events
                .push_back(incoming(SessionId(i), 0x41, HUB_ALPN));
            if i % 512 == 511 {
                drive(&mut node, now);
                now += 1_000_000;
            }
        }
        let refused = SessionId(4096);
        node.endpoint_mut().events.push_back(incoming(refused, 0x41, HUB_ALPN));
        node.endpoint_mut().events.extend(data_events(refused));
        let seen = drive(&mut node, now);
        assert_eq!(
            node.endpoint_mut().closed,
            [refused],
            "only the refused session was closed"
        );
        let leaked: Vec<_> = seen.iter().filter(|e| is_data_event(e)).collect();
        assert!(
            leaked.is_empty(),
            "data events of a hub session the full table refused reached the application: {leaked:?}"
        );
    });
    big(|| {
        // A layer that is off: its session is closed by the node.
        let mut node = node_with(true, &[], HUB_ALPN, NoApps::default()).unwrap();
        let s = SessionId(1);
        node.endpoint_mut().events.push_back(incoming(s, 0x41, VALUES_ALPN));
        node.endpoint_mut().events.extend(data_events(s));
        let seen = drive(&mut node, 1_000_000_000);
        assert_eq!(node.endpoint_mut().closed, [s]);
        let leaked: Vec<_> = seen.iter().filter(|e| is_data_event(e)).collect();
        assert!(
            leaked.is_empty(),
            "data events of a layer session the node refused reached the application: {leaked:?}"
        );
    });
    big(|| {
        // The second dial of one layer to one peer is closed as the duplicate of the first.
        let mut node = node_with(true, &[], HUB_ALPN, LayerApps::new(1, Enabled::ALL)).unwrap();
        let peer = id_of(0x41);
        let connected = |session| Event::Connected {
            session,
            node: peer,
            alpn: Alpn::new(VALUES_ALPN).unwrap(),
            resumed: false,
        };
        node.endpoint_mut().events.push_back(connected(SessionId(1)));
        node.endpoint_mut().events.push_back(connected(SessionId(2)));
        node.endpoint_mut().events.extend(data_events(SessionId(2)));
        let seen = drive(&mut node, 1_000_000_000);
        assert_eq!(node.endpoint_mut().closed, [SessionId(2)], "the duplicate was closed");
        let leaked: Vec<_> = seen.iter().filter(|e| is_data_event(e)).collect();
        assert!(
            leaked.is_empty(),
            "data events of a duplicate layer session reached the application: {leaked:?}"
        );
    });
    big(|| {
        // Two hub sessions of one peer at once: the one that is not kept is closed and its events go nowhere.
        let mut node = node_with(true, &[], HUB_ALPN, NoApps::default()).unwrap();
        let peer = id_of(0x41);
        node.endpoint_mut().events.push_back(Event::Connected {
            session: SessionId(1),
            node: peer,
            alpn: hub_alpn(),
            resumed: false,
        });
        node.endpoint_mut().events.push_back(Event::Connected {
            session: SessionId(2),
            node: peer,
            alpn: hub_alpn(),
            resumed: false,
        });
        let closed_events = [SessionId(1), SessionId(2)].into_iter().flat_map(data_events);
        node.endpoint_mut().events.extend(closed_events);
        let seen = drive(&mut node, 1_000_000_000);
        let leaked: Vec<_> = seen.iter().filter(|e| is_data_event(e)).collect();
        assert!(
            leaked.is_empty(),
            "data events of hub sessions reached the application: {leaked:?}"
        );
    });
}
