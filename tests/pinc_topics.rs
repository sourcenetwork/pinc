//! Topics through the facade: raw publish and subscribe on hubs, the way a key service uses them.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

#[macro_use]
mod pinc_common;

use std::net::SocketAddr;
use std::time::Duration;

use pinc::{Admission, Direction, ErrorKind, Event, Limits, NodeId, Relay};
use pinc_common::within;

/// Refuses one peer, admits the others.
struct Deny(NodeId);

impl Admission for Deny {
    fn admit(&self, peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        *peer != self.0
    }
}

/// The next message of the endpoint's events within `ms`, skipping the others.
macro_rules! next_message {
    ($ep:expr, $ms:expr) => {{
        let ep = $ep.clone();
        nuclei::time::timeout(Duration::from_millis($ms), async move {
            loop {
                match ep.event().await {
                    Some(Event::Message {
                        topic,
                        origin,
                        hop,
                        direct,
                        payload,
                    }) => break Some((topic, origin, hop, direct, payload)),
                    Some(_) => {}
                    None => break None,
                }
            }
        })
        .await
        .ok()
        .flatten()
    }};
}

fn run(ep: &(impl Clone + 'static + RunHandle)) {
    let e = ep.clone();
    nuclei::spawn_local(async move { e.run_forever().await }).detach();
}

/// What the tests need of an endpoint to drive it.
trait RunHandle {
    async fn run_forever(&self);
}

impl<H: pinc::Hosted + 'static, D: pinc::Discovery + 'static> RunHandle for pinc::Endpoint<H, D> {
    async fn run_forever(&self) {
        let _ = self.run().await;
    }
}

fn hub_relay(addr: SocketAddr, id: NodeId) -> Relay {
    Relay::new(id).with_udp(addr)
}

#[nuclei::test]
async fn a_raw_request_and_its_response_cross_two_topics_through_a_hub() {
    let hub = lo_endpoint!(pinc_common::builder().seed(&[10; 32]).unwrap().hub());
    run(&hub);
    let relay = hub_relay(hub.local_addr(), hub.id());
    let a = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap().relays([relay]));
    let b = lo_endpoint!(pinc_common::builder().seed(&[2; 32]).unwrap().relays([relay]));
    run(&a);
    run(&b);
    let request = b"kms/request".to_vec();
    let response = format!("kms/{}/_response", pinc::node_to_string(&a.id())).into_bytes();
    within(120, async {
        assert!(b.join(&request, &[]).await.unwrap());
        assert!(a.join(&response, &[]).await.unwrap());
        // The service answers every request on the requester's topic.
        let (svc, resp_topic) = (b.clone(), response.clone());
        nuclei::spawn_local(async move {
            while let Some(Event::Message { payload, .. }) = {
                let mut ev = svc.event().await;
                while !matches!(ev, Some(Event::Message { .. }) | None) {
                    ev = svc.event().await;
                }
                ev
            } {
                let mut reply = b"answer:".to_vec();
                reply.extend_from_slice(&payload);
                let _ = svc.publish(&resp_topic, &reply, None).await;
            }
        })
        .detach();
        // A asks until an answer comes back: a subscription takes a moment to reach the hub.
        let mut got = None;
        for _ in 0..200 {
            a.publish(&request, b"who", None).await.unwrap();
            if let Some(m) = next_message!(a, 300) {
                got = Some(m);
                break;
            }
        }
        let (topic, origin, hop, direct, payload) = got.expect("no response reached the requester");
        assert_eq!(topic, response);
        assert_eq!(payload, b"answer:who");
        assert_eq!(origin, b.id(), "the answer is signed by the service");
        assert_eq!(hop, hub.id(), "it came through the hub");
        assert!(!direct);
    })
    .await;
}

/// A join with the hint of a peer and no hub at all: the peer is a neighbour once its session is up, as the join's
/// documentation says.
#[nuclei::test]
async fn a_join_with_a_hint_and_no_hub_list_has_the_hinted_peer_as_a_neighbour() {
    const T: &[u8] = b"hinted";
    let a = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap());
    let b = lo_endpoint!(pinc_common::builder().seed(&[2; 32]).unwrap());
    run(&a);
    run(&b);
    within(60, async {
        a.join(T, &[b.addr()]).await.unwrap();
        let mut seen = a.neighbors(T);
        for _ in 0..200 {
            if !seen.is_empty() {
                break;
            }
            nuclei::time::sleep(Duration::from_millis(50)).await;
            seen = a.neighbors(T);
        }
        assert_eq!(seen, [b.id()], "the hinted peer is not a neighbour");
    })
    .await;
}

#[nuclei::test]
async fn a_publish_that_waits_for_a_neighbour_times_out_when_none_joins() {
    let a = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap());
    run(&a);
    within(60, async {
        let t0 = std::time::Instant::now();
        let e = a
            .publish(b"nobody", b"x", Some(Duration::from_millis(300)))
            .await
            .unwrap_err();
        assert_eq!(e.kind(), ErrorKind::TimedOut);
        let took = t0.elapsed();
        assert!(
            took >= Duration::from_millis(300) && took < Duration::from_secs(10),
            "{took:?}"
        );
        // Without a wait the same publish goes out at once.
        a.publish(b"nobody", b"x", None).await.unwrap();
        assert_eq!(a.neighbors(b"nobody"), [] as [pinc::NodeId; 0]);
    })
    .await;
}

#[nuclei::test]
async fn a_publish_over_the_limit_is_a_typed_error_and_one_at_the_limit_goes() {
    let limits = Limits {
        topic_message: 4096,
        ..Limits::default()
    };
    let a = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap().limits(limits));
    run(&a);
    assert_eq!(a.max_message(), 4096);
    within(60, async {
        a.publish(b"t", &vec![7u8; 4096], None).await.unwrap();
        let e = a.publish(b"t", &vec![7u8; 4097], None).await.unwrap_err();
        assert_eq!(e.kind(), ErrorKind::TooLarge);
        let e = a.publish(&[b'x'; 256], b"x", None).await.unwrap_err();
        assert_eq!(e.kind(), ErrorKind::Config, "a topic name over 255 bytes");
    })
    .await;
}

#[nuclei::test]
async fn a_peer_the_hub_refuses_receives_nothing() {
    // The hub refuses D: D never attaches and hears nothing, while C does.
    let d_id = pinc::Identity::from_seed(&[4; 32]).unwrap().node_id();
    let hub = lo_endpoint!(pinc_common::builder().seed(&[10; 32]).unwrap().hub().acp(Deny(d_id)));
    run(&hub);
    let relay = hub_relay(hub.local_addr(), hub.id());
    let a = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap().relays([relay]));
    let c = lo_endpoint!(pinc_common::builder().seed(&[3; 32]).unwrap().relays([relay]));
    let d = lo_endpoint!(pinc_common::builder().seed(&[4; 32]).unwrap().relays([relay]));
    run(&a);
    run(&c);
    run(&d);
    within(120, async {
        c.join(b"t", &[]).await.unwrap();
        d.join(b"t", &[]).await.unwrap();
        let mut c_got = false;
        let mut d_got = false;
        for _ in 0..60 {
            a.publish(b"t", b"hello", None).await.unwrap();
            c_got |= next_message!(c, 200).is_some();
            d_got |= next_message!(d, 50).is_some();
            if c_got {
                break;
            }
        }
        assert!(c_got, "the admitted member got the message");
        // Keep publishing: the refused peer still hears nothing.
        for _ in 0..10 {
            a.publish(b"t", b"again", None).await.unwrap();
            d_got |= next_message!(d, 100).is_some();
        }
        assert!(!d_got, "a peer the hub refused received a message");
    })
    .await;
}

#[nuclei::test]
async fn a_message_from_a_peer_a_member_refuses_is_not_delivered_to_it() {
    // A refuses D as the origin of messages: C hears D, A does not.
    let d_id = pinc::Identity::from_seed(&[4; 32]).unwrap().node_id();
    let hub = lo_endpoint!(pinc_common::builder().seed(&[10; 32]).unwrap().hub());
    run(&hub);
    let relay = hub_relay(hub.local_addr(), hub.id());
    let a = lo_endpoint!(
        pinc_common::builder()
            .seed(&[1; 32])
            .unwrap()
            .relays([relay])
            .acp(Deny(d_id))
    );
    let c = lo_endpoint!(pinc_common::builder().seed(&[3; 32]).unwrap().relays([relay]));
    let d = lo_endpoint!(pinc_common::builder().seed(&[4; 32]).unwrap().relays([relay]));
    run(&a);
    run(&c);
    run(&d);
    within(120, async {
        a.join(b"t", &[]).await.unwrap();
        c.join(b"t", &[]).await.unwrap();
        let mut c_got = false;
        let mut a_got = false;
        for _ in 0..60 {
            d.publish(b"t", b"from d", None).await.unwrap();
            c_got |= next_message!(c, 200).is_some();
            a_got |= next_message!(a, 50).is_some();
            if c_got {
                break;
            }
        }
        assert!(c_got, "the member that admits D heard it");
        for _ in 0..10 {
            d.publish(b"t", b"again", None).await.unwrap();
            a_got |= next_message!(a, 100).is_some();
        }
        assert!(!a_got, "a message of a refused origin was delivered");
    })
    .await;
}

/// A burst is held back, not dropped and not failed: once the endpoint tracks as many publishes as it can, the next
/// one waits, and it goes through when the hub acknowledges earlier ones.
#[nuclei::test]
async fn a_publish_past_the_tracked_ones_waits_for_the_hub_and_then_goes() {
    /// The publishes an endpoint tracks while they wait for a hub.
    const TRACKED: usize = 1024;
    let hub = lo_endpoint!(pinc_common::builder().seed(&[10; 32]).unwrap().hub());
    let relay = hub_relay(hub.local_addr(), hub.id());
    let a = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap().relays([relay]));
    run(&a);
    let topic = b"burst".to_vec();
    within(120, async {
        // The hub is not running yet: nothing is acknowledged, so the endpoint's table fills.
        for k in 0..TRACKED {
            a.publish(&topic, format!("message {k}").as_bytes(), None)
                .await
                .unwrap();
        }
        let (ep, t) = (a.clone(), topic.clone());
        let mut one_more = Box::pin(async move { ep.publish(&t, b"one more", None).await });
        let early = nuclei::time::timeout(Duration::from_millis(300), &mut one_more).await;
        assert!(
            early.is_err(),
            "a publish the endpoint cannot track came back: {early:?}"
        );
        // The hub starts and acknowledges: the waiting publish is taken.
        run(&hub);
        nuclei::time::timeout(Duration::from_secs(60), one_more)
            .await
            .expect("the publish still waits although the hub acknowledges")
            .unwrap();
    })
    .await;
}

#[nuclei::test]
async fn with_connected_topics_a_group_hears_only_the_publishers_its_sessions_link_it_to() {
    const APP: &[u8] = b"app";
    const T: &[u8] = b"doc";
    let hub = lo_endpoint!(pinc_common::builder().seed(&[10; 32]).unwrap().hub());
    run(&hub);
    let relay = hub_relay(hub.local_addr(), hub.id());
    let member = |seed: u8| {
        pinc_common::builder()
            .seed(&[seed; 32])
            .unwrap()
            .relays([relay])
            .alpn(APP)
            .connected_topics()
    };
    let (a1, a2, b1) = (
        lo_endpoint!(member(1)),
        lo_endpoint!(member(2)),
        lo_endpoint!(member(3)),
    );
    run(&a1);
    run(&a2);
    run(&b1);
    within(120, async {
        // A1 - A2 hold an application session; B1 holds none.
        let _conn = a1.connect(a2.addr(), APP).await.unwrap();
        a1.join(T, &[]).await.unwrap();
        a2.join(T, &[]).await.unwrap();
        b1.join(T, &[]).await.unwrap();
        let mut got = None;
        for _ in 0..200 {
            a1.publish(T, b"from a1", None).await.unwrap();
            if let Some(m) = next_message!(a2, 300) {
                got = Some(m);
                break;
            }
        }
        assert_eq!(got.expect("A2 never heard A1").4, b"from a1");
        for _ in 0..5 {
            a1.publish(T, b"from a1", None).await.unwrap();
            b1.publish(T, b"from b1", None).await.unwrap();
        }
        assert!(
            next_message!(b1, 2_000).is_none(),
            "B1 has no session with A1 and hears nothing"
        );
        while let Some(m) = next_message!(a2, 500) {
            assert_eq!(m.1, a1.id(), "A2 hears only A1, never B1");
        }
        // The hub's table is reachable through the facade: three records, open; A1 signed its first record and
        // the one naming A2.
        let at_hub = hub.reach_stats().expect("the hub runs");
        assert!(at_hub.records >= 3 && !at_hub.closed, "{at_hub:?}");
        assert!(a1.reach_stats().expect("A1 runs").signed >= 2);
    })
    .await;
}

/// Whether the endpoint hears a message within 300 ms; a notice that messages may be missing fails the test.
macro_rules! heard_before {
    ($ep:expr) => {{
        let ep = $ep.clone();
        nuclei::time::timeout(Duration::from_millis(300), async move {
            loop {
                match ep.event().await {
                    Some(Event::Message { .. }) => break true,
                    Some(Event::Missed { .. }) => panic!("a first join heard that messages may be missing"),
                    Some(_) => {}
                    None => break false,
                }
            }
        })
        .await
        .unwrap_or(false)
    }};
}

/// An endpoint stops, a burst longer than the hub's log goes by, and a new life of the same identity joins the topic:
/// the hub replays what its log still holds and cannot give the rest, and the application hears it once
/// (`Event::Missed`, pinc#507). A first join hears no such event.
#[nuclei::test]
async fn an_endpoint_that_comes_back_to_a_log_that_moved_past_it_hears_that_messages_may_be_missing() {
    let hub = lo_endpoint!(pinc_common::builder().seed(&[10; 32]).unwrap().hub());
    run(&hub);
    let relay = hub_relay(hub.local_addr(), hub.id());
    let publisher = lo_endpoint!(pinc_common::builder().seed(&[1; 32]).unwrap().relays([relay]));
    run(&publisher);
    // A second subscriber that stays: when it has the last message of the burst, the hub has logged all of it.
    let watcher = lo_endpoint!(pinc_common::builder().seed(&[3; 32]).unwrap().relays([relay]));
    run(&watcher);
    let topic = b"feed".to_vec();
    within(120, async {
        let first = lo_endpoint!(pinc_common::builder().seed(&[2; 32]).unwrap().relays([relay]));
        run(&first);
        assert!(first.join(&topic, &[]).await.unwrap());
        assert!(watcher.join(&topic, &[]).await.unwrap());
        // A subscription takes a moment to reach the hub: publish until a message arrives at both.
        let (mut a, mut b) = (false, false);
        for _ in 0..200 {
            publisher.publish(&topic, b"before", None).await.unwrap();
            a = a || heard_before!(first);
            b = b || heard_before!(watcher);
            if a && b {
                break;
            }
        }
        assert!(a && b, "no message reached the subscribers");
        first.close().await;
        // More messages than the hub's log holds (2,048), none of them to the endpoint that stopped.
        for k in 0..2_200u32 {
            publisher.publish(&topic, &k.to_be_bytes(), None).await.unwrap();
        }
        publisher.publish(&topic, b"last", None).await.unwrap();
        let w = watcher.clone();
        let logged = nuclei::time::timeout(Duration::from_secs(60), async move {
            loop {
                match w.event().await {
                    Some(Event::Message { payload, .. }) if payload == b"last" => break true,
                    Some(_) => {}
                    None => break false,
                }
            }
        })
        .await
        .unwrap_or(false);
        assert!(logged, "the burst did not reach the subscriber that stayed");
        let again = lo_endpoint!(pinc_common::builder().seed(&[2; 32]).unwrap().relays([relay]));
        run(&again);
        assert!(again.join(&topic, &[]).await.unwrap());
        let (ep, hub_id, want) = (again.clone(), hub.id(), topic.clone());
        let missed = nuclei::time::timeout(Duration::from_secs(60), async move {
            let mut n = 0;
            let mut quiet = Duration::from_secs(60);
            // After the first notice, read two more seconds of events: there is no second one.
            loop {
                match nuclei::time::timeout(quiet, ep.event()).await {
                    Ok(Some(Event::Missed { topic, hub })) => {
                        assert_eq!((topic, hub), (want.clone(), hub_id));
                        n += 1;
                        quiet = Duration::from_secs(2);
                    }
                    Ok(Some(_)) => {}
                    Ok(None) | Err(_) => break n,
                }
            }
        })
        .await
        .unwrap_or(0);
        assert_eq!(missed, 1, "the new life is told once that messages may be missing");
    })
    .await;
}
