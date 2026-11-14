//! The access hook is asked for every session with that session's own protocol and direction: a hook that allows a
//! peer on one protocol and refuses it on another serves the first and closes the second with the denied code, whatever
//! the order they come in, in either direction and for a broadcast neighbour.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::large_futures,
    missing_docs
)]

mod vinc_common;

use std::sync::{Arc, Mutex};

use vinc::{Admission, DENIED, Direction, Endpoint, ErrorKind, Event, Hosted, Relay};
use vinc_common::{ECHO, SINK, bind, builder, eventually, serve_conn, within};
use vinc_crypto::NodeId;

/// The questions put to a hook, in order.
type Asked = Arc<Mutex<Vec<(Vec<u8>, Direction)>>>;

/// A hook that decides by protocol and direction alone and records every question put to it.
#[derive(Clone)]
struct Rules {
    allow: fn(&[u8], Direction) -> bool,
    asked: Asked,
}

impl Rules {
    fn new(allow: fn(&[u8], Direction) -> bool) -> Self {
        Self {
            allow,
            asked: Arc::default(),
        }
    }

    fn calls(&self) -> usize {
        self.asked.lock().unwrap().len()
    }
}

impl Admission for Rules {
    fn admit(&self, _peer: &NodeId, alpn: &[u8], dir: Direction) -> bool {
        self.asked.lock().unwrap().push((alpn.to_vec(), dir));
        (self.allow)(alpn, dir)
    }
}

/// Serve every session the endpoint accepts and record the protocol of each.
fn serve_all<H: Hosted + 'static, D: vinc::Discovery + 'static>(ep: &Endpoint<H, D>) -> Arc<Mutex<Vec<Vec<u8>>>> {
    let accepted = Arc::new(Mutex::new(Vec::new()));
    let (s, seen) = (ep.clone(), Arc::clone(&accepted));
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            let conn = i.into_connection();
            seen.lock().unwrap().push(conn.alpn().to_vec());
            nuclei::spawn_local(serve_conn(conn)).detach();
        }
    })
    .detach();
    accepted
}

/// The bytes a session echoes: the session is live and carries data.
async fn echoes<H: Hosted + 'static>(c: &vinc::Connection<H>) {
    let (mut tx, mut rx) = c.open_bi().await.unwrap();
    tx.write_all(b"x").await.unwrap();
    tx.finish().await.unwrap();
    assert_eq!(rx.read_to_end(8).await.unwrap(), b"x");
}

/// The peer that dialed sees the session closed by the other side with the denied code.
async fn denied<H: Hosted + 'static>(c: &vinc::Connection<H>) {
    let why = within(30, c.closed()).await;
    assert_eq!(
        why.kind(),
        ErrorKind::Closed {
            code: DENIED,
            by_peer: true
        },
        "the session was not closed with the denied code: {why:?}"
    );
}

/// A dial the other side refused: closed with the denied code once the session was up, or, when the refusal came
/// before the handshake finished, ended by the peer during it (a handshake close carries no code).
async fn refused_dial<H: Hosted + 'static>(r: vinc::Result<vinc::Connection<H>>) {
    match r {
        Ok(c) => denied(&c).await,
        Err(e) => assert_eq!(
            e.kind(),
            ErrorKind::Closed { code: 0, by_peer: true },
            "the dial failed for another reason: {e:?}"
        ),
    }
}

fn echo_only(alpn: &[u8], _dir: Direction) -> bool {
    alpn == ECHO
}

#[nuclei::test]
async fn a_protocol_the_hook_allows_is_served_and_one_it_refuses_is_closed_denied() {
    within(120, async {
        let hook = Rules::new(echo_only);
        let server = bind(builder().alpn(ECHO).alpn(SINK).acp(hook)).await;
        let accepted = serve_all(&server);
        let peer = bind(builder().alpn(ECHO).alpn(SINK)).await;

        let a = peer.connect(server.addr(), ECHO).await.unwrap();
        echoes(&a).await;
        let b = peer.connect(server.addr(), SINK).await.unwrap();
        denied(&b).await;
        echoes(&a).await;
        assert_eq!(
            *accepted.lock().unwrap(),
            [ECHO.to_vec()],
            "only the allowed session was accepted"
        );
    })
    .await;
}

#[nuclei::test]
async fn a_refusal_first_does_not_keep_the_peer_off_the_protocol_the_hook_allows() {
    within(120, async {
        let hook = Rules::new(echo_only);
        let server = bind(builder().alpn(ECHO).alpn(SINK).acp(hook)).await;
        let accepted = serve_all(&server);
        let peer = bind(builder().alpn(ECHO).alpn(SINK)).await;

        refused_dial(peer.connect(server.addr(), SINK).await).await;
        let a = peer.connect(server.addr(), ECHO).await.unwrap();
        echoes(&a).await;
        assert_eq!(
            *accepted.lock().unwrap(),
            [ECHO.to_vec()],
            "only the allowed session was accepted"
        );
    })
    .await;
}

#[nuclei::test]
async fn an_outbound_refusal_fails_the_dial_and_leaves_the_inbound_session_open() {
    within(120, async {
        let hook = Rules::new(|alpn, dir| !(alpn == SINK && dir == Direction::Outbound));
        let server = bind(builder().alpn(ECHO).alpn(SINK).acp(hook)).await;
        let accepted = serve_all(&server);
        let peer = bind(builder().alpn(ECHO).alpn(SINK)).await;
        serve_all(&peer);

        let a = peer.connect(server.addr(), ECHO).await.unwrap();
        echoes(&a).await;
        eventually(30, "the session is accepted", || async {
            accepted.lock().unwrap().len() == 1
        })
        .await;

        let err = server
            .connect(peer.addr(), SINK)
            .await
            .expect_err("the dial is refused");
        assert_eq!(err.kind(), ErrorKind::Refused, "{err:?}");
        echoes(&a).await;
    })
    .await;
}

#[nuclei::test]
async fn a_broadcast_neighbour_the_hook_allows_is_refused_as_an_application_peer() {
    within(120, async {
        let hook = Rules::new(|_, dir| dir == Direction::Gossip);
        let hub = bind(builder().seed(&[10; 32]).unwrap().alpn(ECHO).hub().acp(hook)).await;
        let accepted = serve_all(&hub);
        let relay = Relay::new(hub.id()).with_udp(hub.local_addr());
        let a = bind(builder().seed(&[1; 32]).unwrap().alpn(ECHO).relays([relay])).await;
        let b = bind(builder().seed(&[2; 32]).unwrap().alpn(ECHO).relays([relay])).await;
        b.join(b"t", &[]).await.unwrap();

        // the broadcast relation works: a message of `a` reaches `b` through the hub
        let mut got = false;
        for _ in 0..200 {
            a.publish(b"t", b"hello", None).await.unwrap();
            let b2 = b.clone();
            got = nuclei::time::timeout(std::time::Duration::from_millis(300), async move {
                loop {
                    match b2.event().await {
                        Some(Event::Message { .. }) => break true,
                        Some(_) => {}
                        None => break false,
                    }
                }
            })
            .await
            .unwrap_or(false);
            if got {
                break;
            }
        }
        assert!(got, "the hub did not carry the message of a neighbour the hook allows");

        refused_dial(a.connect(hub.addr(), ECHO).await).await;
        assert!(
            accepted.lock().unwrap().is_empty(),
            "the refused application session was accepted"
        );
    })
    .await;
}

#[nuclei::test]
async fn a_peer_refused_everything_is_refused_on_every_protocol() {
    within(120, async {
        let hook = Rules::new(|_, _| false);
        let server = bind(builder().alpn(ECHO).alpn(SINK).acp(hook)).await;
        let accepted = serve_all(&server);
        let peer = bind(builder().alpn(ECHO).alpn(SINK)).await;

        for alpn in [ECHO, SINK] {
            refused_dial(peer.connect(server.addr(), alpn).await).await;
        }
        assert!(accepted.lock().unwrap().is_empty());
    })
    .await;
}

#[nuclei::test]
async fn a_hook_is_asked_once_per_question_while_the_answer_stands() {
    within(120, async {
        let hook = Rules::new(|_, _| true);
        let server = bind(builder().alpn(ECHO).alpn(SINK).acp(hook.clone())).await;
        let accepted = serve_all(&server);
        let peer = bind(builder().alpn(ECHO).alpn(SINK)).await;

        let a = peer.connect(server.addr(), ECHO).await.unwrap();
        echoes(&a).await;
        assert_eq!(hook.calls(), 1, "one question for the peer's first session");
        let a2 = peer.connect(server.addr(), ECHO).await.unwrap();
        echoes(&a2).await;
        assert_eq!(
            hook.calls(),
            1,
            "a second session of the same protocol and direction adds none"
        );
        let _b = peer.connect(server.addr(), SINK).await.unwrap();
        eventually(30, "the sessions are accepted", || async {
            accepted.lock().unwrap().len() == 3
        })
        .await;
        assert_eq!(hook.calls(), 2, "the first session of a second protocol asks once more");

        // The same protocol in the other direction is another question.
        let _served = serve_all(&peer);
        let back = server.connect(peer.addr(), ECHO).await.unwrap();
        echoes(&back).await;
        assert_eq!(
            hook.calls(),
            3,
            "the first session in the other direction asks once more"
        );
        let last = hook.asked.lock().unwrap().last().cloned();
        assert_eq!(last, Some((ECHO.to_vec(), Direction::Outbound)));
    })
    .await;
}
