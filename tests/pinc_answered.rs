//! A connection handed over before its peer answered says when the peer is heard: a dial with a cached allow, which is
//! reported before its handshake, and a protocol opened over a held session, which has no handshake. `answered`
//! returns once the peer is heard and fails when the connection ends first, as one to a peer that stopped does.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::needless_continue)]

#[macro_use]
mod pinc_common;

use pinc::{Connection, ErrorKind, Hosted, NodeAddr};
use pinc_common::{ECHO, SINK, serve_conn, within};

/// One message echoed on a fresh stream of `conn`.
async fn echo_once<H: Hosted + 'static>(conn: &Connection<H>) {
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"ping").await.unwrap();
    tx.finish().await.unwrap();
    let mut got = [0u8; 4];
    rx.read_exact(&mut got).await.unwrap();
    assert_eq!(&got, b"ping");
}

/// A peer serving the echo and sink protocols, run by the returned task: dropping the task stops the peer without a
/// word, as a killed process. The task owns the tasks serving its sessions, which drive the endpoint too, so they
/// end with it and nothing drives its socket any more.
macro_rules! peer {
    () => {{
        let ep = lo_endpoint!(pinc_common::builder().alpn(ECHO).alpn(SINK));
        let to: NodeAddr = ep.addr();
        let (run, acc) = (ep.clone(), ep);
        let task = nuclei::spawn_local(async move {
            let serve = async move {
                let mut served = Vec::new();
                while let Some(inc) = acc.accept().await {
                    served.push(nuclei::spawn_local(serve_conn(inc.into_connection())));
                }
            };
            nuclei::select! {
                _r = run.run() => {},
                () = serve => {},
            }
        });
        (to, task)
    }};
}

/// Whether `e` is how a dial to a peer that stopped ends.
fn stopped_peer(e: &pinc::Error) -> bool {
    matches!(e.kind(), ErrorKind::TimedOut | ErrorKind::Unreachable)
}

#[nuclei::test]
async fn a_dial_to_a_running_peer_is_answered_and_so_is_its_redial() {
    within(30, async {
        let (to, _task) = peer!();
        let client = pinc_common::client().await;
        let first = client.connect(to.clone(), ECHO).await.unwrap();
        first.answered().await.unwrap();
        assert!(first.is_answered());
        echo_once(&first).await;
        first.close(0).await;
        let _ = first.closed().await;
        // The allow is cached now: the redial is handed over before its handshake and answered when it ends.
        let again = client.connect(to, ECHO).await.unwrap();
        again.answered().await.unwrap();
        assert!(again.is_answered());
        echo_once(&again).await;
    })
    .await;
}

#[nuclei::test]
async fn a_redial_handed_over_before_its_handshake_reports_resumed_once_the_peer_answers() {
    within(30, async {
        let (to, _task) = peer!();
        let client = pinc_common::client().await;
        let first = client.connect(to.clone(), ECHO).await.unwrap();
        first.answered().await.unwrap();
        assert!(!first.resumed(), "the first dial has no ticket to resume with");
        echo_once(&first).await;
        first.close(0).await;
        let _ = first.closed().await;
        let again = client.connect(to, ECHO).await.unwrap();
        assert!(
            !again.is_answered(),
            "the redial was not handed over before its handshake"
        );
        again.answered().await.unwrap();
        assert!(again.resumed(), "the redial resumed with the ticket of the first");
    })
    .await;
}

#[nuclei::test]
async fn a_protocol_opened_over_a_session_is_answered_once_the_peer_answers() {
    within(30, async {
        let (to, _task) = peer!();
        let client = pinc_common::client().await;
        let parent = client.connect(to, ECHO).await.unwrap();
        echo_once(&parent).await;
        let sub = parent.open_protocol(SINK).await.unwrap();
        let (mut tx, mut rx) = sub.open_bi().await.unwrap();
        tx.write_all(b"x").await.unwrap();
        tx.finish().await.unwrap();
        sub.answered().await.unwrap();
        assert!(sub.is_answered());
        // The sink's answer: the length and the hash of what it read.
        let mut reply = [0u8; 40];
        rx.read_exact(&mut reply).await.unwrap();
        assert_eq!(u64::from_le_bytes(reply[..8].try_into().unwrap()), 1);
    })
    .await;
}

/// The limit is above both ends of the dial: about 3 s when the node is not thin (the dial ends after its fourth
/// unanswered first flight), and the 60 s handshake limit when a stalled host made the node thin (it measured a round
/// trip of 250 ms or more, and the early end does not apply to it). A connect timeout does not bound it: that ends
/// a dial only until it is handed over, and this one is handed over at once.
#[nuclei::test]
async fn a_dial_to_a_peer_that_stopped_is_handed_over_but_never_answered() {
    within(120, async {
        let (to, task) = peer!();
        let client = pinc_common::client().await;
        let first = client.connect(to.clone(), ECHO).await.unwrap();
        echo_once(&first).await;
        first.close(0).await;
        let _ = first.closed().await;
        drop(task);
        // The allow is cached, so the dial is handed over at once, before anything could come back.
        let down = client
            .connect(to, ECHO)
            .await
            .expect("a dial with a cached allow is handed over before its handshake");
        assert!(!down.is_answered(), "a dial to a stopped peer counts as answered");
        let e = down.answered().await.unwrap_err();
        assert!(stopped_peer(&e), "{e:?}");
        assert!(!down.is_answered());
    })
    .await;
}

#[nuclei::test]
async fn a_protocol_opened_over_a_session_whose_peer_stopped_is_never_answered() {
    within(120, async {
        let (to, task) = peer!();
        let client = pinc_common::client().await;
        let parent = client.connect(to, ECHO).await.unwrap();
        echo_once(&parent).await;
        drop(task);
        // The parent was heard a moment ago, so the protocol opens over it at once, with no round trip.
        let sub = parent.open_protocol(SINK).await.unwrap();
        assert!(
            !sub.is_answered(),
            "a protocol opened over a session to a stopped peer counts as answered"
        );
        let (mut tx, _rx) = sub.open_bi().await.unwrap();
        let _ = tx.write_all(b"x").await;
        let e = sub.answered().await.unwrap_err();
        assert!(!sub.is_answered(), "{e:?}");
    })
    .await;
}
