//! The facade's surface: access hook, errors, addresses, tags, protocols, discovery and the thread-safety of handles.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::zombie_processes,
    clippy::useless_conversion,
    clippy::manual_assert_eq,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

#[macro_use]
mod vinc_common;

use std::future::Future;
use std::net::SocketAddr;
use std::rc::Rc;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use vinc::{Admission, Direction, Discovery, ErrorKind, NodeAddr, NodeId, node_from_str, node_to_string};
use vinc_common::{ECHO, Svc, bind, client, node, register, serve_conn, within};

#[nuclei::test]
async fn addresses_round_trip() {
    let node = bind(vinc_common::builder().seed(&[9; 32]).unwrap()).await.id();
    let text = node_to_string(&node);
    assert_eq!(text.len(), 64);
    assert_eq!(node_from_str(&text).unwrap(), node);
    let a = NodeAddr::new(node)
        .with_direct("10.1.2.3:4433".parse().unwrap())
        .with_relay("https://relay.example/");
    assert_eq!(NodeAddr::parse(&a.ticket()).unwrap(), a);
    assert_eq!(NodeAddr::parse(&text).unwrap(), NodeAddr::new(node));
    for bad in ["", "zz", &text[..63], "00@x", &format!("{text}@nope")] {
        assert_eq!(NodeAddr::parse(bad).unwrap_err().kind(), ErrorKind::Config, "{bad}");
    }
}

#[nuclei::test]
async fn identity_is_the_seed_and_signs() {
    let a = bind(vinc_common::builder().seed(&[5; 32]).unwrap()).await;
    let b = bind(vinc_common::builder().seed(&[5; 32]).unwrap()).await;
    assert_eq!(a.id(), b.id());
    assert_eq!(a.public_key(), &a.id().bytes);
    let sig = within(30, a.sign(b"message")).await.unwrap();
    assert_eq!(sig.len(), 64);
    // Verify with the public key through the crypto crate the facade uses.
    vinc_crypto::identity::verify(vinc_crypto::IdentityAlg::Ed25519, a.public_key(), b"message", &sig).unwrap();
}

struct Gate {
    seen: Arc<AtomicUsize>,
    deny: Option<NodeId>,
}

impl Admission for Gate {
    fn admit(&self, peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        self.seen.fetch_add(1, Ordering::SeqCst);
        self.deny != Some(*peer)
    }
}

#[nuclei::test]
async fn access_hook_refuses_on_accept_and_on_dial_and_serves_gossip_checks() {
    let denied = bind(vinc_common::builder().seed(&[7; 32]).unwrap().alpn(ECHO)).await;
    let seen = Arc::new(AtomicUsize::new(0));
    let server = bind(vinc_common::builder().alpn(ECHO).acp(Gate {
        seen: Arc::clone(&seen),
        deny: Some(denied.id()),
    }))
    .await;
    let s = server.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();

    within(60, async {
        // A peer the hook allows connects and works.
        let ok = client().await;
        let c = ok.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = c.open_bi().await.unwrap();
        tx.write_all(b"ok").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(10).await.unwrap(), b"ok");
        assert!(seen.load(Ordering::SeqCst) >= 1);

        // The denied peer is closed out: its streams never work.
        match denied.connect(server.addr(), ECHO).await {
            Err(e) => assert!(
                matches!(
                    e.kind(),
                    ErrorKind::Refused | ErrorKind::Closed { .. } | ErrorKind::TimedOut
                ),
                "{e:?}"
            ),
            Ok(c) => {
                let r = async {
                    let (mut tx, mut rx) = c.open_bi().await?;
                    tx.write_all(b"no").await?;
                    tx.finish().await?;
                    rx.read_to_end(10).await
                }
                .await;
                assert!(r.is_err(), "the denied peer got an echo");
            }
        }

        // The same hook answers for a gossip neighbour.
        assert!(server.admit(&ok.id(), b"gossip", Direction::Gossip));
        assert!(!server.admit(&denied.id(), b"gossip", Direction::Gossip));
    })
    .await;
}

struct Book(SocketAddr, NodeId);
impl Discovery for Book {
    fn lookup(&self, node: &NodeId) -> impl Future<Output = Vec<SocketAddr>> {
        std::future::ready(if *node == self.1 { vec![self.0] } else { Vec::new() })
    }
}

#[nuclei::test]
async fn discovery_unreachable_and_self_dial_errors() {
    let server = bind(vinc_common::builder().seed(&[3; 32]).unwrap().alpn(ECHO)).await;
    let s = server.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            std::mem::forget(i);
        }
    })
    .detach();
    let book = Book(server.local_addr(), server.id());
    let client = bind(vinc_common::builder().discovery(book)).await;
    within(120, async {
        // No address given: discovery supplies it.
        let c = client.connect(server.id(), ECHO).await.unwrap();
        assert_eq!(c.remote(), server.id());
        // An unknown node with no address cannot be reached.
        let nobody = bind(vinc_common::builder().seed(&[4; 32]).unwrap()).await.id();
        assert_eq!(
            client.connect(nobody, ECHO).await.unwrap_err().kind(),
            ErrorKind::Unreachable
        );
        // A node does not dial itself.
        assert_eq!(
            client.connect(client.addr(), ECHO).await.unwrap_err().kind(),
            ErrorKind::Config
        );
        // A bad protocol name.
        assert_eq!(
            client.connect(server.addr(), b"").await.unwrap_err().kind(),
            ErrorKind::Config
        );
    })
    .await;
}

#[nuclei::test]
async fn registered_protocols_tags_and_alpn_limits() {
    let server = bind(vinc_common::builder()).await;
    let client = bind(vinc_common::builder()).await;
    within(120, async {
        for a in [&b"t/0"[..], b"t/1", b"t/2", b"t/3", b"t/4", b"t/5", b"t/6", b"t/7"] {
            let a: &'static [u8] = Box::leak(a.to_vec().into_boxed_slice());
            register(&server, Rc::new(Svc(a))).await.unwrap();
        }
        // A ninth, a repeat and a bad name are refused.
        assert_eq!(
            register(&server, Rc::new(Svc(b"t/8"))).await.unwrap_err().kind(),
            ErrorKind::Config
        );
        assert_eq!(
            register(&server, Rc::new(Svc(b"t/0"))).await.unwrap_err().kind(),
            ErrorKind::Config
        );

        // Two protocols to the same peer: the second is a sub-session.
        let first = client.connect(server.addr(), b"t/0").await.unwrap();
        let second = first.open_protocol(b"t/1").await.unwrap();
        assert_eq!(second.alpn(), b"t/1");
        assert_eq!(second.remote(), first.remote());
        assert_eq!(client.peers().await.unwrap(), vec![server.id()]);

        // A tag names the protocol per stream; the service here does not speak tags, so only the framing is checked.
        let (mut tx, _rx) = first.open_bi_tagged(b"pushlog").await.unwrap();
        assert_eq!(first.open_bi_tagged(b"").await.unwrap_err().kind(), ErrorKind::Config);
        assert_eq!(
            first.open_bi_tagged(&[1u8; 65]).await.unwrap_err().kind(),
            ErrorKind::Config
        );
        tx.reset(9).await;
    })
    .await;
}

#[nuclei::test]
async fn close_peer_and_shutdown() {
    let server = node().await;
    let client = client().await;
    within(120, async {
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        client.close_peer(&server.id()).await;
        let why = c.closed().await;
        assert!(matches!(why.kind(), ErrorKind::Closed { .. }), "{why:?}");
        assert_eq!(c.open_bi().await.unwrap_err().kind(), why.kind());
        let c2 = client.connect(server.addr(), ECHO).await.unwrap();
        client.close().await;
        assert!(c2.closed().await.kind() != ErrorKind::Refused);
        assert_eq!(
            client.connect(server.addr(), ECHO).await.unwrap_err().kind(),
            ErrorKind::Shutdown
        );
    })
    .await;
}

/// A revoke ends every session with the peer within the call, a transfer in flight included; the peer stays out,
/// whichever side dials and whatever the access hook says, until the revocation is lifted.
#[nuclei::test]
async fn a_revoked_peer_loses_every_session_and_stays_out() {
    let server = node().await;
    let client = client().await;
    within(120, async {
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = c.open_bi().await.unwrap();
        tx.write_all(&[7u8; 4096]).await.unwrap();
        let mut back = [0u8; 4096];
        rx.read_exact(&mut back).await.unwrap();

        assert!(!server.is_revoked(&client.id()));
        server.revoke(&client.id()).await.unwrap();
        assert!(server.is_revoked(&client.id()));
        assert!(
            !server.admit(&client.id(), ECHO, Direction::Gossip),
            "a revoked peer is no neighbour either"
        );
        let why = c.closed().await;
        assert_eq!(
            why.kind(),
            ErrorKind::Closed {
                code: vinc::DENIED,
                by_peer: true
            },
            "the session ended with the denied code"
        );
        assert!(
            tx.write_all(&[7u8; 4096]).await.is_err(),
            "the transfer in flight ended with it"
        );

        // The revoked peer dials again: no session with it stays up.
        if let Ok(again) = client.connect(server.addr(), ECHO).await {
            let why = again.closed().await;
            assert!(
                matches!(why.kind(), ErrorKind::Closed { .. } | ErrorKind::Refused),
                "a session with a revoked peer came up: {why:?}"
            );
        }
        // Nor does the revoking side reach it.
        assert!(server.connect(client.addr(), ECHO).await.is_err());

        // Revoking twice changes nothing; lifting it lets the peer in again.
        server.revoke(&client.id()).await.unwrap();
        assert!(server.unrevoke(&client.id()));
        assert!(!server.unrevoke(&client.id()));
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = c.open_bi().await.unwrap();
        tx.write_all(b"again").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(64).await.unwrap(), b"again");
    })
    .await;
}

/// The deny an endpoint gave while a peer was revoked does not outlive the revocation: the peer connects at once.
#[nuclei::test]
async fn a_peer_connects_at_once_after_its_revocation_is_lifted() {
    let server = node().await;
    let client = client().await;
    within(20, async {
        server.revoke(&client.id()).await.unwrap();
        if let Ok(c) = client.connect(server.addr(), ECHO).await {
            assert!(matches!(
                c.closed().await.kind(),
                ErrorKind::Closed { .. } | ErrorKind::Refused
            ));
        }
        assert!(server.unrevoke(&client.id()));
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = c.open_bi().await.unwrap();
        tx.write_all(b"now").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(64).await.unwrap(), b"now");
    })
    .await;
}

/// A peer that dialed while revoked is let in on its next dial once the revocation is lifted: the deny the endpoint
/// cached for it then (30 s) goes with the revocation.
#[nuclei::test]
async fn an_unrevoked_peer_is_admitted_at_once_after_a_denied_dial() {
    let server = node().await;
    let client = client().await;
    within(20, async {
        server.revoke(&client.id()).await.unwrap();
        if let Ok(refused) = client.connect(server.addr(), ECHO).await {
            let why = refused.closed().await;
            assert!(
                matches!(why.kind(), ErrorKind::Closed { .. } | ErrorKind::Refused),
                "a session with a revoked peer came up: {why:?}"
            );
        }
        assert!(server.unrevoke(&client.id()));
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = c.open_bi().await.unwrap();
        tx.write_all(b"back").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(64).await.unwrap(), b"back");
    })
    .await;
}

/// An allowlist the test edits while the server runs.
struct Listed(Arc<std::sync::atomic::AtomicBool>);

impl Admission for Listed {
    fn admit(&self, _peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        self.0.load(Ordering::SeqCst)
    }
}

/// A peer the hook refused is let in on its next dial once the host says the hook's answer changed: the cached deny
/// goes, and the server serves the session the dialer was told is up.
#[nuclei::test]
async fn a_peer_the_hook_refused_is_admitted_at_once_after_admission_changed() {
    let listed = Arc::new(std::sync::atomic::AtomicBool::new(false));
    let server = bind(vinc_common::builder().alpn(ECHO).acp(Listed(Arc::clone(&listed)))).await;
    let s = server.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    let client = client().await;
    within(20, async {
        if let Ok(refused) = client.connect(server.addr(), ECHO).await {
            let why = refused.closed().await;
            assert!(
                matches!(why.kind(), ErrorKind::Closed { .. } | ErrorKind::Refused),
                "a session the hook refused came up: {why:?}"
            );
        }
        listed.store(true, Ordering::SeqCst);
        server.admission_changed(&client.id());
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, mut rx) = c.open_bi().await.unwrap();
        tx.write_all(b"listed").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(64).await.unwrap(), b"listed");
    })
    .await;
}

/// A dial to an address nobody answers at ends inside the builder's connect timeout, not at the transport's own.
#[nuclei::test]
async fn a_dial_nobody_answers_ends_inside_the_connect_timeout() {
    let client = bind(vinc_common::builder().alpn(ECHO).connect_timeout(std::time::Duration::from_millis(800))).await;
    within(60, async {
        let silent = std::net::UdpSocket::bind("127.0.0.1:0").unwrap();
        let t0 = std::time::Instant::now();
        let e = client
            .connect(NodeAddr::new(node().await.id()).with_direct(silent.local_addr().unwrap()), ECHO)
            .await
            .unwrap_err();
        assert_eq!(e.kind(), ErrorKind::TimedOut, "{e:?}");
        assert!(t0.elapsed() < std::time::Duration::from_secs(5), "{:?}", t0.elapsed());
    })
    .await;
}
