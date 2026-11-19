//! Revocation through the facade, on the revoking side: every session with the peer has ended by the time `revoke`
//! returns, a transfer in flight and a sub-session included, and nobody else is touched; the revocation table holds
//! its bound; the endpoint keeps the access answers of hundreds of peers, so none is asked twice inside the cache's
//! life. On nuclei.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

mod pinc_common;

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use pinc::{Admission, Connection, DENIED, Direction, ErrorKind, Hosted, Limits, NodeId, REVOKED_MAX};
use pinc_common::{ECHO, GEN, SINK, bind, bind_idle, builder, eventually, serve_conn, within};

/// Counts the hook's answers per peer.
#[derive(Clone, Default)]
struct Hook {
    asked: Rc<RefCell<HashMap<NodeId, usize>>>,
}

impl Admission for Hook {
    fn admit(&self, peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        *self.asked.borrow_mut().entry(*peer).or_default() += 1;
        true
    }
}

fn closed_by_revoke(kind: ErrorKind) -> bool {
    kind == ErrorKind::Closed {
        code: DENIED,
        by_peer: false,
    }
}

#[nuclei::test]
async fn a_revoke_ends_every_session_with_the_peer_within_the_call_a_transfer_included() {
    let hook = Hook::default();
    let server = bind(builder().alpn(ECHO).alpn(GEN).alpn(SINK).acp(hook.clone())).await;
    let held: Rc<RefCell<Vec<Connection<_>>>> = Rc::default();
    let (s, h) = (server.clone(), Rc::clone(&held));
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            let c = i.into_connection();
            h.borrow_mut().push(c.clone());
            nuclei::spawn_local(serve_conn(c)).detach();
        }
    })
    .detach();
    let client = bind(builder().alpn(ECHO).alpn(GEN)).await;
    let bystander = bind(builder().alpn(ECHO)).await;

    within(120, async {
        // Two sessions with the client: an echo, and a generator streaming 1 GiB that is mid-flight at the revoke.
        let echo = client.connect(server.addr(), ECHO).await.unwrap();
        let generator = echo.open_protocol(GEN).await.unwrap();
        let (mut gtx, mut grx) = generator.open_bi().await.unwrap();
        let mut req = 7u64.to_le_bytes().to_vec();
        req.extend_from_slice(&(1u64 << 30).to_le_bytes());
        gtx.write_all(&req).await.unwrap();
        let mut buf = vec![0u8; 64 * 1024];
        let mut got = 0u64;
        while got < 4 * 1024 * 1024 {
            got += grx.read(&mut buf).await.unwrap().unwrap() as u64;
        }
        let other = bystander.connect(server.addr(), ECHO).await.unwrap();
        eventually(10, "the server holds three sessions", || {
            let n = held.borrow().len();
            async move { n == 3 }
        })
        .await;

        server.revoke(&client.id()).await.unwrap();

        // Within the call: the server has no session with the client, and its handles report the revoke.
        assert_eq!(server.peers().await.unwrap(), vec![bystander.id()]);
        let theirs: Vec<_> = held
            .borrow()
            .iter()
            .filter(|c| c.remote() == client.id())
            .cloned()
            .collect();
        assert_eq!(theirs.len(), 2);
        for c in &theirs {
            let why = c.close_reason().expect("a session of the revoked peer is still open");
            assert!(closed_by_revoke(why.kind()), "{why:?}");
            assert!(c.open_bi().await.is_err());
        }
        assert!(server.is_revoked(&client.id()));
        assert!(!server.admit(&client.id(), b"gossip", Direction::Gossip));
        // The server dials the revoked peer: no session comes up.
        assert!(server.connect(client.addr(), ECHO).await.is_err());

        // The client hears the close and its transfer stops short.
        let end = loop {
            match grx.read(&mut buf).await {
                Ok(Some(n)) => got += n as u64,
                Ok(None) => panic!("the transfer finished after the revoke"),
                Err(e) => break e,
            }
        };
        assert!(got < 1 << 30);
        assert_eq!(
            end.kind(),
            ErrorKind::Closed {
                code: DENIED,
                by_peer: true
            },
            "{end:?}"
        );
        assert_ne!(echo.closed().await.kind(), ErrorKind::Shutdown);

        // The client comes back while the server still caches its earlier allow: it gets no working session.
        match client.connect(server.addr(), ECHO).await {
            Err(e) => assert!(
                matches!(
                    e.kind(),
                    ErrorKind::Refused | ErrorKind::Closed { .. } | ErrorKind::TimedOut | ErrorKind::Unreachable
                ),
                "{e:?}"
            ),
            Ok(c) => {
                let r = async {
                    let (mut tx, mut rx) = c.open_bi().await?;
                    tx.write_all(b"back").await?;
                    tx.finish().await?;
                    rx.read_to_end(10).await
                }
                .await;
                assert!(r.is_err(), "the revoked peer got an echo");
            }
        }
        assert!(!server.peers().await.unwrap().contains(&client.id()));

        // Nobody else was touched.
        let (mut tx, mut rx) = other.open_bi().await.unwrap();
        tx.write_all(b"still").await.unwrap();
        tx.finish().await.unwrap();
        assert_eq!(rx.read_to_end(10).await.unwrap(), b"still");
    })
    .await;
}

#[nuclei::test]
async fn the_revocation_table_holds_its_bound_and_refuses_the_next_peer() {
    let server = bind(builder().alpn(ECHO)).await;
    within(60, async {
        let id = |i: u64| {
            let mut n = server.id();
            n.bytes[..8].copy_from_slice(&i.to_le_bytes());
            n.bytes[8] ^= 0xA5;
            n
        };
        for i in 0..REVOKED_MAX as u64 {
            server.revoke(&id(i)).await.unwrap();
        }
        // Revoking a revoked peer again is no change and no error.
        server.revoke(&id(0)).await.unwrap();
        let next = id(REVOKED_MAX as u64);
        assert_eq!(server.revoke(&next).await.unwrap_err().kind(), ErrorKind::Busy);
        assert!(!server.is_revoked(&next));
        assert!(server.is_revoked(&id(REVOKED_MAX as u64 - 1)));
    })
    .await;
}

/// Hundreds of peers: each is asked once, and a second session within the cache's life is not asked
/// again, so no answer was evicted.
const PEERS: u64 = 300;
const BATCH: u64 = 30;

fn tiny() -> Limits {
    Limits {
        connections: 1,
        pool_chunks: 16,
        stream_window: 32 * 1024,
        streams: 2,
        ..Limits::default()
    }
}

async fn echo_once<H: Hosted>(conn: &Connection<H>) {
    let (mut tx, mut rx) = conn.open_bi().await.unwrap();
    tx.write_all(b"hi").await.unwrap();
    tx.finish().await.unwrap();
    assert_eq!(rx.read_to_end(10).await.unwrap(), b"hi");
}

async fn visit(seed: u64, to: pinc::NodeAddr) {
    let mut s = [0u8; 32];
    s[..8].copy_from_slice(&seed.to_le_bytes());
    s[31] = 0x5E;
    let ep = bind_idle(builder().seed(&s).unwrap().limits(tiny())).await;
    let c = ep.connect(to, ECHO).await.unwrap();
    echo_once(&c).await;
    c.close(0).await;
}

#[nuclei::test]
async fn the_endpoint_keeps_the_access_answers_of_hundreds_of_peers() {
    let hook = Hook::default();
    let server = bind(builder().alpn(ECHO).acp(hook.clone()).limits(Limits {
        connections: 64,
        ..Limits::default()
    }))
    .await;
    let s = server.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    within(240, async {
        let started = std::time::Instant::now();
        for round in 0..2 {
            for b in 0..PEERS / BATCH {
                let tasks: Vec<_> = (b * BATCH..(b + 1) * BATCH)
                    .map(|i| nuclei::spawn_local(visit(i, server.addr())))
                    .collect();
                for t in tasks {
                    t.await;
                }
            }
            let asked = hook.asked.borrow();
            assert_eq!(asked.len() as u64, PEERS, "round {round}");
        }
        // Both rounds ran inside the 30 s an answer is cached (less its 5 s re-ask), so a peer asked twice had its
        // answer evicted.
        assert!(
            started.elapsed().as_secs() < 25,
            "too slow to tell: {:?}",
            started.elapsed()
        );
        let twice: Vec<_> = hook.asked.borrow().values().copied().filter(|n| *n > 1).collect();
        assert!(twice.is_empty(), "{} peers were asked again", twice.len());
    })
    .await;
}
