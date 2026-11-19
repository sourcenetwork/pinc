//! The facade's revoke and access check from the revoking side: its own handles end within the call, the revocation
//! table holds its bound and says so, and the access cache keeps hundreds of peers.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::large_futures,
    clippy::items_after_statements,
    missing_docs
)]

mod pinc_common;

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use pinc::{Admission, DENIED, Direction, ErrorKind, Limits, REVOKED_MAX};
use pinc_common::{ECHO, bind, builder, client, poll_drop, serve_conn, within};
use pinc_crypto::{IdentityAlg, NodeId};

/// Every call of the access hook, per peer.
#[derive(Clone, Default)]
struct Counting(Arc<Mutex<HashMap<NodeId, u32>>>);

impl Admission for Counting {
    fn admit(&self, peer: &NodeId, _alpn: &[u8], _dir: Direction) -> bool {
        *self.0.lock().unwrap().entry(*peer).or_default() += 1;
        true
    }
}

#[nuclei::test]
async fn the_revoking_sides_own_handles_end_within_the_revoke_call() {
    within(60, async {
        let server = bind(builder().alpn(ECHO)).await;
        let peer = client().await;
        let c = peer.connect(server.addr(), ECHO).await.unwrap();
        let (mut ctx, _crx) = c.open_bi().await.unwrap();
        ctx.write_all(b"hello").await.unwrap();

        let sconn = server.accept().await.unwrap().into_connection();
        let (mut stx, mut srx) = sconn.accept_bi().await.unwrap();
        let mut got = [0u8; 5];
        srx.read_exact(&mut got).await.unwrap();
        assert_eq!(&got, b"hello");

        // in flight on the revoking side: a read that waits for more, a write the peer never drains, and accepts of
        // streams the peer has not opened
        let read = nuclei::spawn_local(async move {
            let mut b = [0u8; 16];
            srx.read(&mut b).await.is_err()
        });
        let write = nuclei::spawn_local(async move { stx.write_all(&vec![1u8; 32 << 20]).await.is_err() });
        let (a1, a2) = (sconn.clone(), sconn.clone());
        let accept_bi = nuclei::spawn_local(async move { a1.accept_bi().await.is_err() });
        let accept_uni = nuclei::spawn_local(async move { a2.accept_uni().await.is_err() });
        // a pending accept of the endpoint serves the next peer, not the revoked one
        let s = server.clone();
        let next = nuclei::spawn_local(async move { s.accept().await.is_some() });
        nuclei::time::sleep(std::time::Duration::from_millis(50)).await;

        server.revoke(&peer.id()).await.unwrap();

        // the connection and what it opens end at once, whatever the peer does
        let why = poll_drop(sconn.closed(), 0)
            .await
            .expect("the connection ended with the revoke");
        assert_eq!(
            why.kind(),
            ErrorKind::Closed {
                code: DENIED,
                by_peer: false
            }
        );
        assert!(poll_drop(sconn.open_bi(), 0).await.expect("open ends at once").is_err());
        for (what, task) in [
            ("read", read),
            ("write", write),
            ("accept_bi", accept_bi),
            ("accept_uni", accept_uni),
        ] {
            assert_eq!(
                poll_drop(task, 5).await,
                Some(true),
                "the pending {what} ended with the revoke"
            );
        }
        assert!(
            poll_drop(next, 5).await.is_none(),
            "the endpoint's accept is still waiting for the next peer"
        );
    })
    .await;
}

fn id_of(i: u32) -> NodeId {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&i.to_be_bytes());
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    }
}

#[nuclei::test]
async fn the_revocation_table_holds_its_bound_and_says_so() {
    within(120, async {
        let server = bind(builder().alpn(ECHO)).await;
        for i in 0..REVOKED_MAX as u32 {
            server.revoke(&id_of(i)).await.unwrap();
        }
        let extra = id_of(REVOKED_MAX as u32);
        let err = server.revoke(&extra).await.unwrap_err();
        assert_eq!(err.kind(), ErrorKind::Busy, "{err:?}");
        assert_ne!(err.message(), "");
        assert!(!server.is_revoked(&extra), "a revoke that failed bars nobody");
        assert!(server.is_revoked(&id_of(0)) && server.is_revoked(&id_of(REVOKED_MAX as u32 - 1)));

        // a peer that is already barred can be revoked again, and room freed by a lifted revocation is used
        server.revoke(&id_of(0)).await.unwrap();
        assert!(server.unrevoke(&id_of(7)));
        server.revoke(&extra).await.unwrap();
        assert!(server.is_revoked(&extra));
        assert!(!server.is_revoked(&id_of(7)));
        let barred = (0..=REVOKED_MAX as u32)
            .filter(|i| server.is_revoked(&id_of(*i)))
            .count();
        assert_eq!(barred, REVOKED_MAX);
    })
    .await;
}

/// `peers` distinct nodes each connect to a server, move a byte and leave, one after another; then each does it again.
/// The server's hook is asked once per peer if its cache keeps them all for the 30 s an answer counts.
async fn reconnecting_peers(peers: u32, server_limits: Limits) -> HashMap<NodeId, u32> {
    let counting = Counting::default();
    let server = bind(builder().alpn(ECHO).limits(server_limits).acp(counting.clone())).await;
    let s = server.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    let small = Limits {
        connections: 1,
        pool_chunks: 8,
        ..Limits::default()
    };
    for _round in 0..2 {
        for n in 0..peers {
            let mut seed = [0u8; 32];
            seed[..4].copy_from_slice(&(n + 1).to_be_bytes());
            let ep = bind(builder().seed(&seed).unwrap().alpn(ECHO).limits(small)).await;
            let c = ep.connect(server.addr(), ECHO).await.unwrap();
            let (mut tx, mut rx) = c.open_bi().await.unwrap();
            tx.write_all(b"x").await.unwrap();
            tx.finish().await.unwrap();
            assert_eq!(rx.read_to_end(8).await.unwrap(), b"x");
            c.close(0).await;
            ep.close().await;
        }
    }
    counting.0.lock().unwrap().clone()
}

#[nuclei::test]
async fn the_access_cache_keeps_hundreds_of_peers_so_a_reconnecting_peer_is_not_asked_twice() {
    within(300, async {
        let seen = reconnecting_peers(300, Limits::default()).await;
        assert_eq!(seen.len(), 300, "every peer was checked");
        let twice = seen.values().filter(|n| **n > 1).count();
        assert_eq!(
            twice, 0,
            "{twice} of 300 reconnecting peers were asked again within the 30 s of a cached answer"
        );
    })
    .await;
}

/// The control: with room for 40 cached answers the same run asks again, so the test above fails when the tables are
/// small.
#[nuclei::test]
async fn with_small_tables_the_same_run_asks_again() {
    within(300, async {
        let small = Limits {
            connections: 4,
            pool_chunks: 8,
            ..Limits::default()
        };
        let seen = reconnecting_peers(300, small).await;
        let twice = seen.values().filter(|n| **n > 1).count();
        assert!(twice > 0, "the run is insensitive to the size of the cache");
    })
    .await;
}
