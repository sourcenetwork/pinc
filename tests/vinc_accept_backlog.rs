//! A burst of dials against an application slower than the burst (vinc#436): the endpoint pushes back on the first
//! flights the accept queue has no room for, so no session is closed as busy after its handshake and every dialer is
//! served once the application takes the sessions before it.
#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic, clippy::indexing_slicing)]

mod vinc_common;

use std::cell::Cell;
use std::rc::Rc;
use std::time::Duration;

use vinc::Limits;
use vinc_common::{ECHO, bind, join_all, serve_conn, within};

/// The accept queue of the server.
const ROOM: usize = 4;
/// Dialers at once: four times the queue.
const DIALERS: usize = 16;

/// A dialer's endpoint: one session with one stream.
fn small() -> Limits {
    Limits {
        connections: 1,
        pool_chunks: 16,
        stream_window: 32 * 1024,
        streams: 2,
        ..Limits::default()
    }
}

#[nuclei::test]
async fn a_burst_past_the_accept_queue_loses_no_session() {
    within(120, async {
        let limits = Limits {
            accept_sessions: ROOM,
            ..Limits::default()
        };
        let server = bind(vinc_common::builder().alpn(ECHO).limits(limits)).await;
        let accepted = Rc::new(Cell::new(0usize));
        let (s, n) = (server.clone(), Rc::clone(&accepted));
        nuclei::spawn_local(async move {
            // The application takes a session every 50 ms: the burst's handshakes finish long before it has room.
            while let Some(i) = s.accept().await {
                n.set(n.get() + 1);
                nuclei::spawn_local(serve_conn(i.into_connection())).detach();
                nuclei::time::sleep(Duration::from_millis(50)).await;
            }
        })
        .detach();
        let addr = server.addr();
        let results = join_all((0..DIALERS).map(|i| {
            let addr = addr.clone();
            async move {
                let ep = bind(vinc_common::builder().limits(small())).await;
                let conn = ep
                    .connect(addr, ECHO)
                    .await
                    .map_err(|e| format!("dialer {i}: connect: {e:?}"))?;
                let (mut tx, mut rx) = conn.open_bi().await.map_err(|e| format!("dialer {i}: open: {e:?}"))?;
                let payload = [u8::try_from(i).unwrap(); 64];
                tx.write_all(&payload)
                    .await
                    .map_err(|e| format!("dialer {i}: write: {e:?}"))?;
                tx.finish().await.map_err(|e| format!("dialer {i}: finish: {e:?}"))?;
                let got = rx
                    .read_to_end(1024)
                    .await
                    .map_err(|e| format!("dialer {i}: read: {e:?}"))?;
                if got != payload {
                    return Err(format!("dialer {i}: the echo differs"));
                }
                match conn.close_reason() {
                    None => Ok(()),
                    Some(e) => Err(format!("dialer {i}: closed: {e:?}")),
                }
            }
        }))
        .await;
        let failed: Vec<_> = results.into_iter().filter_map(Result::err).collect();
        assert!(
            failed.is_empty(),
            "{} of {DIALERS} dialers lost their session: {failed:?}",
            failed.len()
        );
        assert_eq!(accepted.get(), DIALERS, "the application took every session once");
    })
    .await;
}
