//! What survives a restart: a restarted endpoint resumes a session with a ticket from before.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::items_after_statements,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

#[macro_use]
mod vinc_common;

use vinc::ErrorKind;
use vinc_common::{ECHO, bind, eventually, serve_conn, within};

#[nuclei::test]
async fn a_restarted_endpoint_resumes_with_a_ticket_from_before_the_restart() {
    let server = bind(vinc_common::builder().seed(&[1; 32]).unwrap().alpn(ECHO)).await;
    let s = server.clone();
    nuclei::spawn_local(async move {
        while let Some(i) = s.accept().await {
            nuclei::spawn_local(serve_conn(i.into_connection())).detach();
        }
    })
    .detach();
    let first = bind(vinc_common::builder().seed(&[2; 32]).unwrap().alpn(ECHO)).await;
    within(120, async {
        let conn = first.connect(server.addr(), ECHO).await.unwrap();
        assert!(!conn.resumed(), "the first session cannot resume");
        let (mut tx, mut rx) = conn.open_bi().await.unwrap();
        tx.write_all(b"hello").await.unwrap();
        let mut got = [0u8; 5];
        rx.read_exact(&mut got).await.unwrap();
        // The server gives the ticket after the handshake: wait until the state holds one.
        let probe = bind(vinc_common::builder().seed(&[2; 32]).unwrap().alpn(ECHO)).await;
        let first2 = first.clone();
        let state = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
        let st = state.clone();
        eventually(30, "the state holds a ticket", move || {
            let (first, probe, st) = (first2.clone(), probe.clone(), st.clone());
            async move {
                let s = first.export_state().await.unwrap();
                let ok = probe.restore_state(&s).await.is_ok_and(|r| r.tickets >= 1);
                if ok {
                    *st.borrow_mut() = s;
                }
                ok
            }
        })
        .await;
        let state = state.borrow().clone();

        // The restart: the same identity on a new socket, with the state given back before the first dial.
        first.close().await;
        let second = bind(vinc_common::builder().seed(&[2; 32]).unwrap().alpn(ECHO)).await;
        // Bytes that are not a state change nothing and are refused.
        assert_eq!(
            second
                .restore_state(&state[..state.len() - 1])
                .await
                .unwrap_err()
                .kind(),
            ErrorKind::Config
        );
        assert_eq!(
            second.restore_state(b"nonsense").await.unwrap_err().kind(),
            ErrorKind::Config
        );
        let restored = second.restore_state(&state).await.unwrap();
        assert!(restored.tickets >= 1, "{restored:?}");
        assert!(restored.addresses <= 1);
        let conn = second.connect(server.addr(), ECHO).await.unwrap();
        assert!(conn.resumed(), "the first dial after the restart did not resume");

        // Sealed with the identity's key store, the state opens again, and altered bytes do not.
        let sealed = second.seal_state(&state).await.unwrap();
        assert_ne!(sealed, state);
        assert_eq!(second.unseal_state(&sealed).await.unwrap(), state);
        let mut bad = sealed.clone();
        let last = bad.len() - 1;
        bad[last] ^= 1;
        assert_eq!(second.unseal_state(&bad).await.unwrap_err().kind(), ErrorKind::Config);
    })
    .await;
}
