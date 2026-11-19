//! `RecvStream::stop` tells the peer: its writer fails with the code, and the stream resets.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

mod pinc_common;

use pinc::ErrorKind;
use pinc_common::{ECHO, bind, within};

#[nuclei::test]
async fn a_stopped_reader_makes_the_writer_fail_with_its_code() {
    within(60, async {
        let server = bind(pinc_common::builder().alpn(ECHO)).await;
        let client = bind(pinc_common::builder().alpn(ECHO)).await;
        let c = client.connect(server.addr(), ECHO).await.unwrap();
        let (mut tx, _rx) = c.open_bi().await.unwrap();
        tx.write_all(b"first").await.unwrap();
        let s = server.accept().await.unwrap().into_connection();
        let (_stx, mut srx) = s.accept_bi().await.unwrap();
        let mut got = [0u8; 5];
        srx.read_exact(&mut got).await.unwrap();
        srx.stop(77).await;
        assert_eq!(
            srx.read_exact(&mut got).await.unwrap_err().kind(),
            ErrorKind::Stopped(77)
        );
        // The writer keeps writing until the stop reaches it, then fails with the code.
        let chunk = vec![1u8; 8192];
        let err = loop {
            if let Err(e) = tx.write_all(&chunk).await {
                break e;
            }
        };
        assert_eq!(err.kind(), ErrorKind::Stopped(77), "{err:?}");
        // The connection itself is fine.
        let (mut tx2, _rx2) = c.open_bi().await.unwrap();
        tx2.write_all(b"ok").await.unwrap();
        let (_t, mut r) = s.accept_bi().await.unwrap();
        let mut two = [0u8; 2];
        r.read_exact(&mut two).await.unwrap();
        assert_eq!(&two, b"ok");
    })
    .await;
}
