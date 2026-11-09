//! `RecvStream::stop` tells the peer: its writer fails with the code, and the stream resets.
#![allow(
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing
)]

mod vinc_common;

use vinc::{ErrorKind, Vinc};
use vinc_common::{ECHO, lo, watchdog};

fn node() -> vinc::blocking::Endpoint {
    Vinc::builder()
        .alpn(ECHO)
        .bind_addr(lo())
        .bind_blocking()
        .unwrap()
        .blocking()
}

#[test]
fn a_stopped_reader_makes_the_writer_fail_with_its_code() {
    watchdog(60);
    let (server, client) = (node(), node());
    let c = client.connect(server.addr(), ECHO).unwrap();
    let (mut tx, _rx) = c.open_bi().unwrap();
    tx.write_all(b"first").unwrap();
    let (_, _, s) = server.accept().unwrap();
    let (_stx, mut srx) = s.accept_bi().unwrap();
    let mut got = [0u8; 5];
    srx.read_exact(&mut got).unwrap();
    srx.stop(77);
    assert_eq!(srx.read_exact(&mut got).unwrap_err().kind(), ErrorKind::Stopped(77));
    // The writer keeps writing until the stop reaches it, then fails with the code.
    let chunk = vec![1u8; 8192];
    let err = loop {
        if let Err(e) = tx.write_all(&chunk) {
            break e;
        }
    };
    assert_eq!(err.kind(), ErrorKind::Stopped(77), "{err:?}");
    // The connection itself is fine.
    let (mut tx2, _rx2) = c.open_bi().unwrap();
    tx2.write_all(b"ok").unwrap();
    let (_t, mut r) = s.accept_bi().unwrap();
    let mut two = [0u8; 2];
    r.read_exact(&mut two).unwrap();
    assert_eq!(&two, b"ok");
}
