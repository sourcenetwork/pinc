//! The examples compile as modules of this test and run.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    dead_code,
    missing_docs,
    unreachable_pub,
    async_fn_in_trait
)]

#[path = "../crates/pinc/examples/defradb_backend.rs"]
mod defradb_backend;
#[path = "../crates/pinc/examples/echo.rs"]
mod echo;
#[path = "../crates/pinc/examples/platform.rs"]
mod platform;
#[path = "../crates/pinc/examples/transfer.rs"]
mod transfer;

#[nuclei::test]
async fn echo_example() {
    assert_eq!(echo::run().await.unwrap(), b"hello, pinc");
}

#[nuclei::test]
async fn transfer_example() {
    let (n, ok) = transfer::run(4 << 20).await.unwrap();
    assert_eq!(n, 4 << 20);
    assert!(ok);
}

#[nuclei::test]
async fn defradb_backend_example() {
    assert_eq!(defradb_backend::run().await.unwrap(), b"pushlog/payload");
}

#[test]
fn platform_example() {
    assert_eq!(platform::run(b"hello, pinc").unwrap(), b"hello, pinc");
}
