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

#[path = "../crates/vinc/examples/defradb_backend.rs"]
mod defradb_backend;
#[path = "../crates/vinc/examples/echo.rs"]
mod echo;
#[path = "../crates/vinc/examples/transfer.rs"]
mod transfer;

#[test]
fn echo_example() {
    assert_eq!(echo::run().unwrap(), b"hello, vinc");
}

#[test]
fn transfer_example() {
    let (n, ok) = transfer::run(4 << 20).unwrap();
    assert_eq!(n, 4 << 20);
    assert!(ok);
}

#[test]
fn defradb_backend_example() {
    assert_eq!(defradb_backend::run().unwrap(), b"pushlog/payload");
}
