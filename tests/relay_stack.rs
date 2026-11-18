//! A relay builds and runs on a small stack, as in an application's unoptimised build: the stack a test thread has is
//! 2 MiB, and the `unoptimised` profile (`just unoptimised`) builds the
//! library at opt-level 0, where a function reserves stack for every value it could build by value. Each test builds the
//! relay through the public builder, on the thread whose stack is small, identity included.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::large_futures,
    dead_code,
    missing_docs
)]

mod relay_members;
mod vinc_common;

use std::cell::RefCell;
use std::collections::VecDeque;
use std::rc::Rc;

use relay_members::{bind_ports, build_relay, on_stack};
use vinc::Identity;
use vinc::relay::Relay;

#[test]
fn a_relay_builds_on_a_two_mebibyte_stack_in_an_unoptimised_build() {
    on_stack(2 << 20, || async {
        let ports = bind_ports().await;
        let kinds = Rc::new(RefCell::new(VecDeque::new()));
        let builder = Relay::builder().identity(Identity::from_seed(&[3; 32]).unwrap());
        drop(build_relay(&ports, &kinds, builder));
    });
}
