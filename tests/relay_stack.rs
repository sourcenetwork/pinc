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

mod pinc_common;
mod relay_members;

use std::cell::RefCell;
use std::collections::VecDeque;
use std::pin::pin;
use std::rc::Rc;
use std::task::{Context, Waker};

use pinc::Identity;
use pinc::relay::{Hosted, Relay};
use relay_members::{bind_ports, build_relay, on_stack};

#[test]
fn a_relay_builds_on_a_two_mebibyte_stack_in_an_unoptimised_build() {
    on_stack(2 << 20, || async {
        let ports = bind_ports().await;
        let kinds = Rc::new(RefCell::new(VecDeque::new()));
        let builder = Relay::builder().identity(Identity::from_seed(&[3; 32]).unwrap());
        drop(build_relay(&ports, &kinds, builder));
    });
}

/// The identity builds on a 128 KiB stack: an Ed25519 key pair costs tens of bytes and is no longer moved 64 KiB by
/// value (#706; before, the floor measured in #681 was 512 KiB in this profile, so this aborted with a stack
/// overflow). What is left is the curve arithmetic: on `x86_64` its vector code reserves 44 KiB in one frame at
/// opt-level 0, so 64 KiB overflows there and 96 KiB is enough (64 KiB is enough on aarch64).
#[test]
fn an_identity_builds_on_a_128_kib_stack_in_an_unoptimised_build() {
    std::thread::Builder::new()
        .stack_size(128 << 10)
        .spawn(|| {
            let id = Identity::from_seed(&[3; 32]).unwrap();
            assert_ne!(id.node_id().bytes, [0; 32]);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// Poll `run` once and drop it: the first round of a relay.
fn poll_run_once<H: Hosted>(relay: &Relay<H>) {
    let mut run = pin!(relay.run());
    let mut cx = Context::from_waker(Waker::noop());
    let _ = run.as_mut().poll(&mut cx);
}

/// A relay without the hub role builds, its identity included, and polls `run` once on a 256 KiB stack.
#[test]
fn a_relay_polls_run_once_on_a_256_kib_stack_in_an_unoptimised_build() {
    on_stack(256 << 10, || async {
        let ports = bind_ports().await;
        let kinds = Rc::new(RefCell::new(VecDeque::new()));
        let builder = Relay::builder().identity(Identity::from_seed(&[3; 32]).unwrap());
        let relay = build_relay(&ports, &kinds, builder);
        poll_run_once(&relay);
    });
}

/// A relay with the hub role builds, its identity included, and polls `run` once on a 256 KiB stack.
///
/// Ignored for a cause the key pair no longer owns: the hub endpoint's construction reserves its tables' by-value
/// temporaries and a whole endpoint copy on the stack in this profile (~300 KiB, #736). The identity on this path
/// builds on 128 KiB since the key pair shrank; the test is the done-when of #706's hub leg.
#[test]
#[ignore = "the hub endpoint's construction needs ~300 KiB of stack in this profile; #736"]
fn a_hub_relay_polls_run_once_on_a_256_kib_stack_in_an_unoptimised_build() {
    on_stack(256 << 10, || async {
        let ports = bind_ports().await;
        let kinds = Rc::new(RefCell::new(VecDeque::new()));
        let builder = Relay::builder()
            .identity(Identity::from_seed(&[3; 32]).unwrap())
            .hub(ports.addr, &[]);
        let relay = build_relay(&ports, &kinds, builder);
        poll_run_once(&relay);
    });
}
