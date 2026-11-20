//! The deadlines of the facade go through the host's platform: a dial whose 20 s timeout the virtual clock reaches
//! fails after the test has advanced that clock, in well under a second of real time. A deadline that read the
//! operating system's clock instead would never fire here, so the test fails rather than waits for it.
#![allow(clippy::panic, clippy::expect_used, reason = "tests assert")]

use std::cell::Cell;
use std::future::Future;
use std::net::SocketAddr;
use std::pin::pin;
use std::rc::Rc;
use std::task::{Context, Poll, Waker};

use pinc::Pinc;
use pinc::{ErrorKind, HostError, NodeAddr, NodeId, Platform};
use pinc_crypto::IdentityAlg;

/// The virtual clock: a nanosecond count the test advances.
#[derive(Debug, Clone)]
struct Clock(Rc<Cell<u64>>);

impl Clock {
    fn new() -> Self {
        Self(Rc::new(Cell::new(1_000_000_000)))
    }

    fn advance(&self, ns: u64) {
        self.0.set(self.0.get().saturating_add(ns));
    }
}

/// The host's error: never transient, so a failing receive would end the endpoint instead of losing a datagram.
#[derive(Debug)]
struct NeverTransient;

impl HostError for NeverTransient {
    fn is_transient(&self) -> bool {
        false
    }
}

/// The platform of the test: the virtual clock, no wall clock, fixed randomness.
#[derive(Debug, Clone)]
struct Virtual {
    clock: Clock,
}

impl Platform for Virtual {
    type Instant = u64;
    type Error = NeverTransient;

    fn now(&self) -> u64 {
        self.clock.0.get()
    }

    fn wall_ns(&self) -> Option<u64> {
        None
    }

    fn random(&self, out: &mut [u8]) -> Result<(), pinc::Error> {
        out.fill(9);
        Ok(())
    }
}

/// Poll `f` until it is ready, advancing the clock 100 ms a round; `steps` bounds the wait, so a deadline that
/// never fires ends the test instead of hanging it.
fn drive<F: Future>(f: F, clock: &Clock, steps: usize) -> F::Output {
    let mut f = pin!(f);
    let mut cx = Context::from_waker(Waker::noop());
    for _ in 0..steps {
        if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
            return v;
        }
        clock.advance(100_000_000);
    }
    panic!("the future never finished in {steps} rounds of 100 ms");
}

/// The 20 s connect timeout fires when the platform's clock says so, not when the operating system's does.
#[test]
fn a_connect_timeout_fires_on_the_platforms_clock() {
    let clock = Clock::new();
    let platform = Virtual { clock: clock.clone() };
    let peer_addr: SocketAddr = "127.0.0.1:1".parse().expect("an address");
    let ep = Pinc::builder_on(platform)
        .expect("the platform has randomness")
        .connect_timeout(std::time::Duration::from_secs(20))
        .build(
            // The peer never answers: a receive that is never ready.
            move |_buf: &mut [u8]| async {
                std::future::pending::<Result<(usize, SocketAddr), NeverTransient>>().await
            },
            async |pkt: &[u8], _to: SocketAddr| Ok(pkt.len()),
            {
                let clock = clock.clone();
                // The sleep completes when the virtual clock reaches `at`: the only wait the host gives.
                move |at: u64| {
                    let clock = clock.clone();
                    async move {
                        std::future::poll_fn(|cx| {
                            if clock.0.get() >= at {
                                Poll::Ready(())
                            } else {
                                cx.waker().wake_by_ref();
                                Poll::Pending
                            }
                        })
                        .await;
                    }
                }
            },
        )
        .expect("the endpoint builds");
    let to = NodeAddr {
        node: NodeId {
            alg: IdentityAlg::Ed25519,
            bytes: [11; 32],
        },
        direct: vec![peer_addr],
        relays: Vec::new(),
    };
    let err = drive(ep.connect(to, b"t"), &clock, 1_000).expect_err("the dial times out");
    assert_eq!(err.kind(), ErrorKind::TimedOut, "the connect timeout fired");
}
