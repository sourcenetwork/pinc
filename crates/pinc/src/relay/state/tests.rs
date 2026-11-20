//! Tests of the state machine's stream handling: refusals.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use alloc::rc::Rc;
use core::cell::RefCell;
use core::net::SocketAddr;

use pinc_keystore::SoftwareStore;

use super::*;
use crate::keys::Identity;
use crate::relay::access::AllowAll;

const T0: u64 = 1_000_000_000_000;

fn core(limits: Limits) -> Core<(), SoftwareStore, AllowAll> {
    let identity = Rc::new(RefCell::new(Identity::from_seed_with(&[7; 32], &[0; 32]).unwrap()));
    let local: SocketAddr = "192.0.2.1:4000".parse().unwrap();
    Core::new(identity, AllowAll, &[], limits, Some(local), T0).unwrap()
}

/// A stream refused because the relay is stopping is an accept error, not a full table of handshakes.
#[test]
fn a_stream_refused_while_stopping_is_an_accept_error() {
    let mut core = core(Limits::default());
    core.begin_shutdown();
    assert!(core.add_conn((), CarrierKind::Tcp, T0).is_err());
    assert_eq!(core.counters.refused_handshakes_full, 0);
    assert_eq!(core.counters.accept_errors, 1);
}
