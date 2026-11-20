//! Tests of the state machine's stream handling: refusals, the write backlog and the WebSocket control replies.

#![allow(clippy::unwrap_used, clippy::indexing_slicing, reason = "tests assert")]

use alloc::rc::Rc;
use alloc::vec;
use core::cell::RefCell;
use core::net::SocketAddr;

use pinc_connect::carrier::ws::{self, Opcode};
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

/// A write in flight is part of the stream's backlog: a stream never holds more than the limit in all.
#[test]
fn a_write_in_flight_counts_against_the_backlog() {
    let limits = Limits::default();
    let limit = limits.write_backlog;
    let mut core = core(limits);
    let slot = core.add_conn((), CarrierKind::Tcp, T0).unwrap();
    let c = core.conn(slot).unwrap();
    assert!(c.push(&vec![0; limit], limit));
    assert!(c.take_write(None).is_some(), "the queue is handed to a write");
    assert!(!c.push(&[0], limit), "a second backlog fits beside the write in flight");
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

/// Pings that arrive together are answered once, with the latest: no honest peer is closed, and the answers waiting
/// stay one frame.
#[test]
fn nine_pings_in_one_read_leave_one_answer_and_an_open_carrier() {
    let mut core = core(Limits::default());
    let slot = core.add_conn((), CarrierKind::Ws, T0).unwrap();
    let mut raw = Vec::new();
    for i in 0..9u8 {
        let mut f = [0u8; 2 + 4 + 125];
        let n = ws::encode(Opcode::Ping, &[i; 125], Some([1, 2, 3, 4]), &mut f).unwrap();
        raw.extend_from_slice(&f[..n]);
    }
    core.read_ws(slot, T0, &raw, raw.len());
    let c = core.conn(slot).unwrap();
    assert_eq!(c.dying, None, "an honest peer was closed");
    let (buf, from) = c.take_write(None).unwrap();
    let mut pong = [0u8; 2 + 125];
    let n = ws::encode(Opcode::Pong, &[8; 125], None, &mut pong).unwrap();
    assert_eq!((&buf[from..], from), (&pong[..n], 0), "the answer is not the latest ping's alone");
    assert_eq!(core.counters.slow_closed, 0);
}
