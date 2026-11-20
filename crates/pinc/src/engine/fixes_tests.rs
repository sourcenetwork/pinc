//! Regressions of the core's bounded tables: a refused revoke leaves no bar, a stale lookup failure answers no later
//! lookup, and a restore counts the addresses the book kept.

use alloc::rc::Rc;
use alloc::vec;
use core::net::SocketAddr;

use pinc_connect::client::Notice;
use pinc_core::SessionId;
use pinc_security::Alpn;

use super::adjacent_tests::{core, peer};
use super::state::BOOK_MAX;
use super::{DISCARDED, REVOKED_MAX, Try, Up};
use crate::error::ErrorKind;

#[test]
fn a_revoke_the_node_refuses_leaves_the_peer_unbarred() {
    let mut c = core();
    // The node's own table fills first when it is filled past the bar's view of it.
    for i in 0..REVOKED_MAX as u64 {
        c.node.revoke(1, &peer(i).bytes).unwrap();
    }
    let extra = peer(REVOKED_MAX as u64);
    let err = c.revoke(1, &extra).unwrap_err();
    assert_eq!(err.kind(), ErrorKind::Busy);
    assert!(!c.admit.is_revoked(&extra), "a refused revoke leaves no bar");
}

#[test]
fn a_stale_lookup_failure_does_not_answer_a_later_lookup() {
    let mut c = core();
    let p = peer(1);
    c.on_notice(&Notice::Missing(p));
    c.lookup_start(1, &p);
    assert!(
        matches!(c.lookup_poll(&p, 100, 2), Try::Wait(_)),
        "the old failure answered"
    );
}

#[test]
fn a_restore_counts_the_nodes_the_book_kept() {
    let mut c = core();
    let a: SocketAddr = "10.0.0.1:9".parse().unwrap();
    for i in 0..(BOOK_MAX - 1) as u64 {
        assert!(c.add_address(peer(1000 + i), a));
    }
    let mut state = c.export_state(1).unwrap();
    let len = u32::from_be_bytes(state[1..5].try_into().unwrap()) as usize;
    let at = 5 + len;
    // Two new nodes with one address each; only one has room.
    let mut entries = vec![0, 2];
    for i in 0..2u64 {
        entries.push(peer(i).alg.tag());
        entries.extend_from_slice(&peer(i).bytes);
        entries.extend_from_slice(&[1, 4, 10, 0, 0, 2, 0, 9]);
    }
    let tail = state.split_off(at);
    // The tail is the old count, the old entries and the record number.
    let seq = tail[tail.len() - 8..].to_vec();
    state.extend_from_slice(&entries);
    state.extend_from_slice(&seq);
    let r = c.restore_state(1, &state).unwrap();
    assert_eq!(r.addresses, 1);
}

/// A session of the core's table that the endpoint does not know, so any stream of it is gone.
fn listed_full() -> (super::adjacent_tests::C, Rc<super::SessInfo>) {
    let mut c = core();
    let id = SessionId(1);
    c.session_up(1, id, peer(1), Alpn::new(b"app").unwrap(), Up::Accepted { held: 0 });
    let s = c.sessions.get_mut(&id).unwrap();
    s.discard.extend((0..DISCARDED as u64).map(|i| i * 4));
    let info = Rc::clone(&s.info);
    (c, info)
}

#[test]
fn a_dropped_stream_that_holds_no_slot_is_not_listed() {
    let (mut c, info) = listed_full();
    // The end of this stream was consumed by a read that was dropped before it told the handle: the slot is free.
    c.drop_recv(1, &info, 4 * DISCARDED as u64 + 400);
    assert_eq!(c.sessions.get(&info.id).unwrap().discard.len(), DISCARDED);
}
