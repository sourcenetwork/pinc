//! The adjacency report of connected topics: a burst of sessions is named to the hubs once a turn, and no more often
//! than [`ADJ_GAP`] while sessions churn (pinc#86, review of #137).

use alloc::vec;
use alloc::vec::Vec;

use pinc_core::{EndReason, Event, SessionId};
use pinc_crypto::{IdentityAlg, NodeId};
use pinc_keystore::SoftwareStore;
use pinc_security::Alpn;

use super::topics::ADJ_GAP;
use super::{AllowAll, Core, CoreConfig, Up};
use crate::keys::Identity;
use crate::mem::Limits;

const BURST: u64 = 1000;

pub(super) type C = Core<SoftwareStore, AllowAll>;

pub(super) fn core() -> C {
    let cfg = CoreConfig {
        identity: Identity::from_seed(&[5; 32]).unwrap(),
        map_keys: crate::maps::Keys::for_tests(5),
        alpns: vec![b"app".to_vec()],
        limits: Limits {
            connections: 1024,
            accept_sessions: 1024,
            pool_chunks: 16,
            ..Limits::default()
        },
        admit: AllowAll,
        max_gso: 1,
        mtu: 1500,
        locals: vec!["127.0.0.1:1".parse().unwrap()],
        relays: Vec::new(),
        hub: false,
        connected_topics: true,
        relaying: false,
        connect_timeout: 1_000_000_000,
        port_mapping: crate::start::PortMapping {
            on: false,
            gateway: None,
        },
    };
    crate::start::build(cfg, 1, 1_700_000_000_000).unwrap()
}

pub(super) fn peer(i: u64) -> NodeId {
    let mut bytes = [0u8; 32];
    bytes[..8].copy_from_slice(&i.to_be_bytes());
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes,
    }
}

fn signed(c: &C) -> u64 {
    c.node.reach_stats().signed
}

fn named(c: &C) -> Option<usize> {
    c.adjacent.as_ref().map(Vec::len)
}

/// One turn of the driver at `now`: everything waiting is handled.
fn turn(c: &mut C, now: u64) {
    for _ in 0..4 {
        c.service(now);
    }
}

/// 1,000 sessions coming up in one turn are one signed record naming all of them; 500 of them ending inside the gap
/// sign nothing until the gap passes, then one record more. Reporting on every event signed 1,000 records.
#[test]
fn a_burst_of_sessions_is_one_record_a_turn() {
    let mut c = core();
    let alpn = Alpn::new(b"app").unwrap();
    let start = signed(&c);
    let now = 10 * ADJ_GAP;
    // The sessions come up as their `Incoming` would bring them: the endpoint has none of them, so the event itself
    // would find each one gone.
    for i in 0..BURST {
        c.session_up(now, SessionId(i + 1), peer(i), alpn, Up::Accepted { held: 0 });
        c.adjacent_changed();
    }
    turn(&mut c, now);
    assert_eq!(signed(&c) - start, 1, "one record for the whole burst");
    assert_eq!(named(&c), Some(1000));

    for i in 0..BURST / 2 {
        c.on_event(
            now + 1,
            Event::Closed {
                session: SessionId(i + 1),
                reason: EndReason::Orphaned,
            },
        );
    }
    turn(&mut c, now + 1);
    assert_eq!(signed(&c) - start, 1, "nothing more is signed inside the gap");
    assert_eq!(c.adjacent_deadline(), Some(now + ADJ_GAP));
    turn(&mut c, now + ADJ_GAP);
    assert_eq!(
        signed(&c) - start,
        2,
        "the gap passed: one record for the ended sessions"
    );
    assert_eq!(named(&c), Some(500));
    assert_eq!(c.adjacent_deadline(), None);
}
