//! The adjacency report of connected topics: a burst of sessions is named to the hubs once a turn, and no more often
//! than [`ADJ_GAP`] while sessions churn (vinc#86, review of #137).

use vinc_core::{EndReason, Event, SessionId};
use vinc_crypto::{IdentityAlg, NodeId};
use vinc_keystore::SoftwareStore;
use vinc_security::Alpn;

use super::topics::ADJ_GAP;
use super::{AllowAll, Core, CoreConfig};
use crate::keys::Identity;
use crate::mem::Limits;

const BURST: u64 = 1000;

type C = Core<SoftwareStore, AllowAll>;

fn core() -> C {
    let cfg = CoreConfig {
        identity: Identity::from_seed(&[5; 32]).unwrap(),
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
    };
    crate::start::build(cfg, 1).unwrap()
}

fn peer(i: u64) -> NodeId {
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
    for i in 0..BURST {
        c.on_event(
            now,
            Event::Incoming {
                session: SessionId(i + 1),
                node: peer(i),
                alpn,
            },
        );
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
