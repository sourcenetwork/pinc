//! The unpacking of a held entry: bytes whose head cannot be cut from them are rejected as a bad head.
#![allow(clippy::unwrap_used, reason = "tests assert")]

use super::*;
use crate::host::Lane;
use crate::node::Config;
use alloc::boxed::Box;
use vinc_crypto::{IdentityAlg, Keypair};

struct Quiet {
    delivered: usize,
}

impl Host for Quiet {
    fn send(&mut self, _: &NodeId, _: Lane, _: &[u8]) -> bool {
        true
    }
    fn send_member(&mut self, _: &NodeId, _: &[u8]) -> bool {
        true
    }
    fn hub_up(&self, _: &NodeId) -> bool {
        true
    }
    fn in_view(&self, _: &NodeId) -> bool {
        true
    }
    fn wall_ms(&self) -> u64 {
        0
    }
    fn event(&mut self, e: Event<'_>) {
        self.delivered += usize::from(matches!(e, Event::Message { .. }));
    }
}

const ORIGIN: NodeId = [5; 32];

/// A node that keeps heads, and an entry in its hold whose head bytes are not a head.
fn node_with_corrupt_entry() -> (Topics, Held) {
    let key = Keypair::from_seed(IdentityAlg::Ed25519, &[1; 32]).unwrap();
    let cfg = Config {
        me: key.node_id().bytes,
        is_hub: false,
        hubs: &[],
        incarnation: 1 << 16,
        trace: true,
        limits: crate::Limits {
            keep_heads: true,
            ..crate::Limits::default()
        },
    };
    let mut t = Topics::start(&cfg, Box::new(key), 0, 0).unwrap();
    let (slot, len) = t.holds.put(b"topic", &[0xff; 6], b"").unwrap();
    let e = Held {
        mid: [7; 8],
        origin: ORIGIN,
        hop: ORIGIN,
        ts: Hlc::new(1, 0),
        slot,
        len,
    };
    (t, e)
}

fn rejected(t: &mut Topics) -> bool {
    core::iter::from_fn(|| t.poll_trace()).any(|x| {
        matches!(
            x,
            Trace::Rejected {
                why: Reject::BadHead,
                ..
            }
        )
    })
}

/// A floor-held entry with corrupt head bytes is rejected as a bad head and delivers nothing.
#[test]
fn a_held_offer_with_a_corrupt_head_is_a_bad_head() {
    let (mut t, e) = node_with_corrupt_entry();
    let mut h = Quiet { delivered: 0 };
    t.offer_held(&mut h, 0, e);
    assert!(rejected(&mut t));
    assert_eq!(h.delivered, 0);
}

/// An access-held entry with corrupt head bytes is rejected as a bad head when the answer allows it.
#[test]
fn an_allowed_hold_with_a_corrupt_head_is_a_bad_head() {
    let (mut t, e) = node_with_corrupt_entry();
    let mut h = Quiet { delivered: 0 };
    t.held.push(e);
    t.checks.push((1, ORIGIN));
    t.acp_answer(&mut h, 0, 1, true);
    assert!(rejected(&mut t));
    assert_eq!(h.delivered, 0);
    assert!(t.held.is_empty());
}
