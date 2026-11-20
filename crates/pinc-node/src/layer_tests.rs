//! Unit tests of how the node dials the sessions of its layers and ends a dial that gets no session: a reconcile round
//! whose dial is refused or shed ends with an event, a delay-tolerant redial is not lost behind another peer's
//! backoff, and a full table of dials sends none.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    missing_docs,
    reason = "tests assert freely"
)]

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::net::{IpAddr, Ipv4Addr, SocketAddr};

use pinc_broadcast::{IdKey, Limits};
use pinc_connect::client::{Config as ConnCfg, RelayCfg};
use pinc_core::{ConnectFailure, Event, SessionId};
use pinc_crypto::{Drbg, IdentityAlg, Keypair, Software};
use pinc_security::{Alpn, Env, KeyHandle, LocalIdentity, PrekeyPolicy, SoftPrekeys};
use pinc_values::knobs::OPEN_RETRY;

use crate::apps::{Apps, Enabled, NoDtn, NoIndex, NoValues, SetsApp};
use crate::config::{Config, HUB_ALPN, SETS_ALPN, TABLE_MAX};
use crate::event::{NodeEvent, ReconcileFailure};
use crate::io::tests::{DIALED, Stub};
use crate::layer::{LSess, Layer};
use crate::node::Node;
use crate::reconcile::ATTEMPTS;
use crate::trace::Body;
use crate::values_types::ValuesRequest;

const S: u64 = 1_000_000_000;
const SET: &[u8] = b"items";

/// The secrets of the broadcast id tables.
static SECRETS: [u64; 7] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xff51_afd7_ed55_8ccd,
    0xc4ce_b9fe_1a85_ec53,
];

/// A set of that name, always empty.
pub(crate) struct Sets;

impl SetsApp for Sets {
    type Index<'a> = NoIndex;
    fn index(&self, _set_ref: &[u8]) -> Option<NoIndex> {
        Some(NoIndex)
    }
}

/// Reconcile and delay-tolerant delivery on, with nothing stored.
pub(crate) struct TApps {
    values_on: bool,
    values: NoValues,
    sets: Sets,
    dtn: NoDtn,
}

impl Apps<Software> for TApps {
    type Values = NoValues;
    type Sets = Sets;
    type Dtn = NoDtn;
    fn enabled(&self) -> Enabled {
        Enabled {
            values: self.values_on,
            sets: true,
            dtn: true,
        }
    }
    fn values(&mut self) -> &mut NoValues {
        &mut self.values
    }
    fn sets(&self) -> &Sets {
        &self.sets
    }
    fn dtn(&mut self) -> &mut NoDtn {
        &mut self.dtn
    }
}

pub(crate) type TNode = Node<Stub, Software, (), 4, 32, TApps>;

/// The peer the node lists as its relay: a dial to it always has a way to go.
fn hub() -> pinc_crypto::NodeId {
    Keypair::from_seed(IdentityAlg::Ed25519, &[0x41; 32]).unwrap().node_id()
}

fn node() -> Box<TNode> {
    node_cfg(false, false, false)
}

pub(crate) fn node_with(is_hub: bool) -> Box<TNode> {
    node_cfg(is_hub, false, false)
}

/// A node that is a hub or not, with the values layer on or off, and its trace on or off.
fn node_cfg(is_hub: bool, values_on: bool, trace: bool) -> Box<TNode> {
    let kp = Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap();
    let identity = LocalIdentity::from_keypair(&kp, KeyHandle(1)).unwrap();
    let prov = Software;
    let mut drbg = Drbg::new(&[0x21; 32]);
    let mut env = Env {
        provider: &prov,
        now: 0,
        drbg: &mut drbg,
    };
    let mut prekeys = SoftPrekeys::new(&mut env, PrekeyPolicy::default()).unwrap();
    let prekey = prekeys.acquire(&mut env).unwrap();
    let local = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 10)), 4433);
    let addr = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(203, 0, 113, 20)), 4433);
    let mut relays = [None; 4];
    relays[0] = Some(RelayCfg {
        id: hub(),
        udp: Some(addr),
        tcp: Some(addr),
        ws: Some(addr),
    });
    let cfg = Config {
        connect: ConnCfg {
            me: kp.node_id(),
            identity,
            relays,
            phone: false,
            restarted: false,
            start: 0,
            v6: false,
            keep_learn: false,
        },
        is_hub,
        version: 1,
        alpn: HUB_ALPN,
        limits: Limits::default(),
        map_keys: IdKey::new(0x5eed, &SECRETS).unwrap(),
        wall_ms: 1_700_000_000_000,
        local,
        trace,
    };
    let apps = TApps {
        values_on,
        values: NoValues,
        sets: Sets,
        dtn: NoDtn,
    };
    Node::with_apps(
        &cfg,
        Stub::default(),
        prekey,
        prov,
        Drbg::new(&[0x31; 32]),
        Box::new(Keypair::from_seed(IdentityAlg::Ed25519, &[0x11; 32]).unwrap()),
        (),
        7,
        apps,
    )
    .map(Box::new)
    .unwrap()
}

/// Run `f` on a thread with the stack a node needs.
pub(crate) fn big(f: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(f)
        .unwrap()
        .join()
        .unwrap();
}

/// The reasons of the reconcile rounds that failed, as the node reports them now.
fn failures(node: &mut TNode) -> Vec<ReconcileFailure> {
    let mut out = Vec::new();
    while let Some(e) = node.poll_event() {
        if let NodeEvent::ReconcileFailed { reason, .. } = e {
            out.push(reason);
        }
    }
    out
}

#[test]
fn a_round_whose_session_is_shed_for_a_revoked_peer_ends_cancelled() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        node.sets_start(S, &peer, SET).unwrap();
        assert_eq!(node.io.ep.dials.len(), 1, "the round dials its peer");
        assert_eq!(node.io.ep.dials[0].1, SETS_ALPN);
        node.revoke(S, &peer).unwrap();
        node.layer_up(S, Layer::Sets, SessionId(DIALED), peer, false);
        node.settle(S);
        assert_eq!(failures(&mut node), [ReconcileFailure::Cancelled]);
        assert_eq!(node.sets_running(), 0);
    });
}

#[test]
fn a_dial_that_fails_after_the_peer_was_revoked_ends_the_round_cancelled() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        node.sets_start(S, &peer, SET).unwrap();
        let failed = || Event::ConnectFailed {
            session: None,
            node: hub(),
            alpn: Alpn::new(SETS_ALPN).unwrap(),
            reason: ConnectFailure::Timeout,
        };
        for _ in 0..ATTEMPTS - 1 {
            node.on_layer_event(S, Layer::Sets, failed());
            node.settle(S);
            assert!(failures(&mut node).is_empty(), "an attempt that failed retries");
        }
        node.revoke(S, &peer).unwrap();
        node.on_layer_event(S, Layer::Sets, failed());
        node.settle(S);
        assert_eq!(failures(&mut node), [ReconcileFailure::Cancelled]);
        assert_eq!(node.sets_running(), 0);
    });
}

#[test]
fn a_round_whose_session_closes_after_the_peer_was_revoked_ends_cancelled() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        node.sets_start(S, &peer, SET).unwrap();
        let failed = || Event::ConnectFailed {
            session: None,
            node: hub(),
            alpn: Alpn::new(SETS_ALPN).unwrap(),
            reason: ConnectFailure::Timeout,
        };
        for _ in 0..ATTEMPTS - 1 {
            node.on_layer_event(S, Layer::Sets, failed());
            node.settle(S);
            assert!(failures(&mut node).is_empty(), "an attempt that failed retries");
        }
        let session = SessionId(DIALED + last_sets_dial(&node) as u64);
        node.layer_up(S, Layer::Sets, session, peer, false);
        node.settle(S);
        assert!(failures(&mut node).is_empty(), "the session coming up ends no round");
        node.revoke(S, &peer).unwrap();
        node.layer_closed(S, session);
        node.settle(S);
        assert_eq!(failures(&mut node), [ReconcileFailure::Cancelled]);
        assert_eq!(node.sets_running(), 0);
    });
}

#[test]
fn a_round_started_for_a_revoked_peer_ends_cancelled_without_retrying() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        node.revoke(S, &peer).unwrap();
        node.sets_start(S, &peer, SET).unwrap();
        assert_eq!(failures(&mut node), [ReconcileFailure::Cancelled]);
        assert!(node.io.ep.dials.is_empty(), "nothing is dialed for a revoked peer");
        assert_eq!(node.sets_running(), 0);
    });
}

/// The index of the last dial of the reconcile protocol the node made.
fn last_sets_dial(node: &TNode) -> usize {
    node.io
        .ep
        .dials
        .iter()
        .rposition(|d| d.1 == SETS_ALPN)
        .expect("a dial of the reconcile protocol")
}

fn sets_dials(node: &TNode) -> usize {
    node.io.ep.dials.iter().filter(|d| d.1 == SETS_ALPN).count()
}

fn fill_lconn(node: &mut TNode) {
    for i in 0..TABLE_MAX as u64 {
        let mut other = [0u8; 32];
        other[..8].copy_from_slice(&i.to_le_bytes());
        node.io.lconn.insert((Layer::Values, other));
    }
}

#[test]
fn a_round_whose_session_the_full_table_sheds_spends_an_attempt_and_dials_again_after_the_period() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        for i in 0..TABLE_MAX as u64 {
            let mut other = [0u8; 32];
            other[..8].copy_from_slice(&i.to_le_bytes());
            node.io.lsess.insert(
                SessionId(1 + i),
                LSess {
                    layer: Layer::Values,
                    peer: other,
                    incoming: true,
                    opened: 0,
                },
            );
        }
        node.sets_start(S, &peer, SET).unwrap();
        for k in 0..u64::from(ATTEMPTS) {
            let t = S + k * OPEN_RETRY;
            let dials = sets_dials(&node);
            node.layer_up(
                t,
                Layer::Sets,
                SessionId(DIALED + last_sets_dial(&node) as u64),
                peer,
                false,
            );
            node.settle(t);
            if k + 1 == u64::from(ATTEMPTS) {
                assert_eq!(failures(&mut node), [ReconcileFailure::Exhausted]);
                assert_eq!(node.sets_running(), 0);
                break;
            }
            assert!(failures(&mut node).is_empty(), "no event while attempts remain ({k})");
            assert_eq!(node.sets_running(), 1);
            node.handle_timeout(t + OPEN_RETRY - 1);
            assert_eq!(sets_dials(&node), dials, "the round waits for the period ({k})");
            node.handle_timeout(t + OPEN_RETRY);
            assert_eq!(
                sets_dials(&node),
                dials + 1,
                "the round dials again after the period ({k})"
            );
        }
    });
}

#[test]
fn a_round_on_a_table_that_stays_full_spends_one_attempt_per_retry_period_and_ends_exhausted() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        fill_lconn(&mut node);
        node.sets_start(S, &peer, SET).unwrap();
        assert_eq!(sets_dials(&node), 0, "a dial that cannot be recorded is not sent");
        assert!(
            failures(&mut node).is_empty(),
            "one attempt is spent and no event has come"
        );
        assert_eq!(node.sets_running(), 1);
        for k in 1..u64::from(ATTEMPTS) {
            node.handle_timeout(S + k * OPEN_RETRY - 1);
            assert_eq!(node.sets_running(), 1, "the round waits for the period ({k})");
            assert!(failures(&mut node).is_empty(), "the dial after the wait ends no round");
            node.handle_timeout(S + k * OPEN_RETRY);
            if k + 1 == u64::from(ATTEMPTS) {
                assert_eq!(failures(&mut node), [ReconcileFailure::Exhausted]);
                assert_eq!(node.sets_running(), 0);
            } else {
                assert!(failures(&mut node).is_empty(), "the attempt {k} ends no round");
                assert_eq!(node.sets_running(), 1);
            }
        }
        assert_eq!(sets_dials(&node), 0);
    });
}

#[test]
fn a_round_whose_table_frees_before_the_retry_period_ends_dials_at_that_time() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        fill_lconn(&mut node);
        node.sets_start(S, &peer, SET).unwrap();
        assert_eq!(sets_dials(&node), 0);
        node.io.lconn.clear();
        node.handle_timeout(S + OPEN_RETRY - 1);
        assert_eq!(sets_dials(&node), 0, "the round waits for its retry period");
        node.handle_timeout(S + OPEN_RETRY);
        assert_eq!(sets_dials(&node), 1, "the round dials at the retry time");
        let id = SessionId(DIALED + last_sets_dial(&node) as u64);
        node.layer_up(S + OPEN_RETRY, Layer::Sets, id, peer, false);
        node.settle(S + OPEN_RETRY);
        assert!(node.io.lsess.contains_key(&id));
        assert!(failures(&mut node).is_empty(), "the dial ends no round");
        assert_eq!(node.sets_running(), 1);
    });
}

#[test]
fn a_delay_tolerant_dial_skipped_inside_its_backoff_arms_the_redial_at_its_own_end() {
    big(|| {
        let mut node = node();
        let (a, b) = (hub().bytes, [0x42u8; 32]);
        // A fails at 0 and waits 2 s; B fails at 1 s and waits 2 s, until 3 s.
        node.layer_failed(0, Layer::Dtn, &a);
        node.layer_failed(S, Layer::Dtn, &b);
        assert_eq!(node.dtn.as_deref().unwrap().redial_at, Some(2 * S));
        // The timer fires at 2 s and is cleared; A is dialed again and B is still inside its wait.
        node.dtn.as_deref_mut().unwrap().redial_at = None;
        node.dial_layer(2 * S, Layer::Dtn, &a);
        node.dial_layer(2 * S, Layer::Dtn, &b);
        assert_eq!(
            node.dtn.as_deref().unwrap().redial_at,
            Some(3 * S),
            "nothing would wake the node when B's wait ends"
        );
    });
}

#[test]
fn a_dial_with_a_full_table_of_dials_is_not_sent_and_the_layer_is_told() {
    big(|| {
        let mut node = node();
        let peer = hub().bytes;
        for i in 0..TABLE_MAX as u64 {
            let mut other = [0u8; 32];
            other[..8].copy_from_slice(&i.to_le_bytes());
            node.io.lconn.insert((Layer::Values, other));
        }
        node.dial_layer(S, Layer::Dtn, &peer);
        assert!(
            node.io.ep.dials.is_empty(),
            "a dial that cannot be recorded is not sent"
        );
        assert!(node.io.lfailed.contains_key(&(Layer::Dtn, peer)), "the layer is told");
        assert_eq!(node.io.lconn.len(), TABLE_MAX);
    });
}

/// A stall redial hangs up the session every fetch of the provider shares, which takes it out of the sessions the node
/// opens streams on at once. When the endpoint reports that session closed, every fetch on it is told, not only the
/// one that redialed: each gives up its streams there and tries again.
#[test]
fn a_hung_up_values_session_that_closes_is_reported_to_every_fetch_on_it() {
    big(|| {
        let mut node = node_cfg(false, true, true);
        let peer = hub().bytes;
        for _ in 0..2 {
            let req = ValuesRequest {
                root: [7; 32],
                length: 1 << 20,
                ranges: &[],
                providers: &[peer],
                deadline: None,
            };
            node.values_fetch(S, &req).unwrap();
        }
        node.settle(S);
        node.layer_up(S, Layer::Values, SessionId(DIALED), peer, false);
        node.settle(S);
        node.io.lout.remove(&(Layer::Values, peer));
        while node.poll_trace().is_some() {}
        node.layer_closed(S, SessionId(DIALED));
        let mut told = 0;
        while let Some(item) = node.poll_trace() {
            told += usize::from(matches!(
                item.body,
                Body::Values(_, pinc_values::trace::Trace::Retry(_))
            ));
        }
        assert_eq!(told, 2, "a fetch of the closed session was not told it is gone");
    });
}
