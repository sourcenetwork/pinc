//! The paths of the PINCER connection when one is lost or turns out to be a relay's: a session leaves a lost or silent
//! direct path for a relay path added later, a lost path is never used again, and a path named a relay's is valid.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::similar_names
)]

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::conn::{PathId, PathInfo};
use pinc_transport::recovery::PathKind;

const RELAY: PathInfo = PathInfo {
    kind: PathKind::Relay,
    v6: false,
    interface_mtu: 1500,
};

fn connected<'a>(w: &'a mut World, sa: &'a mut Store, sb: &'a mut Store, link: Link) -> Net<'a, 'a> {
    let mut net = setup(w, sa, sb, link);
    assert!(net.connect(net.now + 10 * SEC), "{:?}", net.rx_drops);
    net
}

/// A direct route (A names it 1, B names it 2) and a second one (3 and 4).
fn two_routes(seed: u64) -> Link {
    let mut link = Link::new(seed, Params::new(10 * MS));
    link.add_route(PathId(3), PathId(4), Params::new(10 * MS), Params::new(10 * MS));
    link
}

/// The path the connection is on is lost with no other path valid; a relay path added after the loss takes the
/// session at once, and a stream written next is delivered.
#[test]
fn a_session_on_a_lost_path_moves_to_a_relay_path_added_after_the_loss() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, two_routes(30));
        net.a.conn.path_lost(PathId(1)).unwrap();
        net.link.route(PathId(1)).up = false;
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)), "nothing to move to yet");
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), RELAY)).unwrap();
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(3)),
            "the lost path is still the active one beside a valid relay path"
        );
        let data = pattern(20_000, 31);
        bulk(&mut net, &data, 30 * SEC);
    });
}

/// The direct path stops answering and the session has no relay path at its first probe timeouts: one added after
/// them still takes the session at the next, though the direct path was already dropped as validated.
#[test]
fn a_session_whose_direct_path_went_silent_falls_back_to_a_relay_path_added_later() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut net = connected(&mut w, &mut sa, &mut sb, two_routes(32));
        net.link.route(PathId(1)).up = false;
        let id = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id, &pattern(10_000, 33)).unwrap();
        assert!(net.run(net.now + 30 * SEC, |n| n.a.conn.stats().ptos >= 3));
        assert!(
            !net.a.conn.path_validated(PathId(1)),
            "the silent path is no longer validated"
        );
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), RELAY)).unwrap();
        assert!(
            net.run(net.now + 5 * SEC, |n| n.a.conn.active_is_relay()),
            "the session stays on the unanswered direct path"
        );
    });
}

/// A lost path is not validated by the answer to a challenge sent before the loss, and is not followed by the peer's
/// data: a second direct path is followed while the lost one is held, and data on the lost one's id does not move the
/// session back.
#[test]
fn a_lost_path_is_never_validated_or_followed_again() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = two_routes(34);
        // Nothing A sends on route 3 arrives: its path stays unvalidated.
        link.route(PathId(3)).ab.drop_next(u32::MAX);
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a.with_env(now, |c, env| {
            c.add_path(env, PathId(3), PathInfo::default()).unwrap();
            c.probe(env, PathId(1)).unwrap();
        });
        net.flush();
        net.a.conn.path_lost(PathId(1)).unwrap();
        assert_eq!(net.a.conn.active_path(), Some(PathId(1)), "no valid path to leave for");
        let mark = net.a.log.len();
        net.run(net.now + 200 * MS, |_| false);
        assert!(
            !net.a.conn.path_validated(PathId(1)),
            "the answer to a challenge sent before the loss validated the lost path"
        );
        assert!(
            !net.a.log[mark..].contains(&Rec::PathValidated(PathId(1))),
            "the lost path was reported valid"
        );
        // The peer sends data from the second route: the session follows it.
        let now = net.now;
        net.b.with_env(now, |c, env| c.add_path(env, PathId(4), RELAY)).unwrap();
        net.b.conn.set_active(PathId(4)).unwrap();
        let s = net.b.conn.open_bi().unwrap();
        net.b.conn.write(s, &pattern(2000, 35)).unwrap();
        assert!(net.run(net.now + SEC, |n| n.a.conn.active_path() == Some(PathId(3))));
        // Then from the first again, with higher numbers: the lost path is not followed back.
        net.b.conn.set_active(PathId(2)).unwrap();
        net.b.conn.write(s, &pattern(2000, 36)).unwrap();
        net.run(net.now + SEC, |_| false);
        assert_eq!(
            net.a.conn.active_path(),
            Some(PathId(3)),
            "the session followed data onto a path whose address is gone"
        );
    });
}

/// A held direct path the endpoint then names a relay's is valid at once, as every relay path is.
#[test]
fn a_held_path_named_a_relay_by_add_path_is_valid_at_once() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = two_routes(36);
        link.route(PathId(3)).up = false;
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a
            .with_env(now, |c, env| c.add_path(env, PathId(3), PathInfo::default()))
            .unwrap();
        assert!(!net.a.conn.path_validated(PathId(3)));
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), RELAY)).unwrap();
        assert!(
            net.a.conn.path_validated(PathId(3)),
            "a held path named a relay's stays unvalidated"
        );
    });
}

/// The session is on a relay path and follows the peer onto a direct route whose answers never arrive: at the third
/// probe timeout it leaves that path for a validated one, though the direct path was never validated.
#[test]
fn a_session_followed_onto_an_unanswered_direct_path_leaves_it_at_the_third_probe_timeout() {
    big_stack(|| {
        let mut w = World::new(IdentityAlg::Ed25519);
        let (mut sa, mut sb) = (Store::new(true), Store::new(false));
        let mut link = two_routes(42);
        link.add_route(PathId(5), PathId(6), Params::new(10 * MS), Params::new(10 * MS));
        // Nothing A sends on route 5 arrives: the path stays unanswered.
        link.route(PathId(5)).ab.drop_next(u32::MAX);
        let mut net = connected(&mut w, &mut sa, &mut sb, link);
        let now = net.now;
        net.a.with_env(now, |c, env| c.add_path(env, PathId(3), RELAY)).unwrap();
        net.a.conn.set_active(PathId(3)).unwrap();
        net.b.with_env(now, |c, env| c.add_path(env, PathId(6), RELAY)).unwrap();
        net.b.conn.set_active(PathId(6)).unwrap();
        let s = net.b.conn.open_bi().unwrap();
        net.b.conn.write(s, &pattern(2000, 43)).unwrap();
        assert!(
            net.run(net.now + SEC, |n| n.a.conn.active_path() == Some(PathId(5))),
            "the session did not follow the peer onto the direct route"
        );
        assert!(!net.a.conn.active_is_relay());
        let id = net.a.conn.open_uni().unwrap();
        net.a.conn.write(id, &pattern(10_000, 44)).unwrap();
        assert!(
            net.run(net.now + 30 * SEC, |n| n.a.conn.active_path() != Some(PathId(5))),
            "the session stays on the unanswered direct path"
        );
        assert_eq!(net.a.conn.stats().ptos, 3, "the session left the unanswered path late");
    });
}
