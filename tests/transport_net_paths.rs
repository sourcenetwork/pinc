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
