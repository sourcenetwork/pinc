//! Tests of the role's clock and of the readiness of its mailbox, moved out of `drive.rs` to keep it under its size
//! limit.

use core::convert::Infallible;

use super::*;
use crate::endpoint::{Endpoint, Pinc};

const SEC: u64 = 1_000_000_000;

/// A platform whose wall clock reads the given nanoseconds.
struct Wall(u64);

impl Platform for Wall {
    type Instant = u64;
    type Error = Infallible;

    fn now(&self) -> u64 {
        0
    }

    fn wall_ns(&self) -> u64 {
        self.0
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Infallible> {
        for (i, b) in (0u8..=255).cycle().zip(out) {
            *b = i.wrapping_mul(31).wrapping_add(7);
        }
        Ok(())
    }
}

/// An endpoint with the relay role, on a platform whose wall clock reads `wall`; its carriers never complete.
fn rolled(wall: u64) -> Endpoint<impl Hosted> {
    let carriers = crate::relay::CarrierFns::new(
        async || -> crate::Result<((), crate::carrier::CarrierKind)> { core::future::pending().await },
        async |_: &crate::relay::Peer, _: crate::carrier::CarrierKind| -> crate::Result<()> {
            Err(crate::error::Error::config("no peers"))
        },
        async |_s: &(), buf: Vec<u8>| -> (crate::Result<usize>, Vec<u8>) { (Ok(0), buf) },
        async |_s: &(), buf: Vec<u8>, _: usize| -> (crate::Result<usize>, Vec<u8>) { (Ok(0), buf) },
        async |_s: ()| {},
    );
    Pinc::builder_on(Wall(wall))
        .local_addr("192.0.2.1:4000".parse().unwrap())
        .hub()
        .relay_role(crate::relay::Relay::builder(), carriers)
        .build(
            async |_buf: &mut [u8]| -> Result<(usize, SocketAddr), Infallible> { core::future::pending().await },
            async |pkt: &[u8], _to: SocketAddr| -> Result<usize, Infallible> { Ok(pkt.len()) },
            async |_at: u64| {},
        )
        .unwrap()
}

/// A platform whose clock the test sets.
#[derive(Clone)]
struct Clock(Rc<core::cell::Cell<u64>>);

impl Platform for Clock {
    type Instant = u64;
    type Error = Infallible;

    fn now(&self) -> u64 {
        self.0.get()
    }

    fn wall_ns(&self) -> u64 {
        1_700_000_000_000_000_000
    }

    fn random(&self, out: &mut [u8]) -> Result<(), Infallible> {
        for (i, b) in (0u8..=255).cycle().zip(out) {
            *b = i.wrapping_mul(31).wrapping_add(7);
        }
        Ok(())
    }
}

/// An endpoint whose start is the clock's value now.
fn started(clock: &Clock) -> Endpoint<impl Hosted<Platform = Clock> + use<>> {
    Pinc::builder_on(clock.clone())
        .limits(crate::Limits {
            connections: 4,
            ..crate::Limits::default()
        })
        .build(
            async |_buf: &mut [u8]| -> Result<(usize, SocketAddr), Infallible> { core::future::pending().await },
            async |pkt: &[u8], _to: SocketAddr| -> Result<usize, Infallible> { Ok(pkt.len()) },
            async |_at: u64| {},
        )
        .unwrap()
}

#[test]
fn the_clock_saturates_and_follows_the_platform() {
    for start in [0, u64::MAX - 5, T0] {
        let clock = Clock(Rc::new(core::cell::Cell::new(start)));
        let ep = started(&clock);
        let sh = &ep.0.shared;
        assert_eq!(sh.now(), T0);
        clock.0.set(start.saturating_add(3));
        assert_eq!(sh.now(), T0 + 3);
        clock.0.set(u64::MAX);
        assert_eq!(sh.now(), T0.saturating_add(u64::MAX - start));
        // below the start the clock reads as the start, and a step back follows the platform
        clock.0.set(start.saturating_sub(1));
        assert_eq!(sh.now(), T0);
        clock.0.set(start.saturating_add(2));
        let a = sh.now();
        clock.0.set(start.saturating_add(1));
        assert_eq!(a - sh.now(), 1);
        assert_eq!(sh.instant(0), start);
        assert_eq!(sh.instant(T0 - 1), start);
        assert_eq!(sh.instant(T0), start);
        assert_eq!(sh.instant(T0 + 4), start.saturating_add(4));
        assert_eq!(sh.instant(u64::MAX), start.saturating_add(u64::MAX - T0));
    }
}

/// A wall clock below the endpoint's first instant is still the role's clock: wall time plus the time elapsed.
#[test]
fn the_roles_clock_is_the_wall_clock_even_below_the_endpoints_first_instant() {
    let (wall, sec) = (3_000_000_000, 1_000_000_000);
    let origin = wall;
    assert_eq!(role_clock(origin, T0), wall, "the role starts at the wall clock");
    assert_eq!(role_clock(origin, T0 + 2 * sec), wall + 2 * sec);
    assert_eq!(endpoint_clock(origin, wall + 2 * sec), T0 + 2 * sec);
}

/// The relay role's clock is read from the platform's wall clock when the endpoint is built, below the endpoint's
/// first instant or not.
#[test]
fn the_role_starts_at_the_platforms_wall_clock() {
    let wall = 3 * SEC;
    let ep = rolled(wall);
    let sh = &ep.0.shared;
    let rnow = sh.relay_now(T0);
    assert_eq!(rnow, wall, "the role's clock does not start at the wall clock");
    // the role runs its timers, so its next deadline counts from the clock it was built on
    let mut role = sh.role().unwrap();
    role.tick(rnow);
    let due = role.due(rnow).unwrap();
    assert!(
        due <= rnow + SEC,
        "the role's first deadline is {due} at {rnow}, more than a second away"
    );
}

/// A datagram for a member that the endpoint hands over before the role restored its mailbox is taken and counted
/// as dropped, and the role sends nothing.
#[test]
fn a_datagram_for_a_member_before_the_role_is_restored_is_dropped_and_counted() {
    let ep = rolled(3 * SEC);
    let sh = &ep.0.shared;
    let to = pinc_core::relay_addr(false, 0, 1);
    let mut core = sh.lock().unwrap();
    assert!(
        sh.role_carries(&mut core, T0, &to, b"x", 1),
        "the datagram was left to the socket"
    );
    drop(core);
    assert!(sh.role_outgoing(&mut [0u8; 1500]).is_none());
    assert_eq!(ep.relay_stats().unwrap().hub_dropped, 1, "the drop was not counted");
}

/// A batch of several datagrams dropped before the role is restored counts every datagram.
#[test]
fn a_batch_dropped_before_the_role_is_restored_counts_every_datagram() {
    let ep = rolled(3 * SEC);
    let sh = &ep.0.shared;
    let to = pinc_core::relay_addr(false, 0, 1);
    let mut core = sh.lock().unwrap();
    assert!(sh.role_carries(&mut core, T0, &to, b"abcdef", 2));
    drop(core);
    assert_eq!(
        ep.relay_stats().unwrap().hub_dropped,
        3,
        "the drop was not counted per datagram"
    );
}

/// A member the role's hub knows by its relay path address, on an endpoint whose role is not restored yet.
fn rolled_with_member() -> (Endpoint<impl Hosted>, SocketAddr) {
    let ep = rolled(3 * SEC);
    let node = pinc_crypto::NodeId {
        alg: pinc_crypto::IdentityAlg::Ed25519,
        bytes: [9; 32],
    };
    let to = ep.0.shared.role().unwrap().member_addr(&node).unwrap();
    (ep, to)
}

/// Before the role is restored, a datagram for a member the hub knows is not handed to the role: it is taken and
/// counted as dropped, where the role would have sent it down the member's carrier and counted nothing.
#[test]
fn a_datagram_for_a_known_member_is_not_handed_to_a_role_that_is_not_restored() {
    let (ep, to) = rolled_with_member();
    let sh = &ep.0.shared;
    let mut core = sh.lock().unwrap();
    assert!(sh.role_carries(&mut core, T0, &to, b"x", 1));
    drop(core);
    assert_eq!(
        ep.relay_stats().unwrap().hub_dropped,
        1,
        "the role was handed a datagram before its mailbox was restored"
    );
}

/// Before the role is restored, what the role would send is held back: the answer to an address query waits.
#[test]
fn a_role_that_is_not_restored_sends_nothing() {
    let ep = rolled(3 * SEC);
    let sh = &ep.0.shared;
    let mut q = [0u8; 16];
    let n = pinc_connect::relay::datagram::Datagram::Qad { nonce: [7; 8] }
        .encode(&mut q)
        .unwrap();
    let mut core = sh.lock().unwrap();
    sh.role_datagrams(&mut core, T0, "198.51.100.7:5000".parse().unwrap(), &mut q[..n], n);
    drop(core);
    assert!(
        sh.role_outgoing(&mut [0u8; 1500]).is_none(),
        "a role that is not restored sent a datagram"
    );
    assert!(
        sh.role().unwrap().outgoing(&mut [0u8; 1500]).is_some(),
        "the role did not queue an answer, so the test proves nothing"
    );
}

/// The role is built at the platform's wall clock: its first check falls a second after it, not after the
/// endpoint's first instant (the machine's own sweep, run at half a second, is due later than that check).
#[test]
fn the_role_is_built_at_the_platforms_wall_clock() {
    let wall = 3 * SEC;
    let ep = rolled(wall);
    let sh = &ep.0.shared;
    let mut role = sh.role().unwrap();
    role.tick(wall + SEC / 2);
    assert_eq!(
        role.due(wall + SEC / 2),
        Some(wall + SEC),
        "the role was built at a clock other than the wall clock"
    );
}
