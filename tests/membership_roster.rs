//! How a hub's roster settles: the second probe before a confirmation takes a path of its own and must have left,
//! and a hub that learns of a leave from another hub drops the member as left.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::struct_excessive_bools,
    clippy::redundant_closure_for_method_calls,
    clippy::unused_self
)]

#[path = "membership_world.rs"]
mod world;

use vinc_membership::codec::{Path, ty};
use vinc_membership::{Event, Route, Trace};
use world::{LEAVE, SEC, World, id};

vinc_tests::install_counting_allocator!();

const START: u64 = 100 * SEC;

fn started(hubs: usize, members: usize) -> World {
    let mut w = World::new(hubs, members, START);
    w.attach_all();
    w.run(3 * SEC);
    w
}

fn traces(w: &World, i: usize, f: impl Fn(&Trace) -> bool) -> usize {
    w.traces[i].iter().filter(|t| f(t)).count()
}

fn probes_to(w: &World, from: usize, to: usize) -> Vec<Route> {
    w.sent_types
        .iter()
        .filter(|s| s.1 == from && s.2 == to && s.3 == ty::PROBE)
        .map(|s| s.4)
        .collect()
}

fn probe_paths(w: &World, hub: usize, member: usize) -> Vec<Path> {
    w.traces[hub]
        .iter()
        .filter_map(|t| match t {
            Trace::ProbeSent { member: m, path } if *m == id(member) => Some(*path),
            _ => None,
        })
        .collect()
}

fn downs(w: &World, from: usize, to: usize) -> usize {
    w.sent_types
        .iter()
        .filter(|s| s.1 == from && s.2 == to && s.3 == ty::DOWN)
        .count()
}

#[test]
fn a_member_whose_direct_path_alone_is_cut_is_not_confirmed_down_while_another_hubs_relay_reaches_it() {
    let mut w = started(2, 1);
    w.direct.insert((0, 2));
    w.run(40 * SEC);
    // The session runs on the direct path; the path between the hub and the member is cut, the other hub's relay is not.
    w.cut.insert((0, 2));
    w.set_carrier_gone(0, 2);
    w.run(10 * SEC);
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })),
        0,
        "the relay reached the member"
    );
    assert_eq!(downs(&w, 0, 1), 0, "no other hub is told");
    assert_eq!(w.nodes[0].m.roster_len(), 2, "the member and the other hub are kept");
    assert!(
        probes_to(&w, 0, 2).contains(&Route::Via(id(1))),
        "the second probe took the other hub's relay: {:?}",
        probes_to(&w, 0, 2)
    );
}

#[test]
fn a_member_unreachable_on_every_path_is_confirmed_down_on_two_different_paths() {
    let mut w = started(2, 1);
    w.direct.insert((0, 2));
    w.run(40 * SEC);
    w.cut.insert((0, 2));
    w.cut.insert((1, 2));
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.lease_of(&id(2)).is_none()));
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 1);
    let routes = probes_to(&w, 0, 2);
    assert_eq!(routes.len(), 2, "{routes:?}");
    assert!(routes.contains(&Route::Reply) && routes.contains(&Route::Via(id(1))), "{routes:?}");
    assert_eq!(probe_paths(&w, 0, 2), [Path::Session, Path::Relay]);
    assert_eq!(downs(&w, 0, 1), 1, "the other hub is told");
}

#[test]
fn a_second_probe_the_host_refused_is_not_counted_as_sent() {
    let mut w = started(2, 1);
    w.run(40 * SEC);
    w.nodes[0].h.refuse_via.insert(id(1));
    w.cut.insert((1, 2));
    w.set_carrier_gone(0, 2);
    w.run(10 * SEC);
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })),
        0,
        "no second probe left, so no confirmation"
    );
    assert_eq!(downs(&w, 0, 1), 0);
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::NoIndependentPath { .. })), 1);
    assert_eq!(probe_paths(&w, 0, 2), [Path::Session], "only the session probe is recorded");
    assert_eq!(w.nodes[0].m.roster_len(), 2, "the lease decides");
}

#[test]
fn a_refused_relay_makes_the_hub_try_the_next_hubs_relay() {
    let mut w = started(3, 1);
    w.run(40 * SEC);
    w.nodes[0].h.refuse_via.insert(id(1));
    w.cut.insert((0, 3));
    w.cut.insert((1, 3));
    w.cut.insert((2, 3));
    w.set_carrier_gone(0, 3);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.lease_of(&id(3)).is_none()));
    let routes = probes_to(&w, 0, 3);
    assert!(routes.contains(&Route::Via(id(2))), "{routes:?}");
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 1);
}

/// Three hubs; members 3 (the leaver), 4, 5 and 6 homed on hubs 0, 1 and 2.
fn three_hubs_with_a_leaver() -> World {
    let mut w = World::new(3, 4, START);
    for (m, hub) in [(4, 0), (5, 1), (6, 2)] {
        for h in 0..3 {
            w.set_rtt(m, h, if h == hub { 20 * world::MS } else { 120 * world::MS });
        }
    }
    w.attach_all();
    w.run(30 * SEC);
    w
}

#[test]
fn a_member_that_leaves_while_one_hubs_close_is_lost_is_reported_as_left_everywhere() {
    let mut w = three_hubs_with_a_leaver();
    for i in [4, 5, 6] {
        assert!(w.has(i, 3), "member {i} lists the leaver before it leaves");
    }
    let t = w.now;
    w.leave(3);
    w.close_session(3, 0, LEAVE);
    w.close_session(3, 1, LEAVE);
    // The close to hub 2 is lost, and the member is gone.
    w.crash(3);
    w.run(10 * SEC);
    for i in [4, 5, 6] {
        let at = w.first_event_time(i, |e| matches!(e, Event::MemberLeft { member } if *member == id(3)));
        assert!(at.is_some_and(|at| at - t < 10 * SEC), "member {i} saw the leave within the push delay: {at:?}");
    }
    w.run(120 * SEC);
    for i in [4, 5, 6] {
        assert_eq!(
            w.count_events(i, |e| matches!(e, Event::MemberLeft { member } if *member == id(3))),
            1,
            "member {i}"
        );
        assert_eq!(
            w.count_events(i, |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(3))),
            0,
            "member {i} saw no confirmation after the lease"
        );
        assert!(!w.has(i, 3));
    }
    assert!(w.nodes[2].m.lease_of(&id(3)).is_none(), "hub 2 dropped the lease");
}
