//! A member that switches its home to a hub that never heard of another member keeps that member in its view: the
//! crash of that member never reaches it, not even after every partition healed.
//!
//! The real hub and member machines of `pinc-membership` over the membership test world (`membership_world.rs`),
//! through the scenario TLC finds on `MembershipSys` (`LiveCompleteAll` and `LiveConverged` violated). World indices
//! 0 and 1 are the hubs 1 and 2 of the model, 2 and 3 its members 3 and 4; times are seconds after the start.
//!
//! * 0 s: hub 1 is cut from hub 2, hub 2 from member 4. Member 3 homes on hub 1 (100 ms against 120 ms) and lists
//!   member 4, which only hub 1 knows.
//! * 100 s: hub 2 comes to 40 ms from member 3, which switches its home to hub 2. Hub 2's snapshot omits member 4,
//!   which hub 2 has never heard of, and member 3's copy of hub 1 still lists it.
//! * 130 s: member 4 crashes. Hub 1 lets its lease go a lease later and reports it down to its attached hubs (hub 2 is
//!   cut) and to the members homed on it (member 3 no longer is).
//! * 250 s: every cut heals and hub 2 dials hub 1 again. Neither hub lists member 4.
//! * 400 s: member 3 still lists member 4.
//!
//! The control runs (no hub cut; no home switch) take member 4 out of member 3's view.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::doc_markdown,
    clippy::struct_excessive_bools,
    clippy::unused_self,
    clippy::redundant_closure_for_method_calls,
    clippy::too_many_lines
)]

#[path = "membership_world.rs"]
mod world;

use pinc_membership::Trace;
use world::{MS, SEC, World, id};

const START: u64 = 100 * SEC;
/// Hubs 1 and 2 of the model.
const H1: usize = 0;
const H2: usize = 1;
/// Member 3 of the model: the one whose view is checked.
const N: usize = 2;
/// Member 4 of the model: the one that crashes.
const M: usize = 3;

fn at(w: &mut World, secs: u64) {
    let t = START + secs * SEC;
    assert!(w.now <= t);
    w.run(t - w.now);
}

fn view(w: &World, i: usize) -> Vec<usize> {
    (0..4).filter(|&j| w.has(i, j)).collect()
}

/// The scenario, with or without the cut between the hubs and the home switch of member 3; the world at 400 s.
fn scenario(hub_cut: bool, switch: bool) -> World {
    let mut w = World::new(2, 2, START);
    if hub_cut {
        w.cut.insert((H1, H2));
    }
    w.cut.insert((H2, M));
    w.set_rtt(N, H1, 100 * MS);
    w.set_rtt(N, H2, 120 * MS);
    w.attach_all();
    at(&mut w, 100);
    assert_eq!(w.nodes[N].m.primary(), Some(&id(H1)), "member 3 homes on hub 1");
    assert!(w.has(N, M), "member 3 lists member 4 through hub 1");
    assert_eq!(w.has(H2, M), !hub_cut, "hub 2 knows member 4 only through hub 1");
    if switch {
        w.set_rtt(N, H2, 40 * MS);
    }
    at(&mut w, 130);
    let home = if switch { H2 } else { H1 };
    assert_eq!(w.nodes[N].m.primary(), Some(&id(home)), "member 3's home at 130 s");
    assert!(w.has(N, M), "member 3 still lists member 4 before the crash");
    w.crash(M);
    at(&mut w, 250);
    assert!(!w.has(H1, M), "hub 1 let member 4's lease go");
    assert!(!w.has(H2, M));
    // Every cut heals; hub 2 dials hub 1 again (member 4 is down and dials nothing).
    w.cut.clear();
    if hub_cut {
        w.connect(H2, H1);
    }
    at(&mut w, 400);
    assert!(
        w.sessions.contains(&(H2, H1)) && w.sessions.contains(&(N, H1)) && w.sessions.contains(&(N, H2)),
        "every session of the live nodes is up: {:?}",
        w.sessions
    );
    for h in [H1, H2] {
        assert!(!w.has(h, M), "hub {} lists no member 4: {:?}", h + 1, view(&w, h));
    }
    w
}

fn assert_gone(w: &World, case: &str) {
    let crashed = START + 130 * SEC;
    assert!(
        !w.has(N, M),
        "{case}: at {} s, {} s after member 4 crashed and 150 s after every cut healed, member 3 (home: hub {}) still \
         lists member 4; member 3's view {:?}, hub 1's {:?}, hub 2's {:?} (model numbering: world index + 1)",
        (w.now - START) / SEC,
        (w.now - crashed) / SEC,
        usize::from(w.nodes[N].m.primary().unwrap()[0]),
        view(w, N).iter().map(|i| i + 1).collect::<Vec<_>>(),
        view(w, H1).iter().map(|i| i + 1).collect::<Vec<_>>(),
        view(w, H2).iter().map(|i| i + 1).collect::<Vec<_>>(),
    );
}

#[test]
fn a_crash_reaches_a_member_whose_new_home_never_heard_of_the_crashed_member() {
    let w = scenario(true, true);
    assert_gone(&w, "hub cut, home switch");
}

#[test]
fn control_without_the_hub_cut_the_crash_reaches_the_member() {
    let w = scenario(false, true);
    assert_gone(&w, "no hub cut");
}

#[test]
fn control_without_the_home_switch_the_crash_reaches_the_member() {
    let w = scenario(true, false);
    assert_gone(&w, "no home switch");
}

/// Member 3 switches its home to hub 2, which has never heard of member 4 (alive); the cut between hub 2 and member 4
/// heals before the omission lease of 80 s ends, hub 2 lists member 4, and member 3 keeps it to the end.
#[test]
fn a_member_the_home_lists_again_before_the_lease_ends_stays() {
    let mut w = World::new(2, 2, START);
    w.cut.insert((H1, H2));
    w.cut.insert((H2, M));
    w.set_rtt(N, H1, 100 * MS);
    w.set_rtt(N, H2, 120 * MS);
    w.attach_all();
    at(&mut w, 100);
    assert!(w.has(N, M), "member 3 lists member 4 through hub 1");
    w.set_rtt(N, H2, 40 * MS);
    at(&mut w, 110);
    assert_eq!(w.nodes[N].m.primary(), Some(&id(H2)), "member 3's home is hub 2");
    assert!(w.has(N, M), "the omission lease keeps member 4 in the view");
    w.cut.clear();
    w.connect(M, H2);
    at(&mut w, 400);
    assert!(w.has(H2, M), "hub 2 listed member 4 again");
    assert!(w.has(N, M), "member 3 keeps member 4: {:?}", view(&w, N));
}

/// A complete snapshot of a hub that is not the confirmed home starts no omission clock for a member outside that
/// hub's copy: hub 2 never held member 4 and member 3 stays homed on hub 1.
#[test]
fn a_snapshot_of_a_hub_that_is_not_the_home_starts_no_clock_for_members_outside_its_copy() {
    let mut w = World::new(2, 2, START);
    w.cut.insert((H1, H2));
    w.cut.insert((H2, M));
    w.set_rtt(N, H1, 100 * MS);
    w.set_rtt(N, H2, 120 * MS);
    w.attach_all();
    at(&mut w, 100);
    w.snapshot_to(H2, N);
    at(&mut w, 400);
    assert_eq!(w.nodes[N].m.primary(), Some(&id(H1)), "member 3 stays homed on hub 1");
    assert!(w.has(N, M), "member 3 lists member 4");
    let m = id(M);
    assert!(
        !w.traces[N]
            .iter()
            .any(|t| matches!(t, Trace::Absent { member } if *member == m)),
        "no omission clock for member 4 at member 3"
    );
}
