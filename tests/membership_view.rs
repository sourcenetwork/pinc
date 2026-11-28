//! The member view: the home snapshot, the union rule, hub staleness, quiet resync after a late timer and after a
//! heal, reconnect snapshots, primary-hub hysteresis, PULSE HELLO suppression, MOVE_TAG and MOVE_SETTLE, and the
//! events.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::too_many_lines,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::struct_excessive_bools,
    clippy::cast_possible_truncation,
    clippy::doc_markdown,
    clippy::bool_to_int_with_if,
    clippy::manual_range_contains,
    clippy::manual_assert_eq,
    clippy::redundant_closure_for_method_calls,
    clippy::assert_is_empty,
    clippy::len_zero,
    clippy::unused_self,
    clippy::type_complexity,
    clippy::needless_pass_by_value,
    clippy::too_many_arguments
)]

#[path = "membership_world.rs"]
mod world;

use pinc_membership::codec::{Alive, Down, Entry, Frame, Path, Probe, Proof, Record, Snap, entry_bytes, ty};
use pinc_membership::consts::{LEASE, NODE_TICK, QUIET, RECHECK_GAP, SLOW_TICK, WAKE_GAP};
use pinc_membership::event::{QuietCause, Removal};
use pinc_membership::{Event, NodeId, Trace};
use world::{Bc, LEAVE, MS, SEC, World, id};

const START: u64 = 100 * SEC;

fn started(hubs: usize, members: usize) -> World {
    let mut w = World::new(hubs, members, START);
    w.attach_all();
    w.run(5 * SEC);
    w
}

fn rec(epoch: u64, seq: u16, ver: u16) -> Record {
    Record {
        inc: (epoch << 16) | u64::from(seq),
        ver,
        thash: [9; 8],
    }
}

fn delta(w: &mut World, to: usize, from: usize, m: &NodeId, r: Record, alive: Alive) {
    w.inject(
        to,
        from,
        &Frame::Delta(Entry {
            member: m,
            rec: r,
            alive,
        }),
    );
}

fn traces(w: &World, i: usize, f: impl Fn(&Trace) -> bool) -> usize {
    w.traces[i].iter().filter(|t| f(t)).count()
}

fn hello_flags(w: &World, from: usize, to: usize, after: u64) -> Vec<u8> {
    w.frames
        .iter()
        .filter(|f| f.0 >= after && f.1 == from && f.2 == to && f.3[4] == ty::HELLO)
        .map(|f| f.3[24])
        .collect()
}

#[test]
fn the_view_follows_the_home_snapshot_and_its_epoch_only_increases() {
    let w = started(2, 3);
    let me = 2;
    let got: Vec<NodeId> = w.members_of(me);
    let want: Vec<NodeId> = [0, 1, 3, 4].iter().map(|&i| id(i)).collect();
    assert_eq!(got, want, "hubs and the other members, never the node itself");
    assert_eq!(w.count_events(me, |e| matches!(e, Event::MemberJoined { .. })), 4);
    let epochs: Vec<u64> = w.events[me]
        .iter()
        .filter_map(|(_, e)| {
            if let Event::ViewChanged { epoch, .. } = e {
                Some(*epoch)
            } else {
                None
            }
        })
        .collect();
    assert!(epochs.windows(2).all(|p| p[0] < p[1]), "{epochs:?}");
    assert_eq!(epochs.last().copied(), Some(w.nodes[me].m.view_epoch()));
}

#[test]
fn a_hub_view_is_the_union_of_hub_copies_and_the_highest_incarnation_wins() {
    let mut w = started(3, 0);
    let x = id(30);
    delta(&mut w, 0, 1, &x, rec(7, 0, 1), Alive::Alive);
    let seen = |w: &World| w.nodes[0].m.members().find(|(m, _)| **m == x).map(|(_, r)| *r);
    assert_eq!(seen(&w).unwrap().inc, 7 << 16);
    assert_eq!(
        w.count_events(0, |e| matches!(e, Event::MemberJoined { member } if *member == x)),
        1
    );
    // The hub's own roster hears the member with a newer incarnation: it wins and the member joins again.
    w.inject(
        0,
        0,
        &Frame::Hello(pinc_membership::codec::Hello {
            rec: rec(9, 0, 1),
            snap: false,
            homed: false,
        }),
    );
    let _ = x;
    // An older incarnation from the other hub does not take the place back.
    delta(&mut w, 0, 1, &x, rec(8, 0, 1), Alive::Alive);
    assert_eq!(seen(&w).unwrap().inc, 8 << 16, "8 beats 7");
    delta(&mut w, 0, 2, &x, rec(6, 0, 1), Alive::Alive);
    assert_eq!(seen(&w).unwrap().inc, 8 << 16, "6 does not beat 8");
    delta(&mut w, 0, 2, &x, rec(6, 0, 1), Alive::Down);
    // Within one epoch a higher record sequence updates the record: a stack change.
    delta(&mut w, 0, 1, &x, rec(8, 1, 5), Alive::Alive);
    assert_eq!((seen(&w).unwrap().inc, seen(&w).unwrap().ver), ((8 << 16) | 1, 5));
    assert_eq!(
        w.count_events(0, |e| matches!(e, Event::StackChanged { version: 5, .. })),
        1
    );
    // The view is the union: hub 1 withdrawing it leaves the member only if another copy lists it.
    delta(&mut w, 0, 1, &x, rec(8, 1, 5), Alive::Down);
    assert!(seen(&w).is_none(), "no other copy lists it");
    assert_eq!(
        w.count_events(
            0,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == x)
        ),
        1
    );
}

#[test]
fn a_hub_silent_for_75_s_is_stale_and_its_copy_is_dropped_while_another_is_fresh() {
    let mut w = started(2, 1);
    let m = 2;
    assert!(w.nodes[m].m.primary().is_some());
    // Cut the member from hub 1 only, and from its keepalives. The home hub keeps the view.
    let home = w.nodes[m].m.primary().copied().unwrap();
    let other = if home == id(0) { 1 } else { 0 };
    w.cut.insert((other, m));
    w.run(60 * SEC);
    assert_eq!(traces(&w, m, |t| matches!(t, Trace::HubStale { .. })), 0, "not yet");
    w.run(25 * SEC);
    assert_eq!(
        traces(&w, m, |t| matches!(t, Trace::HubStale { hub } if *hub == id(other))),
        1
    );
    assert!(
        w.nodes[m].h.closed.iter().any(|c| c.0 == id(other)),
        "its session is closed so a fresh one is made"
    );
    assert!(w.has(m, 0) && w.has(m, 1), "the view is unchanged");
}

#[test]
fn a_member_that_hears_no_hub_keeps_its_view() {
    let mut w = started(2, 3);
    let before = w.members_of(2);
    w.cut.insert((0, 2));
    w.cut.insert((1, 2));
    w.run(300 * SEC);
    assert_eq!(
        w.members_of(2),
        before,
        "isolation guard: nothing is removed on silence alone"
    );
    assert_eq!(w.count_events(2, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
}

#[test]
fn a_snapshot_never_removes_it_notes_the_absence_and_a_lease_without_a_listing_ends_it() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let home = *w.nodes[m].m.primary().unwrap();
    let hub = usize::from(home[0]) - 1;
    let mut raw = Vec::new();
    for (mem, r) in w.nodes[m].m.members() {
        if *mem != id(x) {
            raw.extend_from_slice(&entry_bytes(mem, r, Alive::Alive));
        }
    }
    // A partial snapshot (a young hub) that omits the member ages it like any completed one: it stays, noted as absent.
    w.inject(m, hub, &Frame::Snap(Snap::new(true, false, &raw).unwrap()));
    assert!(w.has(m, x));
    assert_eq!(traces(&w, m, |t| matches!(t, Trace::Absent { .. })), 1);
    assert_eq!(w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
    // A complete snapshot that omits the member: it stays, already absent since the partial snapshot, and nothing is
    // reported.
    w.inject(m, hub, &Frame::Snap(Snap::new(false, false, &raw).unwrap()));
    assert!(w.has(m, x), "a snapshot never removes a member on its own");
    assert_eq!(traces(&w, m, |t| matches!(t, Trace::Absent { .. })), 1);
    assert_eq!(w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
    // The hub lists it again (a delta): the absence ends, and nothing removes it however long we wait.
    let r = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(x)).unwrap().1;
    delta(&mut w, m, hub, &id(x), r, Alive::Alive);
    w.run(200 * SEC);
    assert!(w.has(m, x));
    assert_eq!(w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
    // Omitted again and never listed: removed one lease after the omission.
    w.inject(m, hub, &Frame::Snap(Snap::new(false, false, &raw).unwrap()));
    let t0 = w.now;
    w.run(75 * SEC);
    assert!(w.has(m, x), "still inside the lease");
    assert!(w.run_until(15 * SEC, |w| !w.has(m, x)));
    let took = w
        .first_event_time(
            m,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(x)),
        )
        .unwrap()
        - t0;
    assert!(took >= 80 * SEC && took < 86 * SEC, "{} s", took / SEC);
    assert!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Removed {
                why: Removal::LeaseExpired,
                ..
            }
        )) == 1
    );
}

#[test]
fn the_first_snapshot_of_a_new_home_never_brings_back_a_member_that_left() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let home = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let other = 1 - home;
    // The member leaves; only the home sends the view's deltas, so the other hub's copy here still lists it.
    w.leave(x);
    for hub in 0..2 {
        w.close_session(x, hub, LEAVE);
    }
    w.run(5 * SEC);
    assert!(!w.has(m, x), "the home told the member");
    // The home goes away and the other hub becomes the home; its snapshot omits the member that left.
    w.cut.insert((home, m));
    w.close_session(m, home, 0);
    assert!(w.run_until(120 * SEC, |w| w.nodes[m].m.primary() == Some(&id(other))));
    w.snapshot_to(other, m);
    w.run(5 * SEC);
    assert!(
        !w.has(m, x),
        "an omission keeps a listed member, it never lists one again"
    );
    assert_eq!(
        traces(&w, m, |t| matches!(t, Trace::Absent { member } if *member == id(x))),
        0
    );
}

#[test]
fn a_removal_held_while_no_home_is_confirmed_is_decided_when_the_home_is() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let home = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let other = 1 - home;
    // The member leaves while the member is cut from its home: the hubs drop it, the member is not told.
    w.cut.insert((home, m));
    w.leave(x);
    for hub in 0..2 {
        w.close_session(x, hub, LEAVE);
    }
    w.run(5 * SEC);
    assert!(w.has(m, x));
    w.close_session(m, home, 0);
    assert!(w.run_until(120 * SEC, |w| w.nodes[m].m.primary() == Some(&id(other))));
    // Both hub copies here lose the member while the new home is not confirmed: the removal is held.
    let r = w.nodes[m]
        .m
        .members()
        .find(|(k, _)| **k == id(x))
        .map(|(_, r)| *r)
        .unwrap();
    for hub in [home, other] {
        delta(&mut w, m, hub, &id(x), r, Alive::Left);
    }
    assert!(w.has(m, x), "held: no home view is confirmed yet");
    assert_eq!(
        traces(&w, m, |t| matches!(t, Trace::Deferred { .. })),
        0,
        "held by the missing home"
    );
    w.snapshot_to(other, m);
    w.run(20 * SEC);
    assert!(
        !w.has(m, x),
        "the home view omits it and no copy lists it: the held removal is decided"
    );
}

#[test]
fn a_member_only_a_stale_hub_listed_is_aged_by_the_new_home_not_removed() {
    // The hubs never meet, so hub 1 never hears of member 3, which is attached to hub 0 only.
    let mut w = World::new(2, 2, START);
    let (m, x) = (2, 3);
    w.cut.insert((0, 1));
    w.connect(m, 0);
    w.connect(m, 1);
    w.connect(x, 0);
    w.run(5 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(0)));
    assert!(w.has(m, x));
    // The home goes silent: the member switches to hub 1, whose snapshot omits member 3.
    w.cut.insert((0, m));
    assert!(w.run_until(120 * SEC, |w| w.nodes[m].m.primary() == Some(&id(1))));
    w.run(5 * SEC);
    assert!(
        w.has(m, x),
        "a snapshot never removes a member on its own: the omission starts its lease"
    );
    assert_eq!(
        w.count_events(
            m,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(x))
        ),
        0
    );
    assert!(
        traces(&w, m, |t| matches!(t, Trace::HubStale { hub } if *hub == id(0))) >= 1,
        "the stale copy goes once the home is confirmed"
    );
    // No hub lists it again: a lease after the omission it leaves, for its lease.
    assert!(w.run_until(LEASE + 10 * SEC, |w| !w.has(m, x)));
    assert_eq!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Removed {
                member,
                why: Removal::LeaseExpired
            } if *member == id(x)
        )),
        1
    );
}

#[test]
fn a_down_delta_of_the_same_or_a_newer_incarnation_removes_an_older_one_is_ignored() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let r = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(x)).unwrap().1;
    let epoch = r.inc >> 16;
    delta(&mut w, m, hub, &id(x), rec(epoch - 1, 0, r.ver), Alive::Down);
    assert!(w.has(m, x), "a report about an older incarnation is stale");
    delta(&mut w, m, hub, &id(x), r, Alive::Down);
    assert!(!w.has(m, x));
    assert_eq!(
        w.count_events(
            m,
            |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(x))
        ),
        1
    );
    // A DOWN frame with proof removes too.
    let y = 4;
    let proof = Proof::new(
        2000,
        &[
            Probe {
                age_ms: 1000,
                path: Path::Session,
            },
            Probe {
                age_ms: 900,
                path: Path::Relay,
            },
        ],
    )
    .unwrap();
    let inc = w.nodes[y].m.incarnation();
    w.inject(
        m,
        hub,
        &Frame::Down(Down {
            member: &id(y),
            inc,
            proof,
        }),
    );
    assert!(!w.has(m, y));
    // A graceful leave is told apart from a down.
    let mut w = started(2, 3);
    let hub = usize::from(w.nodes[2].m.primary().unwrap()[0]) - 1;
    let r = *w.nodes[2].m.members().find(|(mem, _)| **mem == id(3)).unwrap().1;
    delta(&mut w, 2, hub, &id(3), r, Alive::Left);
    assert_eq!(
        w.count_events(2, |e| matches!(e, Event::MemberLeft { member } if *member == id(3))),
        1
    );
    assert_eq!(w.count_events(2, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
}

/// A snapshot body listing every view member of `m` but `x`.
fn raw_without(w: &World, m: usize, x: usize) -> Vec<u8> {
    let mut raw = Vec::new();
    for (mem, r) in w.nodes[m].m.members() {
        if *mem != id(x) {
            raw.extend_from_slice(&entry_bytes(mem, r, Alive::Alive));
        }
    }
    raw
}

fn absent_traces(w: &World, m: usize) -> usize {
    traces(w, m, |t| matches!(t, Trace::Absent { .. }))
}

fn down_events(w: &World, m: usize) -> usize {
    w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
}

#[test]
fn a_partial_snapshot_ages_what_it_omits() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let raw = raw_without(&w, m, x);
    w.inject(m, hub, &Frame::Snap(Snap::new(true, false, &raw).unwrap()));
    assert!(w.has(m, x));
    assert_eq!(absent_traces(&w, m), 1);
    assert_eq!(down_events(&w, m), 0);
    w.run(75 * SEC);
    assert!(w.has(m, x), "still inside the lease");
    assert!(
        w.run_until(15 * SEC, |w| !w.has(m, x)),
        "a lease after the omission it is gone"
    );
}

#[test]
fn a_partial_snapshot_omission_is_cleared_by_a_delta() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let raw = raw_without(&w, m, x);
    let r = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(x)).unwrap().1;
    w.inject(m, hub, &Frame::Snap(Snap::new(true, false, &raw).unwrap()));
    delta(&mut w, m, hub, &id(x), r, Alive::Alive);
    w.run(200 * SEC);
    assert!(w.has(m, x));
    assert_eq!(down_events(&w, m), 0);
}

#[test]
fn a_home_is_confirmed_only_by_the_last_frame() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let a = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let b = 1 - a;
    // Only a's copy lists x; a's session drops and b becomes the home.
    let r = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(x)).unwrap().1;
    delta(&mut w, m, b, &id(x), r, Alive::Down);
    w.with(m, |n, h, now| n.session_down(h, now, &id(a), 0));
    assert_eq!(w.nodes[m].m.primary(), Some(&id(b)), "b is the home now");
    let absent_x = |w: &World| traces(w, m, |t| matches!(t, Trace::Absent { member } if *member == id(x)));
    let before = absent_x(&w);
    // A first frame of b's snapshot with no entries does not make b's copy the only source: a later look at x (here
    // a repeated report from b, which always recomputes) holds it. With the home taken at the first frame, b's copy
    // alone decided and x was removed as Reported.
    w.inject(m, b, &Frame::Snap(Snap::new(false, true, &[]).unwrap()));
    delta(&mut w, m, b, &id(x), r, Alive::Down);
    assert!(w.has(m, x), "the home is not confirmed by an earlier frame");
    assert_eq!(down_events(&w, m), 0);
    // The last frame confirms b and ages what it omits: x stays, noted as absent once.
    w.inject(m, b, &Frame::Snap(Snap::new(false, false, &[]).unwrap()));
    assert!(w.has(m, x));
    assert_eq!(down_events(&w, m), 0);
    assert_eq!(absent_x(&w), before + 1);
}

/// Three hubs, a member `m` whose home `a` went away, and the hub `b` it moved to, which has not confirmed anything
/// yet. Returns the world, `b`, the third hub `c`, and x's record in the view.
fn moved_home() -> (World, usize, usize, Record) {
    let mut w = started(3, 3);
    let (m, x) = (3, 5);
    let a = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let r = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(x)).unwrap().1;
    w.with(m, |n, h, now| n.session_down(h, now, &id(a), 0));
    let b = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    assert_ne!(a, b);
    let c = 3 - a - b;
    (w, b, c, r)
}

fn x_epoch(w: &World, m: usize, x: usize) -> Option<u64> {
    w.nodes[m]
        .m
        .members()
        .find(|(k, _)| **k == id(x))
        .map(|(_, r)| r.inc >> 16)
}

#[test]
fn a_confirming_snapshot_takes_the_homes_record_over_a_stale_copy() {
    let (mut w, b, c, r) = moved_home();
    let (m, x) = (3, 5);
    let e = r.inc >> 16;
    let up = Record {
        inc: (e + 1) << 16,
        ..r
    };
    let one = |rec: Record| entry_bytes(&id(x), &rec, Alive::Alive);
    // c, not the home, holds a later life of x; the view follows it while no home is confirmed.
    w.inject(m, c, &Frame::Snap(Snap::new(false, false, &one(up)).unwrap()));
    assert_eq!(x_epoch(&w, m, x), Some(e + 1));
    let joined = |w: &World| w.count_events(m, |ev| matches!(ev, Event::MemberJoined { member } if *member == id(x)));
    let before = joined(&w);
    // b, the home, lists x at the earlier life, in one frame: its word is the view's from then on.
    w.inject(m, b, &Frame::Snap(Snap::new(false, false, &one(r)).unwrap()));
    assert_eq!(x_epoch(&w, m, x), Some(e), "the home's record, not a stale copy's");
    assert_eq!(joined(&w), before + 1, "the record moved to another epoch");
}

#[test]
fn a_confirming_snapshot_of_two_frames_takes_the_homes_record_over_a_stale_copy() {
    let (mut w, b, c, r) = moved_home();
    let (m, x, y) = (3, 5, 4);
    let e = r.inc >> 16;
    let up = Record {
        inc: (e + 1) << 16,
        ..r
    };
    w.inject(
        m,
        c,
        &Frame::Snap(Snap::new(false, false, &entry_bytes(&id(x), &up, Alive::Alive)).unwrap()),
    );
    assert_eq!(x_epoch(&w, m, x), Some(e + 1));
    let ry = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(y)).unwrap().1;
    w.inject(
        m,
        b,
        &Frame::Snap(Snap::new(false, true, &entry_bytes(&id(x), &r, Alive::Alive)).unwrap()),
    );
    w.inject(
        m,
        b,
        &Frame::Snap(Snap::new(false, false, &entry_bytes(&id(y), &ry, Alive::Alive)).unwrap()),
    );
    assert_eq!(x_epoch(&w, m, x), Some(e), "the home's record, not a stale copy's");
}

/// The only hub's snapshot is cut after its first frame, which lists x; `end` is what the member sees of the cut. The
/// hub let x go meanwhile and sends no delta; its next snapshot lists only y. The one a new session's HELLO asks for
/// is dropped, so that nothing but this one reaches the member. x must be aged by it and gone a lease later.
fn a_cut_snapshot_leaves_no_ghost(end: impl FnOnce(&mut World)) {
    let mut w = started(1, 3);
    let (m, x, y) = (1, 2, 3);
    let rx = *w.nodes[m].m.members().find(|(k, _)| **k == id(x)).unwrap().1;
    let ry = *w.nodes[m].m.members().find(|(k, _)| **k == id(y)).unwrap().1;
    w.inject(
        m,
        0,
        &Frame::Snap(Snap::new(false, true, &entry_bytes(&id(x), &rx, Alive::Alive)).unwrap()),
    );
    end(&mut w);
    w.drop_once.push((0, m, ty::SNAP));
    w.inject(
        m,
        0,
        &Frame::Snap(Snap::new(false, false, &entry_bytes(&id(y), &ry, Alive::Alive)).unwrap()),
    );
    let absent_x = |w: &World| traces(w, m, |t| matches!(t, Trace::Absent { member } if *member == id(x)));
    assert_eq!(
        absent_x(&w),
        1,
        "a completed snapshot ages what it did not list, whatever an earlier one listed"
    );
    assert!(w.has(m, x), "kept for the lease");
    assert!(
        w.run_until(LEASE + SLOW_TICK + SEC, |w| !w.has(m, x)),
        "a ghost: x is still in the view"
    );
    assert_eq!(
        traces(
            &w,
            m,
            |t| matches!(t, Trace::Removed { member, why: Removal::LeaseExpired } if *member == id(x))
        ),
        1
    );
}

#[test]
fn a_snapshot_cut_short_does_not_leave_a_ghost() {
    a_cut_snapshot_leaves_no_ghost(|w| {
        w.with(1, |n, h, now| n.session_down(h, now, &id(0), 0));
        w.with(1, |n, h, now| n.session_up(h, now, &id(0), false));
    });
}

#[test]
fn a_session_that_replaces_another_closes_a_cut_snapshot() {
    a_cut_snapshot_leaves_no_ghost(|w| w.with(1, |n, h, now| n.session_up(h, now, &id(0), false)));
}

#[test]
fn a_reset_stream_closes_a_cut_snapshot() {
    a_cut_snapshot_leaves_no_ghost(|w| w.with(1, |n, _, _| n.stream_reset(&id(0))));
}

#[test]
fn a_view_follows_its_copies_down_to_an_older_epoch() {
    let mut w = started(2, 0);
    let x = id(30);
    let seen = |w: &World| w.nodes[0].m.members().find(|(m, _)| **m == x).map(|(_, r)| *r);
    delta(&mut w, 0, 1, &x, rec(8, 0, 1), Alive::Alive);
    delta(&mut w, 0, 1, &x, rec(6, 0, 1), Alive::Alive);
    assert_eq!(seen(&w).unwrap().inc, 6 << 16);
    assert_eq!(
        w.count_events(0, |e| matches!(e, Event::MemberJoined { member } if *member == x)),
        2
    );
}

#[test]
fn an_older_epoch_from_one_hub_does_not_beat_a_newer_one_from_another() {
    let mut w = started(3, 0);
    let x = id(30);
    delta(&mut w, 0, 1, &x, rec(8, 0, 1), Alive::Alive);
    delta(&mut w, 0, 2, &x, rec(6, 0, 1), Alive::Alive);
    assert_eq!(
        w.nodes[0].m.members().find(|(m, _)| **m == x).map(|(_, r)| r.inc),
        Some(8 << 16)
    );
}

#[test]
fn a_late_timer_opens_a_quiet_window_and_removals_wait_10_s_plus_5_s() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    w.jump(20 * SEC);
    w.with(m, |n, h, now| n.on_timeout(h, now));
    assert_eq!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::LateTimer
            }
        )),
        1
    );
    let woke = w.now;
    // The wake renewed every hub at once with a snapshot request.
    assert!(hello_flags(&w, m, 0, woke).iter().all(|f| f & 1 == 1) && !hello_flags(&w, m, 0, woke).is_empty());
    // The member really is gone from the home hub; its down delta reaches us inside the window.
    w.with(hub, |n, h, now| n.revoke(h, now, &id(x))).unwrap();
    w.run(100 * MS);
    assert!(w.has(m, x), "the removal is queued, not believed");
    assert!(traces(&w, m, |t| matches!(t, Trace::Deferred { .. })) >= 1);
    w.run(9 * SEC);
    assert!(w.has(m, x));
    assert!(w.run_until(10 * SEC, |w| !w.has(m, x)));
    let took = w
        .first_event_time(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
        .unwrap()
        - woke;
    assert!(
        took >= 14 * SEC && took <= 16 * SEC,
        "reported {} ms after the wake",
        took / MS
    );
}

fn quiet_late_timer(w: &World, m: usize) -> usize {
    traces(w, m, |t| {
        matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::LateTimer
            }
        )
    })
}

#[test]
fn a_late_first_tick_opens_a_quiet_window() {
    let mut w = World::new(2, 3, START);
    w.attach_all();
    let m = 2;
    // The host sleeps from the start: the first tick, due at the start, runs just over WAKE_GAP late.
    w.jump(WAKE_GAP);
    w.run(50 * MS);
    assert_eq!(quiet_late_timer(&w, m), 1, "the first tick is due at the start");
    for hub in 0..2 {
        let f = hello_flags(&w, m, hub, START);
        assert!(
            f.len() >= 2 && f.iter().all(|f| f & 1 == 1),
            "the session's HELLO and the wake's, both asking for a snapshot, to hub {hub}: {f:?}"
        );
    }
}

#[test]
fn a_first_tick_on_time_opens_no_window() {
    let mut w = World::new(2, 3, START);
    w.attach_all();
    let m = 2;
    w.jump(WAKE_GAP - 50 * MS);
    w.run(50 * MS);
    assert_eq!(quiet_late_timer(&w, m), 0, "exactly WAKE_GAP late is not a suspension");
}

#[test]
fn a_complete_snapshot_does_not_lease_a_deferred_removal_again() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    // The hubs have run longer than a lease, so their snapshots are complete.
    w.run(LEASE + 5 * SEC);
    assert!(w.has(m, x));
    w.jump(20 * SEC);
    w.with(m, |n, h, now| n.on_timeout(h, now));
    let woke = w.now;
    // x is gone from the hub after the wake request left: the DOWN is read inside the window, and the snapshot the
    // wake asked for omits x.
    w.with(hub, |n, h, now| n.revoke(h, now, &id(x))).unwrap();
    w.run(100 * MS);
    assert!(w.has(m, x), "the removal is queued, not believed");
    assert!(
        w.run_until(QUIET + RECHECK_GAP + NODE_TICK + 200 * MS, |w| !w.has(m, x)),
        "removed at the end of its window, not a lease after the snapshot ({} ms after the wake)",
        (w.now - woke) / MS
    );
}

#[test]
fn an_expiry_found_at_a_late_tick_is_not_leased_again() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    // x is gone from the hub, and the member is not told; a snapshot of the hub that omits it starts the clock.
    w.drop_once.push((hub, m, ty::DELTA));
    w.with(hub, |n, h, now| n.revoke(h, now, &id(x))).unwrap();
    w.run(SEC);
    assert!(w.has(m, x));
    let raw = raw_without(&w, m, x);
    w.inject(m, hub, &Frame::Snap(Snap::new(true, false, &raw).unwrap()));
    assert_eq!(absent_traces(&w, m), 1);
    // The clock runs out while the host is suspended: the wake tick finds the expiry inside its own window.
    w.run(LEASE - 3 * SEC);
    assert!(w.has(m, x), "still inside the lease");
    w.jump(5 * SEC);
    w.with(m, |n, h, now| n.on_timeout(h, now));
    let woke = w.now;
    assert!(
        w.run_until(QUIET + RECHECK_GAP + SEC, |w| !w.has(m, x)),
        "the forced snapshot of the wake leased it again ({} ms after the wake)",
        (w.now - woke) / MS
    );
}

#[test]
fn a_member_that_is_back_when_the_window_ends_is_never_reported() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    w.jump(20 * SEC);
    w.with(m, |n, h, now| n.on_timeout(h, now));
    let r = *w.nodes[m].m.members().find(|(mem, _)| **mem == id(x)).unwrap().1;
    delta(&mut w, m, hub, &id(x), r, Alive::Down);
    w.run(4 * SEC);
    delta(&mut w, m, hub, &id(x), r, Alive::Alive);
    w.run(30 * SEC);
    assert!(w.has(m, x));
    assert_eq!(w.count_events(m, |e| matches!(e, Event::MemberConfirmedDown { .. })), 0);
}

#[test]
fn a_heal_opens_a_quiet_window_too() {
    let mut w = World::new(2, 2, START);
    w.keepalive = 5 * SEC;
    w.attach_all();
    w.run(5 * SEC);
    let m = 2;
    let other = 1 - usize::from(w.nodes[m].m.primary().unwrap()[0] - 1);
    w.cut.insert((other, m));
    w.run(64 * SEC);
    assert_eq!(traces(&w, m, |t| matches!(t, Trace::Quiet { .. })), 0);
    w.cut.remove(&(other, m));
    w.run(10 * SEC);
    assert_eq!(
        traces(&w, m, |t| matches!(
            t,
            Trace::Quiet {
                cause: QuietCause::Heal
            }
        )),
        1,
        "{:?}",
        w.traces[m]
    );
    assert_eq!(w.members_of(m).len(), 3);
}

/// Member 3 of a three-hub world is homed on hub 3 and has hubs 1 and 2 cut for a minute, then hears hub 1 again (a
/// heal); hub 3 reports member 4 down just after, and hub 2 is heard again `gap` later (a second heal). Returns
/// the world, the instant of the first heal and the instant member 4 left the view.
fn two_heals(gap: u64) -> (World, u64, u64) {
    let mut w = World::new(3, 3, START);
    w.keepalive = 5 * SEC;
    let (m, x) = (3, 4);
    w.set_rtt(m, 0, 100 * MS);
    w.set_rtt(m, 1, 100 * MS);
    w.set_rtt(m, 2, 20 * MS);
    w.attach_all();
    w.run(5 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(2)));
    w.cut.insert((0, m));
    w.cut.insert((1, m));
    w.run(64 * SEC);
    w.cut.remove(&(0, m));
    assert!(w.run_until(20 * SEC, |w| traces(w, m, |t| matches!(t, Trace::Quiet { .. })) == 1));
    let healed = w.now;
    w.with(2, |n, h, now| n.revoke(h, now, &id(x))).unwrap();
    w.run(gap);
    w.cut.remove(&(1, m));
    assert!(w.run_until(30 * SEC, |w| traces(w, m, |t| matches!(t, Trace::Quiet { .. })) == 2));
    assert!(traces(&w, m, |t| matches!(t, Trace::Deferred { .. })) >= 1);
    assert!(w.has(m, x), "the removal is queued while the windows are open");
    assert!(w.run_until(60 * SEC, |w| !w.has(m, x)));
    let left = w
        .first_event_time(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
        .unwrap();
    (w, healed, left)
}

#[test]
fn a_heal_does_not_defer_a_removal_an_earlier_window_deferred() {
    let (_, healed, left) = two_heals(3 * SEC);
    assert!(
        left - healed <= 16 * SEC,
        "the removal left {} ms after the first heal, not at the end of that window plus the extra look",
        (left - healed) / MS
    );
}

#[test]
fn a_removal_found_after_a_heal_waits_for_that_heals_window() {
    let mut w = World::new(2, 3, START);
    w.keepalive = 5 * SEC;
    w.attach_all();
    w.run(5 * SEC);
    let (m, x) = (2, 3);
    let home = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    let other = 1 - home;
    let r = *w.nodes[m].m.members().find(|(k, _)| **k == id(x)).unwrap().1;
    w.cut.insert((other, m));
    w.run(64 * SEC);
    w.cut.remove(&(other, m));
    assert!(w.run_until(20 * SEC, |w| traces(w, m, |t| matches!(t, Trace::Quiet { .. })) == 1));
    let healed = w.now;
    delta(&mut w, m, home, &id(x), r, Alive::Down);
    assert!(w.has(m, x));
    assert!(traces(&w, m, |t| matches!(t, Trace::Deferred { .. })) >= 1);
    assert!(w.run_until(60 * SEC, |w| !w.has(m, x)));
    let left = w
        .first_event_time(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
        .unwrap();
    assert!(
        left - healed >= 14 * SEC,
        "left {} ms after the heal",
        (left - healed) / MS
    );
}

#[test]
fn a_late_timer_defers_a_waiting_removal_again() {
    let mut w = started(2, 3);
    let (m, x) = (2, 3);
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    w.jump(20 * SEC);
    w.with(m, |n, h, now| n.on_timeout(h, now));
    w.with(hub, |n, h, now| n.revoke(h, now, &id(x))).unwrap();
    w.run(8 * SEC);
    assert!(w.has(m, x));
    w.jump(20 * SEC);
    w.with(m, |n, h, now| n.on_timeout(h, now));
    let second = w.now;
    w.run(9 * SEC);
    assert!(
        w.has(m, x),
        "the second late timer reopened the window for the waiting removal"
    );
    assert!(w.run_until(20 * SEC, |w| !w.has(m, x)));
    let left = w
        .first_event_time(m, |e| matches!(e, Event::MemberConfirmedDown { .. }))
        .unwrap();
    assert!(
        left - second >= 14 * SEC,
        "left {} ms after the second late timer",
        (left - second) / MS
    );
}

#[test]
fn a_redial_asks_for_a_snapshot() {
    let mut w = started(2, 2);
    let m = 2;
    let hub = usize::from(w.nodes[m].m.primary().unwrap()[0]) - 1;
    w.run(20 * SEC);
    let t = w.now;
    w.close_session(m, hub, 0);
    w.run(SEC);
    w.connect(m, hub);
    w.run(2 * SEC);
    let flags = hello_flags(&w, m, hub, t);
    assert!(!flags.is_empty());
    assert_eq!(
        flags[0] & 1,
        1,
        "the first HELLO on the new session asks for a snapshot"
    );
    assert!(
        w.nodes[m].h.bc.iter().filter(|b| matches!(b, Bc::Resub(_))).count() >= 2,
        "and the subscriptions are restored"
    );
}

#[test]
fn the_primary_is_the_nearest_hub_with_a_hysteresis_of_20_ms_and_a_quarter() {
    let mut w = World::new(3, 1, START);
    let m = 3;
    for (hub, ms) in [(0, 200), (1, 150), (2, 400)] {
        w.set_rtt(m, hub, ms * MS);
    }
    w.attach_all();
    w.run(20 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(1)), "the nearest hub");
    // Hub 0 gets better, but not by 20 ms and a quarter: no switch.
    w.set_rtt(m, 0, 120 * MS);
    w.run(20 * SEC);
    assert_eq!(
        w.nodes[m].m.primary(),
        Some(&id(1)),
        "120 + 20 is not under three quarters of 150"
    );
    // Hub 0 gets clearly better (the periodic check wants two thirds, the switch itself three quarters).
    w.set_rtt(m, 0, 70 * MS);
    w.run(20 * SEC);
    assert_eq!(w.nodes[m].m.primary(), Some(&id(0)));
    assert!(w.nodes[m].h.bc.contains(&Bc::Primary(Some(id(1)), id(0))));
    // Hub 1 comes within the margin: no flapping back.
    w.set_rtt(m, 1, 60 * MS);
    w.run(40 * SEC);
    assert_eq!(
        w.nodes[m].m.primary(),
        Some(&id(0)),
        "60 + 20 is not under three quarters of 70"
    );
    // A new primary asks for its snapshot and tells the old one.
    assert!(
        hello_flags(&w, m, 0, 0).iter().any(|f| f & 3 == 3),
        "snapshot request homed at the new primary"
    );
}

#[test]
fn a_periodic_hello_is_skipped_only_while_the_transport_proves_the_session_alive() {
    let mut w = World::new(2, 1, START);
    w.keepalive = 0;
    w.attach_all();
    w.run(5 * SEC);
    let m = 2;
    let other = 1 - usize::from(w.nodes[m].m.primary().unwrap()[0] - 1);
    let home = 1 - other;
    // At the 25 s renewal: a pending timeout on one hub forces its HELLO; the other is suppressed.
    w.nodes[m].h.ev.get_mut(&id(other)).unwrap().pto = 1;
    let t = w.now;
    w.run(22 * SEC);
    let sent = |hub| hello_flags(&w, m, hub, t + 15 * SEC).len();
    assert_eq!(sent(other), 1, "pto != 0: not suppressed");
    assert_eq!(sent(home), 0, "pto == 0 and received within 67 s: suppressed");
    // Past 67 s of silence it is sent on both.
    w.run(60 * SEC);
    assert!(hello_flags(&w, m, home, t + 40 * SEC).len() >= 1);
}

#[test]
fn a_move_changes_the_address_tag_once_and_settles_before_the_new_address_is_known() {
    let mut w = started(2, 2);
    let (m, peer) = (2, 3);
    let before = w.nodes[peer]
        .m
        .members()
        .find(|(mem, _)| **mem == id(m))
        .unwrap()
        .1
        .thash;
    // A handover with the same ticket: the move counter alone changes the tag.
    w.with(m, |n, _, now| n.address_changed(now));
    w.run(3 * SEC);
    let after = w.nodes[peer]
        .m
        .members()
        .find(|(mem, _)| **mem == id(m))
        .unwrap()
        .1
        .thash;
    assert_ne!(before, after);
    assert_eq!(
        w.count_events(
            peer,
            |e| matches!(e, Event::AddressChanged { member } if *member == id(m))
        ),
        1
    );
    // A handover where the reflexive address is learned a second later: still one change.
    w.nodes[m].h.reflexive = false;
    w.with(m, |n, _, now| n.address_changed(now));
    w.run(SEC);
    w.nodes[m].h.ticket = 77;
    w.nodes[m].h.reflexive = true;
    w.run(6 * SEC);
    assert_eq!(
        w.count_events(
            peer,
            |e| matches!(e, Event::AddressChanged { member } if *member == id(m))
        ),
        2,
        "one more for the second move, not two"
    );
    let last = w.nodes[peer]
        .m
        .members()
        .find(|(mem, _)| **mem == id(m))
        .unwrap()
        .1
        .thash;
    assert_eq!((last[0], last[1]), (77, 2), "the new ticket with two moves counted");
}

#[test]
fn a_changed_stack_version_is_announced_and_reported() {
    let mut w = started(2, 2);
    w.nodes[2].h.version = 4;
    w.run(3 * SEC);
    assert_eq!(
        w.count_events(
            3,
            |e| matches!(e, Event::StackChanged { member, version: 4 } if *member == id(2))
        ),
        1
    );
    assert_eq!(w.nodes[3].m.members().find(|(m, _)| **m == id(2)).unwrap().1.ver, 4);
    // The record sequence moved on, the epoch did not.
    assert_eq!(w.nodes[2].m.incarnation() & 0xffff, 1);
}

#[test]
fn a_restart_with_a_newer_incarnation_rejoins() {
    let mut w = started(2, 2);
    let r = *w.nodes[3].m.members().find(|(m, _)| **m == id(2)).unwrap().1;
    let hub = usize::from(w.nodes[3].m.primary().unwrap()[0]) - 1;
    let newer = Record {
        inc: ((r.inc >> 16) + 1) << 16,
        ver: r.ver,
        thash: r.thash,
    };
    delta(&mut w, 3, hub, &id(2), newer, Alive::Alive);
    assert_eq!(
        w.count_events(3, |e| matches!(e, Event::MemberJoined { member } if *member == id(2))),
        2
    );
}

#[test]
fn a_member_with_no_hub_starts_alone_and_sends_nothing() {
    // An endpoint that names no relay is a member with no hub to attach to: it runs, and it says nothing to anyone.
    let mut w = World::new(0, 1, START);
    w.run(120 * SEC);
    assert!(w.frames.is_empty(), "{} frames", w.frames.len());
    assert!(w.nodes[0].m.poll_event().is_none());
}
