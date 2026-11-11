//! The hub roster: leases and renewals, PULSE, attachment (FLOOR plus SNAP, else ACK), carrier-drop confirmation
//! with its independent-path rule, DOWN between hubs, carrier return, graceful leave and revocation.
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

use vinc_membership::codec::{Alive, Entry, Frame, Hello, Record, ty};
use vinc_membership::session::DENIED_CODE;
use vinc_membership::{Carrier, CloseReason, Event, Route, Trace};
use world::{Bc, LEAVE, MS, SEC, World, id};

vinc_tests::install_counting_allocator!();

const START: u64 = 100 * SEC;

fn started(hubs: usize, members: usize) -> World {
    let mut w = World::new(hubs, members, START);
    w.attach_all();
    w.run(3 * SEC);
    w
}

fn hubs_n(w: &World) -> usize {
    w.hubs
}

fn count_ty(w: &World, from: usize, to: usize, t: u8) -> usize {
    w.sent_types
        .iter()
        .filter(|s| s.1 == from && s.2 == to && s.3 == t)
        .count()
}

fn types(w: &World, from: usize, to: usize) -> Vec<u8> {
    w.sent_types
        .iter()
        .filter(|s| s.1 == from && s.2 == to)
        .map(|s| s.3)
        .collect()
}

fn traces(w: &World, i: usize, f: impl Fn(&Trace) -> bool) -> usize {
    w.traces[i].iter().filter(|t| f(t)).count()
}

#[test]
fn a_new_attachment_gets_floor_then_snapshot_and_a_plain_renewal_gets_an_ack() {
    let mut w = World::new(1, 2, START);
    w.keepalive = 0;
    w.attach_all();
    w.run(3 * SEC);
    let t = types(&w, 0, 1);
    assert_eq!(&t[..2], &[ty::FLOOR, ty::SNAP], "FLOOR then SNAP first: {t:?}");
    assert_eq!(count_ty(&w, 0, 1, ty::FLOOR), 1, "one FLOOR per attachment");
    let snaps = count_ty(&w, 0, 1, ty::SNAP);
    assert!(
        w.nodes[1].m.members().any(|(m, _)| *m == id(2)),
        "the snapshot carried the other member"
    );
    // FLOOR is opaque: the broadcast layer wrote it, membership did not look inside.
    assert!(!w.nodes[0].h.bc.iter().any(|b| matches!(b, Bc::Frame(..))));
    // The renewal at 25 s and 50 s ride the transport (PULSE); at 75 s the session has been silent 67 s.
    w.run(80 * SEC);
    assert_eq!(traces(&w, 1, |t| matches!(t, Trace::HelloSuppressed { .. })), 2);
    let t = types(&w, 0, 1);
    assert_eq!(count_ty(&w, 0, 1, ty::ACK), 1, "the hub acks the plain renewal: {t:?}");
    assert_eq!(count_ty(&w, 0, 1, ty::SNAP), snaps, "and sends no further snapshot");
    assert_eq!(w.nodes[0].m.roster_len(), 2);
}

#[test]
fn pulse_keeps_the_lease_alive_without_any_hello() {
    let mut w = started(1, 1);
    w.run(400 * SEC);
    assert_eq!(
        w.nodes[0].m.roster_len(),
        1,
        "the lease outlived five leases on transport evidence alone"
    );
    assert!(traces(&w, 0, |t| matches!(t, Trace::Pulse { .. })) >= 10);
    let renewed = w.nodes[0].m.lease_of(&id(1)).unwrap();
    assert!(w.now - renewed < 60 * SEC, "the lease was refreshed lately");
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::LeaseExpired { .. })), 0);
}

#[test]
fn pulse_refreshes_only_a_lease_that_is_25_s_stale() {
    let mut w = World::new(1, 1, START);
    w.keepalive = 0;
    w.attach_all();
    w.run(2 * SEC);
    let first = w.nodes[0].m.lease_of(&id(1)).unwrap();
    w.run(8 * SEC);
    let seen = w.now;
    w.nodes[0].h.ev.get_mut(&id(1)).unwrap().last_rx = seen;
    w.run(10 * SEC);
    assert_eq!(
        w.nodes[0].m.lease_of(&id(1)),
        Some(first),
        "evidence 10 s old and a 20 s old lease: not refreshed yet"
    );
    w.run(10 * SEC);
    assert_eq!(
        w.nodes[0].m.lease_of(&id(1)),
        Some(seen),
        "once the lease is 25 s stale it takes the evidence"
    );
}

#[test]
fn the_lease_ends_80_s_after_the_last_renewal() {
    let mut w = started(1, 1);
    w.run(60 * SEC);
    let renewed = w.nodes[0].m.lease_of(&id(1)).unwrap();
    w.crash(1);
    assert!(w.run_until(120 * SEC, |w| w.nodes[0].m.roster_len() == 0));
    let gone = w.now - renewed;
    assert!(
        gone > 80 * SEC && gone < 82 * SEC,
        "expired {} ms after the last renewal",
        gone / MS
    );
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::LeaseExpired { .. })), 1);
    assert!(w.nodes[0].h.bc.contains(&Bc::Release(id(1))));
}

fn crash_with_carrier_drop(hubs: usize, direct: bool) -> (World, u64) {
    let mut w = started(hubs, 1);
    if direct {
        w.direct.insert((0, hubs));
    }
    w.run(40 * SEC);
    w.crash(hubs);
    let t = w.now;
    w.set_carrier_gone(0, hubs);
    (w, t)
}

#[test]
fn a_dropped_carrier_is_confirmed_at_the_drop_plus_one_second_on_two_paths() {
    let (mut w, t) = crash_with_carrier_drop(2, true);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.lease_of(&id(hubs_n(w))).is_none()));
    let took = w.now - t;
    assert!(
        took >= SEC && took < SEC + 150 * MS,
        "confirmed {} ms after the drop",
        took / MS
    );
    let probes: Vec<_> = w
        .sent_types
        .iter()
        .filter(|s| s.1 == 0 && s.2 == 2 && s.3 == ty::PROBE)
        .collect();
    assert_eq!(probes.len(), 2, "one probe on the session, one on the independent path");
    assert!(probes.iter().any(|p| p.4 == Route::Reply) && probes.iter().any(|p| p.4 == Route::Direct));
    assert_eq!(w.count_events(0, |e| matches!(e, Event::MemberSuspected { .. })), 1);
    assert!(
        w.nodes[0].h.bc.contains(&Bc::Hold(id(2))),
        "the subscriptions are held, not dropped"
    );
    assert!(!w.nodes[0].h.bc.contains(&Bc::Release(id(2))));
    // DOWN went to the other hub with proof of two paths.
    assert!(w.sent_types.iter().any(|s| s.1 == 0 && s.2 == 1 && s.3 == ty::DOWN));
}

#[test]
fn without_a_direct_path_the_second_probe_goes_through_another_hub() {
    let (mut w, t) = crash_with_carrier_drop(2, false);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.lease_of(&id(hubs_n(w))).is_none()));
    assert!(w.now - t >= SEC);
    let probes: Vec<_> = w
        .sent_types
        .iter()
        .filter(|s| s.1 == 0 && s.2 == 2 && s.3 == ty::PROBE)
        .collect();
    assert_eq!(probes.len(), 2);
    assert!(probes.iter().any(|p| p.4 == Route::Via(id(1))), "{probes:?}");
}

#[test]
fn a_lone_hub_cannot_confirm_early_and_waits_for_the_lease() {
    let (mut w, t) = crash_with_carrier_drop(1, false);
    w.run(60 * SEC);
    assert_eq!(
        w.nodes[0].m.roster_len(),
        1,
        "no independent path: no early confirmation"
    );
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::NoIndependentPath { .. })), 1);
    assert!(w.run_until(60 * SEC, |w| w.nodes[0].m.roster_len() == 0));
    assert!(w.now - t > 60 * SEC, "the lease ended it");
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
}

#[test]
fn a_member_that_answers_on_either_path_is_never_confirmed() {
    // The carrier closed and the session path is dead, but the member is alive and its direct path works.
    let mut w = started(2, 1);
    w.direct.insert((0, 2));
    w.run(40 * SEC);
    w.set_carrier_gone(0, 2);
    w.run(10 * SEC);
    assert_eq!(w.nodes[0].m.roster_len(), 2, "member kept (and hub 1)");
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
}

#[test]
fn a_member_that_answers_the_probe_after_its_carrier_closed_is_never_reported_suspected() {
    let mut w = started(2, 1);
    w.run(40 * SEC);
    w.nodes[0].h.carriers.insert(
        id(2),
        Carrier::Gone {
            since: w.now,
            sleep: None,
        },
    );
    w.with(0, |m, h, now| m.carrier_gone(h, now, &id(2)));
    w.run(10 * SEC);
    assert_eq!(w.nodes[0].m.roster_len(), 2, "the member is kept");
    assert_eq!(
        w.count_events(0, |e| matches!(e, Event::MemberSuspected { .. })),
        0,
        "a member that is there is not suspected for a closed carrier"
    );
}

#[test]
fn a_single_lost_probe_does_not_confirm() {
    let mut w = started(2, 1);
    w.run(40 * SEC);
    // The session path stays alive (a carrier close the member survives); only the first probe is lost.
    w.drop_once.push((0, 2, ty::PROBE));
    w.nodes[0].h.carriers.insert(
        id(2),
        Carrier::Gone {
            since: w.now,
            sleep: None,
        },
    );
    w.with(0, |m, h, now| m.carrier_gone(h, now, &id(2)));
    w.run(10 * SEC);
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })),
        0,
        "the other probe was answered"
    );
    assert_eq!(w.nodes[0].m.roster_len(), 2);
}

#[test]
fn a_slow_member_is_not_confirmed_because_its_transport_still_answers() {
    let mut w = started(2, 1);
    w.direct.insert((0, 2));
    w.nodes[2].cpu = 5 * SEC; // twelve times too slow to answer a probe in time
    w.run(40 * SEC);
    w.set_carrier_gone(0, 2);
    w.run(8 * SEC);
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 0);
    assert_eq!(w.nodes[0].m.roster_len(), 2);
}

#[test]
fn two_probes_both_lost_do_confirm_a_member_that_is_truly_unreachable() {
    let mut w = started(2, 1);
    w.run(40 * SEC);
    w.cut.insert((1, 2)); // the relay path is dead too
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.roster_len() == 1));
    assert_eq!(traces(&w, 0, |t| matches!(t, Trace::Confirmed { .. })), 1);
}

#[test]
fn another_hubs_down_is_refused_while_our_own_lease_is_fresh() {
    let (mut w, _t) = crash_with_carrier_drop(2, true);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.lease_of(&id(hubs_n(w))).is_none()));
    w.run(2 * SEC);
    // Hub 1 holds a lease renewed at the crash (a keepalive within the last 40 s): fresh, so the DOWN is refused.
    assert_eq!(w.nodes[1].m.roster_len(), 2, "hub 1 kept the member");
    let refused = traces(&w, 1, |t| {
        matches!(
            t,
            Trace::DownRefused {
                why: vinc_membership::event::Refusal::LeaseFresh,
                ..
            }
        )
    });
    assert_eq!(refused, 1, "{:?}", w.traces[1]);
    assert!(!w.nodes[1].h.bc.contains(&Bc::Hold(id(2))));
    assert!(w.has(1, 2), "hub 1's view still lists the member");
}

#[test]
fn another_hubs_down_is_accepted_once_our_lease_is_stale() {
    let mut w = started(2, 1);
    w.run(10 * SEC);
    w.crash(2);
    w.run(40 * SEC); // both hubs have heard nothing for 40 s
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[1].m.roster_len() == 1));
    assert_eq!(traces(&w, 1, |t| matches!(t, Trace::DownAccepted { .. })), 1);
    assert!(w.nodes[1].h.bc.contains(&Bc::Hold(id(2))));
    assert!(!w.has(1, 2), "both hubs let go, so hub 1's view lost the member");
}

#[test]
fn a_down_needs_a_proof_of_two_paths_and_no_open_carrier() {
    let mut w = started(2, 1);
    w.run(10 * SEC);
    w.crash(2);
    w.run(40 * SEC);
    let m = id(2);
    let one = vinc_membership::codec::Proof::new(
        5000,
        &[vinc_membership::codec::Probe {
            age_ms: 1000,
            path: vinc_membership::codec::Path::Session,
        }],
    )
    .unwrap();
    let inc = w.nodes[2].m.incarnation();
    let down = |proof| Frame::Down(vinc_membership::codec::Down { member: &m, inc, proof });
    let f = down(one);
    w.inject(1, 0, &f);
    assert_eq!(w.nodes[1].m.roster_len(), 2, "a proof of one path is not enough");
    let two = vinc_membership::codec::Proof::new(
        5000,
        &[
            vinc_membership::codec::Probe {
                age_ms: 1000,
                path: vinc_membership::codec::Path::Session,
            },
            vinc_membership::codec::Probe {
                age_ms: 900,
                path: vinc_membership::codec::Path::Relay,
            },
        ],
    )
    .unwrap();
    w.nodes[1].h.carriers.insert(m, Carrier::Open);
    let f = down(two);
    w.inject(1, 0, &f);
    assert_eq!(w.nodes[1].m.roster_len(), 2, "an open carrier to this hub refuses it");
    w.nodes[1].h.carriers.insert(m, Carrier::Unknown);
    let liar = vinc_membership::codec::Proof::new(
        10,
        &[
            vinc_membership::codec::Probe {
                age_ms: 1000,
                path: vinc_membership::codec::Path::Session,
            },
            vinc_membership::codec::Probe {
                age_ms: 900,
                path: vinc_membership::codec::Path::Relay,
            },
        ],
    )
    .unwrap();
    w.inject(1, 0, &down(liar));
    assert_eq!(
        w.nodes[1].m.roster_len(),
        2,
        "a proof that claims less silence than its probes span"
    );
    w.inject(1, 0, &down(two));
    assert_eq!(
        w.nodes[1].m.roster_len(),
        1,
        "two paths, no carrier, a stale lease: accepted"
    );
    // A DOWN from a member (not a hub) is ignored.
    let mut w2 = started(1, 2);
    w2.run(40 * SEC);
    let m2 = id(2);
    w2.inject(
        0,
        1,
        &Frame::Down(vinc_membership::codec::Down {
            member: &m2,
            inc: w2.nodes[2].m.incarnation(),
            proof: two,
        }),
    );
    assert_eq!(w2.nodes[0].m.roster_len(), 2);
}

#[test]
fn a_returning_carrier_restores_the_entry_the_subscriptions_and_tells_the_member() {
    let mut w = started(2, 1);
    w.run(30 * SEC);
    // Everything to the member dies for a moment: the carrier, the relay path. Both probes are lost.
    w.cut.insert((1, 2));
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.roster_len() == 1));
    assert!(w.nodes[0].h.bc.contains(&Bc::Hold(id(2))));
    // The path heals and the carrier opens again within the lease.
    w.cut.remove(&(1, 2));
    w.set_carrier_open(0, 2);
    assert_eq!(w.nodes[0].m.roster_len(), 2, "the entry is back");
    assert!(w.nodes[0].h.bc.contains(&Bc::Restore(id(2))), "and its subscriptions");
    w.run(2 * SEC);
    assert!(
        w.nodes[2].h.bc.contains(&Bc::Resub(id(0))),
        "the member was told about itself and subscribed again: {:?}",
        w.nodes[2].h.bc
    );
    assert!(traces(&w, 2, |t| matches!(t, Trace::SelfDelta { .. })) >= 1);
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::CarrierReturned { restored: true, .. })),
        1
    );
    // Other members of the view heard a down, then an alive delta, and still list the member.
    assert!(w.has(0, 2));
}

#[test]
fn a_carrier_return_after_the_lease_restores_nothing() {
    let mut w = started(2, 1);
    w.run(30 * SEC);
    w.cut.insert((1, 2));
    w.set_carrier_gone(0, 2);
    assert!(w.run_until(5 * SEC, |w| w.nodes[0].m.roster_len() == 1));
    w.run(85 * SEC);
    w.set_carrier_open(0, 2);
    assert!(
        w.nodes[0].h.bc.contains(&Bc::Release(id(2))),
        "the held subscriptions were released at the lease end"
    );
    assert_eq!(
        traces(&w, 0, |t| matches!(t, Trace::CarrierReturned { restored: true, .. })),
        0
    );
}

#[test]
fn a_graceful_leave_is_reported_by_every_hub_and_every_member() {
    let mut w = started(2, 3);
    w.run(10 * SEC);
    assert!(w.has(3, 2) && w.has(4, 2));
    w.with(2, |m, h, _| m.leave(h));
    let closed = w.nodes[2].h.closed.clone();
    assert_eq!(closed.len(), 2, "one close per hub session");
    assert!(closed.iter().all(|c| c.1 == CloseReason::Leave));
    for hub in 0..2 {
        w.close_session(2, hub, LEAVE);
    }
    w.run(5 * SEC);
    for i in [3, 4] {
        assert!(!w.has(i, 2), "member {i} dropped the leaver");
        assert_eq!(
            w.count_events(i, |e| matches!(e, Event::MemberLeft { member } if *member == id(2))),
            1
        );
        assert_eq!(
            w.count_events(
                i,
                |e| matches!(e, Event::MemberConfirmedDown { member } if *member == id(2))
            ),
            0
        );
    }
    for hub in 0..2 {
        assert_eq!(
            w.nodes[hub].m.roster_len(),
            3,
            "hub {hub} released the lease (the other hub and two members remain)"
        );
        assert!(
            w.nodes[hub].h.bc.contains(&Bc::Release(id(2))),
            "a leaver's subscriptions are not held"
        );
        assert!(!w.nodes[hub].h.bc.contains(&Bc::Hold(id(2))));
        assert_eq!(w.count_events(hub, |e| matches!(e, Event::MemberLeft { .. })), 1);
    }
}

#[test]
fn revocation_removes_the_member_and_closes_every_session_at_once() {
    let mut w = started(1, 2);
    w.run(5 * SEC);
    assert!(w.has(1, 2));
    let r = w.with(0, |m, h, now| m.revoke(h, now, &id(2)));
    r.unwrap();
    assert!(w.nodes[0].h.closed.contains(&(id(2), CloseReason::Revoked)));
    assert!(w.nodes[0].h.bc.contains(&Bc::Release(id(2))));
    assert_eq!(w.nodes[0].m.roster_len(), 1);
    assert_eq!(w.count_events(0, |e| matches!(e, Event::MemberRevoked { .. })), 1);
    w.run(2 * SEC);
    assert!(!w.has(1, 2), "the other member learned from the hub's delta");
    // Frames from the revoked member are dropped unread, and its sessions are refused.
    let before = w.nodes[0].m.roster_len();
    w.inject(
        0,
        2,
        &Frame::Hello(Hello {
            rec: Record {
                inc: 5 << 16,
                ver: 1,
                thash: [0; 8],
            },
            snap: true,
            homed: false,
        }),
    );
    assert_eq!(w.nodes[0].m.roster_len(), before);
    w.with(0, |m, h, now| m.session_up(h, now, &id(2), true));
    assert_eq!(w.nodes[0].h.closed.iter().filter(|c| c.0 == id(2)).count(), 2);
    let _ = DENIED_CODE;
}

#[test]
fn a_probe_is_answered_with_a_hello() {
    let mut w = started(1, 1);
    let before = count_ty(&w, 1, 0, ty::HELLO);
    w.inject(1, 0, &Frame::Probe);
    let after = count_ty(&w, 1, 0, ty::HELLO);
    assert_eq!(after, before + 1);
}

#[test]
fn frames_of_other_types_reach_the_broadcast_layer_and_renew_the_lease() {
    let mut w = started(1, 1);
    w.run(60 * SEC);
    let before = w.nodes[0].m.lease_of(&id(1)).unwrap();
    w.inject(
        0,
        1,
        &Frame::Other(vinc_membership::codec::Other {
            ty: 9,
            topic: b"t",
            rest: b"payload",
        }),
    );
    assert_eq!(
        w.nodes[0].h.bc.last(),
        Some(&Bc::Frame(id(1), 9, b"t".to_vec(), b"payload".to_vec()))
    );
    assert!(w.nodes[0].m.lease_of(&id(1)).unwrap() > before, "any frame renews");
    // A DELTA from a non-hub is ignored.
    let m = id(5);
    let before = w.nodes[0].m.member_count();
    w.inject(
        0,
        1,
        &Frame::Delta(Entry {
            member: &m,
            rec: Record {
                inc: 9 << 16,
                ver: 1,
                thash: [1; 8],
            },
            alive: Alive::Alive,
        }),
    );
    assert_eq!(w.nodes[0].m.member_count(), before);
}

#[test]
fn a_new_session_makes_the_next_hello_a_new_attachment() {
    // The hub kept the member as attached after a silent idle close on the member's side: the redial must still be
    // answered with FLOOR and a snapshot.
    let mut w = started(1, 1);
    w.run(10 * SEC);
    let snaps = |w: &World| count_ty(w, 0, 1, ty::SNAP);
    let floors = |w: &World| count_ty(w, 0, 1, ty::FLOOR);
    let (s0, f0) = (snaps(&w), floors(&w));
    assert_eq!(f0, 1);
    // The member side forgets the session (no close reaches the hub) and dials again.
    w.sessions.remove(&(1, 0));
    w.with(1, |m, h, now| m.session_down(h, now, &id(0), 0));
    w.connect(1, 0);
    w.run(2 * SEC);
    assert_eq!(floors(&w), 2, "a redial gets FLOOR");
    assert!(snaps(&w) > s0, "and a snapshot");
}

/// A host that stores nothing and allocates nothing.
#[derive(Default)]
struct Null {
    sends: usize,
    last_rx: u64,
}

impl vinc_membership::Session for Null {
    fn send(&mut self, _: &vinc_membership::NodeId, _: Route, _: &[u8]) -> bool {
        self.sends += 1;
        true
    }
    fn evidence(&self, _: &vinc_membership::NodeId) -> Option<vinc_membership::Evidence> {
        Some(vinc_membership::Evidence {
            last_rx: self.last_rx,
            srtt: 20 * MS,
            pto: 0,
            inflight: 0,
            direct: false,
        })
    }
    fn carrier(&self, _: &vinc_membership::NodeId) -> Carrier {
        Carrier::Open
    }
    fn close(&mut self, _: &vinc_membership::NodeId, _: CloseReason) {}
}

impl vinc_membership::Broadcast for Null {
    fn floor(&mut self, _: &vinc_membership::NodeId, _: &mut [u8]) -> usize {
        0
    }
    fn frame(&mut self, _: &vinc_membership::NodeId, _: u8, _: &[u8], _: &[u8]) {}
    fn hold(&mut self, _: &vinc_membership::NodeId) {}
    fn restore(&mut self, _: &vinc_membership::NodeId) {}
    fn release(&mut self, _: &vinc_membership::NodeId) {}
    fn resubscribe(&mut self, _: &vinc_membership::NodeId) {}
    fn primary_changed(&mut self, _: Option<&vinc_membership::NodeId>, _: &vinc_membership::NodeId) {}
}

impl vinc_membership::Local for Null {
    fn version(&self) -> u16 {
        1
    }
    fn reflexive_known(&self) -> bool {
        true
    }
    fn address_hash(&self, _: u8) -> [u8; 8] {
        [1; 8]
    }
}

fn bytes(f: &Frame<'_>) -> Vec<u8> {
    let mut b = [0u8; 4096];
    f.encode(&mut b).unwrap().to_vec()
}

#[test]
fn steady_state_allocates_nothing() {
    use vinc_membership::{Config, Membership};
    let rec = |n: u8| Record {
        inc: (u64::from(n) + 1) << 16,
        ver: 1,
        thash: [n; 8],
    };
    let hello = |n: u8, snap: bool, homed: bool| {
        bytes(&Frame::Hello(Hello {
            rec: rec(n),
            snap,
            homed,
        }))
    };
    let hubs = [id(0), id(1)];

    // A hub with three attached members and a peer hub: renewals, ACKs, lease ticks, PULSE refreshes.
    let mut host = Null::default();
    let cfg = Config {
        me: id(0),
        is_hub: true,
        hubs: &hubs,
        trace: false,
    };
    let mut hub = Membership::start(&cfg, &mut host, 0, 1, 0).unwrap();
    for n in 2..5u8 {
        hub.session_up(&mut host, SEC, &id(usize::from(n)), true);
        let b = hello(n, true, true);
        hub.on_bytes(&mut host, SEC, &id(usize::from(n)), &b).unwrap();
    }
    hub.session_up(&mut host, SEC, &id(1), true);
    hub.on_bytes(&mut host, SEC, &id(1), &hello(1, true, false)).unwrap();
    let renewals: Vec<Vec<u8>> = (2..5u8).map(|n| hello(n, false, true)).collect();

    // A member with a snapshot from its hub.
    let mut mhost = Null::default();
    let mcfg = Config {
        me: id(7),
        is_hub: false,
        hubs: &hubs[..1],
        trace: false,
    };
    let mut member = Membership::start(&mcfg, &mut mhost, 0, 1, 0).unwrap();
    member.session_up(&mut mhost, SEC, &id(0), false);
    let mut entries = Vec::new();
    for n in 2..6u8 {
        entries.extend_from_slice(&vinc_membership::codec::entry_bytes(
            &id(usize::from(n)),
            &rec(n),
            Alive::Alive,
        ));
    }
    let snap = bytes(&Frame::Snap(
        vinc_membership::codec::Snap::new(false, false, &entries).unwrap(),
    ));
    member.on_bytes(&mut mhost, SEC, &id(0), &snap).unwrap();
    let ack = bytes(&Frame::Ack);
    let delta = bytes(&Frame::Delta(Entry {
        member: &id(2),
        rec: rec(2),
        alive: Alive::Alive,
    }));

    let round =
        |hub: &mut Membership, member: &mut Membership, host: &mut Null, mhost: &mut Null, from: u64, n: u64| {
            let mut events = 0;
            for k in 0..n {
                let t = from + k * 500 * MS;
                host.last_rx = t;
                mhost.last_rx = t;
                if k % 40 == 0 {
                    for (i, b) in renewals.iter().enumerate() {
                        hub.on_bytes(host, t, &id(i + 2), b).unwrap();
                    }
                    member.on_bytes(mhost, t, &id(0), &ack).unwrap();
                    member.on_bytes(mhost, t, &id(0), &delta).unwrap();
                }
                hub.on_timeout(host, t);
                member.on_timeout(mhost, t);
                events += usize::from(hub.poll_event().is_some()) + usize::from(member.poll_event().is_some());
                events += usize::from(hub.poll_trace().is_some());
                let _ = (hub.poll_timeout(), member.poll_timeout());
            }
            events
        };
    // Warm up past every table growing, then count.
    round(&mut hub, &mut member, &mut host, &mut mhost, 2 * SEC, 400);
    let mut events = 0;
    let stats = vinc_tests::measure(|| events = round(&mut hub, &mut member, &mut host, &mut mhost, 300 * SEC, 4000));
    assert_eq!(stats.count(), 0, "{stats:?}");
    assert_eq!(events, 0, "a quiet group reports nothing");
    assert!(host.sends > 0 && mhost.sends > 0, "the machines did work");
    assert_eq!(
        hub.roster_len(),
        4,
        "leases kept alive on transport evidence and renewals"
    );
}

/// A host whose carriers the test sets, that takes every send and reports a validated direct path to everyone.
#[derive(Default)]
struct Scripted {
    carriers: std::collections::BTreeMap<vinc_membership::NodeId, Carrier>,
    released: Vec<vinc_membership::NodeId>,
}

impl vinc_membership::Session for Scripted {
    fn send(&mut self, _: &vinc_membership::NodeId, _: Route, _: &[u8]) -> bool {
        true
    }
    fn evidence(&self, _: &vinc_membership::NodeId) -> Option<vinc_membership::Evidence> {
        Some(vinc_membership::Evidence {
            last_rx: 0,
            srtt: 20 * MS,
            pto: 0,
            inflight: 0,
            direct: true,
        })
    }
    fn carrier(&self, m: &vinc_membership::NodeId) -> Carrier {
        self.carriers.get(m).copied().unwrap_or_default()
    }
    fn close(&mut self, _: &vinc_membership::NodeId, _: CloseReason) {}
}

impl vinc_membership::Broadcast for Scripted {
    fn floor(&mut self, _: &vinc_membership::NodeId, _: &mut [u8]) -> usize {
        0
    }
    fn frame(&mut self, _: &vinc_membership::NodeId, _: u8, _: &[u8], _: &[u8]) {}
    fn hold(&mut self, _: &vinc_membership::NodeId) {}
    fn restore(&mut self, _: &vinc_membership::NodeId) {}
    fn release(&mut self, m: &vinc_membership::NodeId) {
        self.released.push(*m);
    }
    fn resubscribe(&mut self, _: &vinc_membership::NodeId) {}
    fn primary_changed(&mut self, _: Option<&vinc_membership::NodeId>, _: &vinc_membership::NodeId) {}
}

impl vinc_membership::Local for Scripted {
    fn version(&self) -> u16 {
        1
    }
    fn reflexive_known(&self) -> bool {
        true
    }
    fn address_hash(&self, _: u8) -> [u8; 8] {
        [1; 8]
    }
}

/// The id of the `k`-th member of a big table: 30 zero bytes and `k` as a big-endian number.
fn wide(k: u16) -> vinc_membership::NodeId {
    let mut id = [0u8; 32];
    id[30..].copy_from_slice(&k.to_be_bytes());
    id
}

#[test]
fn a_returning_carrier_never_grows_a_full_roster_past_its_bound() {
    use vinc_membership::consts::MAX_TABLE;
    use vinc_membership::{Config, Membership};
    let me = [255u8; 32];
    let mut h = Scripted::default();
    let cfg = Config {
        me,
        is_hub: true,
        hubs: &[],
        trace: false,
    };
    let mut hub = Membership::start(&cfg, &mut h, START, 1_000_000, 0).unwrap();
    let hello = |k: u16| {
        Frame::Hello(Hello {
            rec: Record {
                inc: (u64::from(k) + 2) << 16,
                ver: 1,
                thash: [0; 8],
            },
            snap: false,
            homed: false,
        })
    };
    let mut now = START;
    // Fill the roster with the members 1 to MAX_TABLE.
    let fill = u16::try_from(MAX_TABLE).unwrap();
    for k in 1..=fill {
        hub.on_frame(&mut h, now, &wide(k), &hello(k));
    }
    assert_eq!(hub.roster_len(), MAX_TABLE);
    // Member 1 drops its carrier and is confirmed down on its direct path: the roster has a free slot.
    let x = wide(1);
    now += 5 * SEC;
    h.carriers.insert(
        x,
        Carrier::Gone {
            since: now,
            sleep: None,
        },
    );
    hub.carrier_gone(&mut h, now, &x);
    now += 2 * SEC;
    hub.on_timeout(&mut h, now);
    assert_eq!(
        hub.roster_len(),
        MAX_TABLE - 1,
        "the member was confirmed down and held"
    );
    // Another member takes the free slot.
    hub.on_frame(&mut h, now, &wide(fill + 1), &hello(fill + 1));
    assert_eq!(hub.roster_len(), MAX_TABLE);
    // The carrier returns within the lease, but the roster is full: nothing is restored, the table does not grow,
    // and the held subscriptions are released.
    h.carriers.insert(x, Carrier::Open);
    h.released.clear();
    hub.carrier_return(&mut h, now, &x);
    assert_eq!(hub.roster_len(), MAX_TABLE, "a full roster refuses instead of growing");
    assert!(hub.lease_of(&x).is_none());
    assert!(
        h.released.contains(&x),
        "the subscriptions held for the member are released"
    );
}

#[test]
fn answers_and_pushes_take_the_reply_route_and_a_hello_the_session_route() {
    let mut w = started(1, 2);
    w.run(40 * SEC);
    let (mut hellos, mut answers) = (0, 0);
    for s in &w.sent_types {
        match s.3 {
            t if t == ty::HELLO => {
                hellos += 1;
                assert_eq!(s.4, Route::Session, "a hello may dial the hub");
            }
            t if t == ty::ACK || t == ty::SNAP || t == ty::DELTA || t == ty::FLOOR => {
                answers += 1;
                assert_eq!(s.4, Route::Reply, "frame type {t} from node {} never dials", s.1);
            }
            _ => {}
        }
    }
    assert!(
        hellos > 0 && answers > 0,
        "the run sent {hellos} hellos and {answers} answers"
    );
}
