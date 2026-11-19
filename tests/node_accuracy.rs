//! Accuracy over real sessions: a live member is never confirmed down by a late or lost answer, by a snapshot after a
//! heal, or by a DOWN from another hub while its own lease is fresh.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

mod node_common;

use node_common::{World, big, secs};
use pinc_membership::event::Refusal;
use pinc_node::{Body, TraceItem};
use pinc_sim::{LinkChange, LinkConfig, Loss, MS, NodeId as SimId};
use pinc_tests::NCmd;

fn lossy(delay: u64, p: f64) -> LinkConfig {
    LinkConfig {
        delay,
        loss: Loss::Bernoulli(p),
        ..LinkConfig::default()
    }
}

fn all_nodes(w: &World) -> Vec<SimId> {
    w.hubs
        .iter()
        .map(|(n, _)| *n)
        .chain(w.members.iter().copied())
        .collect()
}

fn no_one_accused(w: &World, seed: u64, what: &str) {
    for n in all_nodes(w) {
        let downs: Vec<_> = w
            .member_events(n)
            .into_iter()
            .filter(|(_, e)| {
                matches!(
                    e,
                    pinc_membership::Event::MemberConfirmedDown { .. } | pinc_membership::Event::MemberLeft { .. }
                )
            })
            .collect();
        assert!(
            downs.is_empty(),
            "seed {seed} ({what}): node {n:?} confirmed a live node down: {downs:?}"
        );
    }
}

fn complete(w: &World, seed: u64, what: &str) {
    for n in all_nodes(w) {
        assert_eq!(w.view(n), w.others(n), "seed {seed} ({what}): the view of {n:?}");
    }
}

/// The 15% loss world: every link between a member and a hub loses 15% of its datagrams both ways, every member's
/// carriers are reset once (staggered from 50 s), and member 0 answers 600 ms late between 100 s and 120 s around a
/// carrier reset at 105 s. With `loss` zero it is the same world with no loss at all.
fn accuracy_world(seed: u64, loss: f64, trace: bool) -> World {
    let mut w = World::build_with(seed, 3, 6, |w| w.trace = trace);
    let pairs: Vec<(SimId, SimId)> = w
        .members
        .iter()
        .flat_map(|m| w.hubs.iter().map(move |(h, _)| (*m, *h)))
        .collect();
    if loss > 0.0 {
        for (m, h) in &pairs {
            w.sim.link_change(0, *m, *h, LinkChange::Config(lossy(5 * MS, loss)));
            w.sim.link_change(0, *h, *m, LinkChange::Config(lossy(5 * MS, loss)));
        }
    }
    let members = w.members.clone();
    for (i, m) in members.iter().enumerate() {
        w.sim.command(secs(50 + 7 * i as u64), *m, NCmd::DropCarriers);
    }
    let slow = members[0];
    for (h, _) in &w.hubs.clone() {
        w.sim.link_change(secs(100), slow, *h, LinkChange::Delay(600 * MS));
        w.sim.link_change(secs(100), *h, slow, LinkChange::Delay(600 * MS));
        w.sim.link_change(secs(120), slow, *h, LinkChange::Delay(5 * MS));
        w.sim.link_change(secs(120), *h, slow, LinkChange::Delay(5 * MS));
    }
    w.sim.command(secs(105), slow, NCmd::DropCarriers);
    w.run(secs(260));
    w
}

#[test]
fn a_member_that_answers_late_and_drops_its_carrier_is_never_confirmed_down() {
    big(|| {
        for seed in [21u64, 22, 23, 24] {
            let w = accuracy_world(seed, 0.0, false);
            no_one_accused(&w, seed, "late answers, no loss");
            complete(&w, seed, "late answers, no loss");
        }
    });
}

/// Every confirmation a hub made, checked against the rule: the carrier of the member had been gone for the confirm
/// wait (1 s), a probe on the session and a probe on an independent path were both sent and each had its wait (250
/// ms), and nothing from the member was heard from the drop to the confirmation. Returns how many were checked.
fn check_confirmations(w: &World, seed: u64) -> usize {
    use pinc_membership::Trace as T;
    use pinc_membership::codec::Path;
    let mut checked = 0;
    for (hub, _) in &w.hubs {
        let traces = &w.sim.node(*hub).traces;
        for (t, item) in traces {
            let Body::Membership(T::Confirmed { member, .. }) = &item.body else {
                continue;
            };
            checked += 1;
            let mine = |b: &Body| match b {
                Body::Membership(T::CarrierGone { member: m }) => (m == member).then_some(0u8),
                Body::Membership(T::ProbeSent { member: m, path }) => (m == member).then_some(match path {
                    Path::Session => 1,
                    _ => 2,
                }),
                Body::Membership(T::FrameIn { peer, .. }) => (peer == member).then_some(3),
                _ => None,
            };
            let before: Vec<(u64, u8)> = traces
                .iter()
                .filter(|(u, _)| u <= t)
                .filter_map(|(u, i)| mine(&i.body).map(|k| (*u, k)))
                .collect();
            let gone = before.iter().rposition(|(_, k)| *k == 0).unwrap_or_else(|| {
                panic!("seed {seed}: hub {hub:?} confirmed a member whose carrier never dropped, at {t}")
            });
            let (g, _) = before[gone];
            let after = &before[gone + 1..];
            let probe = |kind: u8| after.iter().find(|(_, k)| *k == kind).map(|(u, _)| *u);
            let (Some(a), Some(b)) = (probe(1), probe(2)) else {
                panic!(
                    "seed {seed}: hub {hub:?} confirmed at {t} with the session probe {:?} and the independent probe {:?}",
                    probe(1),
                    probe(2)
                );
            };
            assert!(
                *t >= g + 1_000_000_000,
                "seed {seed}: confirmed {} ms after the drop",
                (t - g) / 1_000_000
            );
            assert!(
                *t >= a.max(b) + 250_000_000,
                "seed {seed}: a probe had no wait before the confirmation"
            );
            assert!(
                !after.iter().any(|(u, k)| *k == 3 && *u <= *t),
                "seed {seed}: hub {hub:?} confirmed at {t} after hearing the member"
            );
        }
    }
    checked
}

#[test]
fn a_confirmation_needs_two_probes_on_independent_paths_both_unanswered() {
    big(|| {
        let mut total = 0;
        for seed in 21u64..=60 {
            let w = accuracy_world(seed, 0.15, true);
            total += check_confirmations(&w, seed);
        }
        assert!(
            total > 0,
            "no confirmation happened on any seed, so the rule was not exercised"
        );
    });
}

#[test]
fn a_member_confirmed_down_while_alive_is_in_every_view_again() {
    big(|| {
        for seed in 21u64..=60 {
            let w = accuracy_world(seed, 0.15, false);
            complete(&w, seed, "after the confirmations of a lossy run");
        }
    });
}

#[test]
fn a_snapshot_after_a_heal_removes_nobody() {
    big(|| {
        for seed in [31u64, 32, 33] {
            let mut w = World::build_with(seed, 3, 6, |w| w.trace = true);
            let hubs: Vec<SimId> = w.hubs.iter().map(|(n, _)| *n).collect();
            let m = w.members.clone();
            // 50 s is longer than the transport's give-up time and shorter than the 80 s lease.
            let near: Vec<SimId> = hubs.iter().copied().chain(m[..3].iter().copied()).collect();
            let (cut_at, heal_at) = (secs(60), secs(110));
            w.sim.partition(cut_at, &[&near, &m[3..]]);
            w.sim.heal(heal_at);
            w.run(secs(300));
            // Every hub holds a carrier of every member, and the cut closes all of them. Each hub takes each cut member
            // down within the confirm deadline of its carrier closing: by its own two probes, or by the report of a
            // hub that confirmed first, which it accepts only once its own carrier of the member is closed. Which of
            // the two a hub does depends on whose carrier closed first, so the rule is stated for both.
            let cut: Vec<[u8; 32]> = m[3..].iter().map(|n| w.id(*n)).collect();
            let first = |h: SimId, pick: fn(&pinc_membership::Trace) -> Option<[u8; 32]>, member: &[u8; 32]| {
                w.sim.node(h).traces.iter().find_map(|(t, it)| match &it.body {
                    Body::Membership(x) if pick(x) == Some(*member) => Some(*t),
                    _ => None,
                })
            };
            let gone_of: fn(&pinc_membership::Trace) -> Option<[u8; 32]> = |x| match x {
                pinc_membership::Trace::CarrierGone { member } => Some(*member),
                _ => None,
            };
            let confirmed_of: fn(&pinc_membership::Trace) -> Option<[u8; 32]> = |x| match x {
                pinc_membership::Trace::Confirmed { member, .. } => Some(*member),
                _ => None,
            };
            let accepted_of: fn(&pinc_membership::Trace) -> Option<[u8; 32]> = |x| match x {
                pinc_membership::Trace::DownAccepted { member } => Some(*member),
                _ => None,
            };
            for c in &cut {
                let origin = hubs.iter().filter_map(|h| first(*h, confirmed_of, c)).min();
                let origin = origin.unwrap_or_else(|| panic!("seed {seed}: no hub confirmed a cut member down"));
                for h in &hubs {
                    let gone = first(*h, gone_of, c).unwrap_or_else(|| {
                        panic!("seed {seed}: hub {h:?} never saw the carrier of a cut member close")
                    });
                    let (confirmed, accepted) = (first(*h, confirmed_of, c), first(*h, accepted_of, c));
                    let down = confirmed
                        .into_iter()
                        .chain(accepted)
                        .min()
                        .unwrap_or_else(|| panic!("seed {seed}: hub {h:?} did not take a cut member down"));
                    assert!(
                        gone >= cut_at && down >= gone && down <= gone + 2 * pinc_membership::consts::CONFIRM,
                        "seed {seed}: hub {h:?} took a cut member down at {down} after the carrier closed at {gone}"
                    );
                    if let Some(t) = accepted {
                        assert!(
                            t >= origin,
                            "seed {seed}: hub {h:?} accepted a report at {t} that no hub had confirmed before {origin}"
                        );
                    }
                }
            }
            for h in &hubs {
                for (_, it) in &w.sim.node(*h).traces {
                    if let Body::Membership(
                        pinc_membership::Trace::Confirmed { member, .. }
                        | pinc_membership::Trace::DownAccepted { member },
                    ) = &it.body
                    {
                        assert!(
                            cut.contains(member),
                            "seed {seed}: hub {h:?} took a near-side node down"
                        );
                    }
                }
            }
            // The events: only cut members are ever removed, before the heal, and they are back in every view.
            for n in all_nodes(&w) {
                for (t, e) in w.member_events(n) {
                    let (pinc_membership::Event::MemberConfirmedDown { member: down }
                    | pinc_membership::Event::MemberLeft { member: down }) = e
                    else {
                        continue;
                    };
                    assert!(
                        cut.contains(&down) && t < heal_at,
                        "seed {seed} (a heal): node {n:?} removed {down:?} at {t}"
                    );
                }
            }
            complete(&w, seed, "a heal");
        }
    });
}

fn refusals(traces: &[(u64, TraceItem)], why: Refusal) -> usize {
    traces
        .iter()
        .filter(
            |(_, t)| matches!(t.body, Body::Membership(pinc_membership::Trace::DownRefused { why: w, .. }) if w == why),
        )
        .count()
}

#[test]
fn a_down_from_another_hub_is_refused_while_the_lease_is_fresh() {
    big(|| {
        for seed in [41u64, 42, 43] {
            let mut w = World::build_with(seed, 3, 4, |w| w.trace = true);
            let (a, b, c) = (w.hubs[0].0, w.hubs[1].0, w.hubs[2].0);
            let member = w.members[0];
            // Hub A loses sight of the member and of hub B at once, so both of its probes go unanswered; the member
            // keeps talking to B and C.
            w.sim.command(secs(41), member, NCmd::DropCarriers);
            w.sim.outage(a, member, secs(41), secs(47));
            w.sim.outage(a, b, secs(41), secs(47));
            w.run(secs(200));
            let confirmed_at_a = w
                .sim
                .node(a)
                .traces
                .iter()
                .filter(|(_, t)| matches!(t.body, Body::Membership(pinc_membership::Trace::Confirmed { .. })))
                .count();
            let refused = refusals(&w.sim.node(c).traces, Refusal::LeaseFresh);
            assert!(
                confirmed_at_a > 0,
                "seed {seed}: hub A never confirmed the member, so the scenario did not run"
            );
            assert!(refused > 0, "seed {seed}: hub C did not refuse the DOWN");
            no_one_accused(&w, seed, "a DOWN from another hub");
            complete(&w, seed, "a DOWN from another hub");
        }
    });
}
