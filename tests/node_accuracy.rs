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
use vinc_membership::event::Refusal;
use vinc_node::{Body, TraceItem};
use vinc_sim::{LinkChange, LinkConfig, Loss, MS, NodeId as SimId};
use vinc_tests::NCmd;

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
                    vinc_membership::Event::MemberConfirmedDown { .. } | vinc_membership::Event::MemberLeft { .. }
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

#[test]
fn late_and_lost_answers_confirm_no_live_member() {
    big(|| {
        for seed in [21u64, 22, 23, 24] {
            let mut w = World::build(seed, 3, 6);
            let lossy_pairs: Vec<(SimId, SimId)> = w
                .members
                .iter()
                .flat_map(|m| w.hubs.iter().map(move |(h, _)| (*m, *h)))
                .collect();
            // 15% loss everywhere between members and hubs, from the start.
            for (m, h) in &lossy_pairs {
                w.sim.link_change(0, *m, *h, LinkChange::Config(lossy(5 * MS, 0.15)));
                w.sim.link_change(0, *h, *m, LinkChange::Config(lossy(5 * MS, 0.15)));
            }
            let members = w.members.clone();
            // Every member's carriers are reset once, staggered.
            for (i, m) in members.iter().enumerate() {
                w.sim.command(secs(50 + 7 * i as u64), *m, NCmd::DropCarriers);
            }
            // A slow member: its answers arrive 600 ms late for 20 s, around a carrier reset.
            let slow = members[0];
            for (h, _) in &w.hubs.clone() {
                w.sim.link_change(secs(100), slow, *h, LinkChange::Delay(600 * MS));
                w.sim.link_change(secs(100), *h, slow, LinkChange::Delay(600 * MS));
                w.sim.link_change(secs(120), slow, *h, LinkChange::Delay(5 * MS));
                w.sim.link_change(secs(120), *h, slow, LinkChange::Delay(5 * MS));
            }
            w.sim.command(secs(105), slow, NCmd::DropCarriers);
            w.run(secs(260));
            no_one_accused(&w, seed, "late and lost answers");
            complete(&w, seed, "late and lost answers");
        }
    });
}

#[test]
fn a_snapshot_after_a_heal_removes_nobody() {
    big(|| {
        for seed in [31u64, 32, 33] {
            let mut w = World::build(seed, 3, 6);
            let hubs: Vec<SimId> = w.hubs.iter().map(|(n, _)| *n).collect();
            let m = w.members.clone();
            // 50 s is longer than the transport's give-up time and shorter than the 80 s lease.
            let near: Vec<SimId> = hubs.iter().copied().chain(m[..3].iter().copied()).collect();
            w.sim.partition(secs(60), &[&near, &m[3..]]);
            w.sim.heal(secs(110));
            w.run(secs(300));
            no_one_accused(&w, seed, "a heal");
            complete(&w, seed, "a heal");
        }
    });
}

fn refusals(traces: &[(u64, TraceItem)], why: Refusal) -> usize {
    traces
        .iter()
        .filter(
            |(_, t)| matches!(t.body, Body::Membership(vinc_membership::Trace::DownRefused { why: w, .. }) if w == why),
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
                .filter(|(_, t)| matches!(t.body, Body::Membership(vinc_membership::Trace::Confirmed { .. })))
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
