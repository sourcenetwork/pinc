//! A carrier that holds custody for a destination that slept delivers after the destination wakes: the carrier looks
//! at its contacts when it starts holding a bundle, so its dial of the destination backs off while the destination
//! sleeps and the first dial after the wake delivers. A membership event about the destination clears that backoff.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

mod layers_common;

use layers_common::{LWorld, OWD, big, secs};
use pinc_node::{BACKOFF_CAP, DtnPlan, Enabled, NodeEvent};
use pinc_sim::{MS, NodeId as SimId, SEC, Time};
use pinc_tests::{LayerApps, NCmd, SplitMix64};

/// One dial of the delay-tolerant layer to a peer that is up, from the dial to the carrier's report of delivery: the
/// handshake and the hand-over (offer, request, symbols, acknowledgement) on this link. Measured on the unchanged
/// code, where a dial started by the phone's return took 0.54 s (dial at 51.51 s, report at 52.05 s).
const DIAL: Time = 54 * OWD;

fn plan() -> DtnPlan {
    DtnPlan {
        lifetime_ms: 200_000,
        copies: 2,
        k: 4,
        m: 2,
        slice_log: 2,
    }
}

/// The hub, and the laptop, cloud and phone in id order (custody moves up the order, so the laptop ranks below the
/// carrier and the phone is the destination).
fn world(seed: u64) -> (LWorld, [SimId; 3]) {
    let mk = |tag| {
        let mut apps = LayerApps::new(
            tag,
            Enabled {
                dtn: true,
                ..Enabled::NONE
            },
        );
        apps.dtn.policy.max_sends = 60;
        apps
    };
    let probe = LWorld::build(seed, 1, 3, mk);
    let mut order: Vec<usize> = (0..3).collect();
    order.sort_by_key(|i| probe.id(probe.members[*i]));
    let w = LWorld::build_with(seed, 1, 3, 0, true, mk);
    let nodes = [0, 1, 2].map(|k| w.members[order[k]]);
    (w, nodes)
}

fn body(seed: u64) -> Vec<u8> {
    let mut v = vec![0; 3000];
    SplitMix64::new(seed).fill(&mut v);
    v
}

fn first_at(w: &LWorld, n: SimId, want: impl Fn(&NodeEvent) -> bool) -> Option<Time> {
    w.node_events(n).into_iter().find(|(_, e)| want(e)).map(|(t, _)| t)
}

/// The times `n` heard a membership event about `peer`.
fn member_events(w: &LWorld, n: SimId, peer: [u8; 32]) -> Vec<Time> {
    use pinc_membership::Event::{
        AddressChanged, MemberConfirmedDown, MemberJoined, MemberLeft, MemberRevoked, StackChanged,
    };
    w.node_events(n)
        .into_iter()
        .filter_map(|(t, e)| match e {
            NodeEvent::Member(
                MemberJoined { member }
                | MemberConfirmedDown { member }
                | MemberLeft { member }
                | MemberRevoked { member }
                | AddressChanged { member }
                | StackChanged { member, .. },
            ) if member == peer => Some(t),
            _ => None,
        })
        .collect()
}

/// The times the carrier dialed the delay-tolerant layer of `peer`.
fn dials(w: &LWorld, carrier: SimId, peer: [u8; 32]) -> Vec<Time> {
    let tag = u32::from_be_bytes([peer[0], peer[1], peer[2], peer[3]]);
    let line = format!("LayerDial {{ layer: 3, peer: {tag} }}");
    w.sim
        .node(carrier)
        .traces
        .iter()
        .filter(|(_, t)| format!("{:?}", t.body).contains(&line))
        .map(|(at, _)| *at)
        .collect()
}

#[test]
fn a_carrier_that_holds_custody_for_a_destination_that_slept_delivers_after_it_wakes() {
    big(|| {
        for seed in [601u64, 602] {
            let (mut w, [laptop, cloud, phone]) = world(seed);
            let (t0, sent, laptop_off, wake) = (secs(30), secs(32), secs(42), secs(50));
            let keys = w.apps(phone).dtn.keys();
            let payload = body(seed);
            // A sleeping device keeps its carriers, so nobody learns it is down: the sleepers are cut off from the
            // rest instead of suspended (a suspended node closes its sockets, which the hub reads as a departure).
            let hub_cloud: Vec<SimId> = w.hubs.iter().map(|h| h.0).chain([cloud]).collect();
            let with_cloud: Vec<SimId> = hub_cloud.iter().copied().chain([laptop]).collect();
            w.sim.partition(t0, &[&[phone], &with_cloud]);
            w.sim.command(
                sent,
                laptop,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: payload.clone(),
                    plan: plan(),
                },
            );
            w.sim.partition(laptop_off, &[&[phone], &[laptop], &hub_cloud]);
            let with_phone: Vec<SimId> = hub_cloud.iter().copied().chain([phone]).collect();
            w.sim.partition(wake, &[&[laptop], &with_phone]);
            w.run(wake + secs(120));

            assert!(
                first_at(&w, cloud, |e| matches!(e, NodeEvent::DtnCustody { .. })).is_some_and(|t| t < laptop_off),
                "seed {seed}: the carrier took custody before the laptop slept"
            );
            // The dial that follows the wake is at most the backoff in force plus one dial: a failed dial of a peer
            // doubles its wait from BACKOFF_FIRST up to BACKOFF_CAP, so no wait is longer than BACKOFF_CAP.
            let bound = wake + BACKOFF_CAP + DIAL;
            let got = w.node_events(phone).into_iter().find_map(|(t, e)| match e {
                NodeEvent::DtnReceived { payload, .. } => Some((t, payload)),
                _ => None,
            });
            let (at, got) = got.unwrap_or_else(|| panic!("seed {seed}: the phone received nothing"));
            assert_eq!(got, payload, "seed {seed}: the bundle is intact");
            assert!(
                at > wake && at <= bound,
                "seed {seed}: delivered at {} s, wake at {} s, bound {} s",
                at / SEC,
                wake / SEC,
                bound / SEC
            );
            let done = first_at(&w, cloud, |e| matches!(e, NodeEvent::DtnDelivered { .. }))
                .unwrap_or_else(|| panic!("seed {seed}: the carrier reported no delivery"));
            assert!(
                done > wake && done <= bound,
                "seed {seed}: the carrier reports it in time"
            );
            let phone_id = w.id(phone);
            // The carrier dials the phone while it sleeps, on its own and not on word of the phone: no membership
            // event about the phone reaches it between the send and the wake.
            let tried = dials(&w, cloud, phone_id);
            assert!(
                tried.iter().any(|t| *t > sent && *t < wake),
                "seed {seed}: the carrier dialed the phone for the layer before it woke: dials {tried:?}"
            );
            assert!(
                member_events(&w, cloud, phone_id)
                    .iter()
                    .all(|t| *t <= sent || *t >= wake),
                "seed {seed}: no membership event about the phone reached the carrier while it slept"
            );
        }
    });
}

#[test]
fn the_return_of_a_member_the_carrier_gave_up_on_is_met_by_a_dial_at_once() {
    big(|| {
        for seed in [611u64, 612] {
            let (mut w, [laptop, cloud, phone]) = world(seed);
            // The phone is out of reach for long enough to be confirmed down, so the carrier's dials of it have
            // backed off to the cap by the time it returns and the hubs announce it.
            let (t0, sent, back) = (secs(30), secs(32), secs(130));
            let keys = w.apps(phone).dtn.keys();
            let payload = body(seed);
            let hub_cloud: Vec<SimId> = w.hubs.iter().map(|h| h.0).chain([cloud]).collect();
            let with_laptop: Vec<SimId> = hub_cloud.iter().copied().chain([laptop]).collect();
            w.sim.partition(t0, &[&[phone], &with_laptop]);
            w.sim.command(
                sent,
                laptop,
                NCmd::DtnSend {
                    to: Box::new(keys),
                    payload: payload.clone(),
                    plan: DtnPlan {
                        lifetime_ms: 400_000,
                        ..plan()
                    },
                },
            );
            // The laptop has handed the bundle to the carrier by then and stays away, so only the carrier can deliver.
            w.sim.partition(secs(40), &[&[phone], &[laptop], &hub_cloud]);
            let with_phone: Vec<SimId> = hub_cloud.iter().copied().chain([phone]).collect();
            w.sim.partition(back, &[&[laptop], &with_phone]);
            w.run(back + secs(120));

            let phone_id = w.id(phone);
            let heard = member_events(&w, cloud, phone_id);
            let announced = heard
                .iter()
                .copied()
                .find(|t| *t > back)
                .unwrap_or_else(|| panic!("seed {seed}: the carrier never heard of the phone's return: {heard:?}"));
            let done = first_at(&w, cloud, |e| matches!(e, NodeEvent::DtnDelivered { .. }))
                .unwrap_or_else(|| panic!("seed {seed}: the carrier reported no delivery"));
            // The announcement ends the carrier's wait: delivery follows within one dial of it, where the backoff
            // in force would have held the dial for up to BACKOFF_CAP.
            assert!(
                done > announced && done <= announced + DIAL,
                "seed {seed}: announced at {} ms, delivered at {} ms, one dial is {} ms; dials {:?}; events {heard:?}",
                announced / MS,
                done / MS,
                DIAL / MS,
                dials(&w, cloud, phone_id)
            );
        }
    });
}
