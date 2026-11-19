//! Delivery scoped to the publisher's connected component (pinc#86): members that name the peers they hold sessions
//! with are reached by a hub only from origins a chain of such sessions links them to, as on a gossip mesh.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::expect_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation
)]

#[path = "broadcast_common.rs"]
mod common;

#[path = "broadcast_reach_support.rs"]
mod support;

use common::{Net, SEC, WALL0, ty};
use pinc_broadcast::Topics;
use pinc_broadcast::consts::{ADJ_MAX, RECORD_TTL, REFRESH};
use pinc_crypto::IdentityAlg;
use pinc_membership::NodeId;
use support::{T, adj, ask, capture, got, offered, sends, session};

#[test]
fn two_groups_on_one_hub_hear_only_their_own_group_even_through_gap_repair() {
    // Hub 0; group A is 1 - 2, group B is 3 - 4, no session between the groups.
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 4, SEC);
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 1, 2, true);
    session(&mut net, &mut edges, 3, 4, true);
    for i in 1..=4 {
        net.subscribe(i, T);
    }
    let a = net.publish(1, T, b"from a1");
    let b = net.publish(3, T, b"from b1");
    assert!(got(&net, 2, a) && got(&net, 4, b), "each group hears its own");
    assert!(!got(&net, 3, a) && !got(&net, 4, a), "group B does not hear A");
    assert!(!got(&net, 1, b) && !got(&net, 2, b), "group A does not hear B");

    // Gap repair: a GET for the other group's id is not answered, and a SUB is offered no id of the other group.
    assert!(ask(&mut net, 0, 4, ty::GET, &a).is_empty(), "GET across groups");
    assert!(!ask(&mut net, 0, 4, ty::GET, &b).is_empty(), "GET within the group");
    let since = WALL0.to_be_bytes();
    let have = offered(&ask(&mut net, 0, 4, ty::SUB, &since));
    assert!(
        have.contains(&b) && !have.contains(&a),
        "HAVE offers only the group's ids: {have:?}"
    );
    let replay = ask(&mut net, 0, 2, ty::SUB, &[&since[..], &[1]].concat());
    let replayed: Vec<&[u8]> = replay
        .iter()
        .filter(|f| f.get(4) == Some(&ty::MSG))
        .map(|f| &f[6 + T.len()..6 + T.len() + 8])
        .collect();
    assert_eq!(replayed, [&a[..]], "the replay to A2 carries A1's message and not B1's");

    // The periodic checks run for a minute and still bring nothing across.
    net.advance(60 * SEC);
    assert!(!got(&net, 3, a) && !got(&net, 4, a) && !got(&net, 1, b) && !got(&net, 2, b));
}

#[test]
fn on_a_line_a_b_c_the_ends_reach_each_other_through_b() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 1, 2, true);
    session(&mut net, &mut edges, 2, 3, true);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    let c = net.publish(3, T, b"key request");
    assert!(
        got(&net, 1, c) && got(&net, 2, c),
        "C's request reaches A two hops away"
    );
    let a = net.publish(1, T, b"key reply");
    assert!(got(&net, 3, a) && got(&net, 2, a), "A's reply reaches C");
}

#[test]
fn a_session_joins_components_and_its_end_splits_them_within_one_round_trip() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    adj(&mut net, 1, &[]);
    adj(&mut net, 2, &[]);
    net.subscribe(1, T);
    net.subscribe(2, T);
    assert!(!sends(&mut net, 1, 2, b"apart"), "no session: apart");

    // One end's word is not an edge.
    adj(&mut net, 1, &[2]);
    assert!(!sends(&mut net, 1, 2, b"half"), "only one end reported the session");
    assert!(!net.nodes[0].t.same_component(&net.id(1), &net.id(2)));

    // Both ends report it: the next message crosses.
    adj(&mut net, 2, &[1]);
    assert!(sends(&mut net, 1, 2, b"joined"), "joined by the session");

    // The session ends: the first end that reports it splits the components.
    adj(&mut net, 1, &[]);
    assert!(!sends(&mut net, 1, 2, b"split"), "split as soon as one end dropped it");
    assert!(!sends(&mut net, 2, 1, b"split back"));
}

#[test]
fn a_lost_record_is_repaired_by_the_refresh() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 1, 2, true);
    net.subscribe(1, T);
    net.subscribe(2, T);
    assert!(sends(&mut net, 1, 2, b"joined"));

    // Both ends' records of the split are lost on the way to the hub.
    let lost = std::rc::Rc::new(std::cell::Cell::new(true));
    let l = lost.clone();
    net.filter = Some(Box::new(move |_, _, b: &mut Vec<u8>| {
        !(l.get() && b.get(4) == Some(&ty::ADJ))
    }));
    session(&mut net, &mut edges, 1, 2, false);
    lost.set(false);
    assert!(
        sends(&mut net, 1, 2, b"stale"),
        "the hub has not heard of the split yet"
    );
    net.advance(REFRESH);
    assert!(!sends(&mut net, 1, 2, b"after refresh"), "split within one refresh");
}

#[test]
fn a_record_not_heard_for_its_ttl_expires() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    adj(&mut net, 1, &[2]);
    adj(&mut net, 2, &[1]);
    assert_eq!(net.nodes[0].t.reach_stats().live, 2);
    // Node 2 goes away without a word: its refreshes stop reaching the hub.
    net.link(2, 0, false);
    net.advance(RECORD_TTL + REFRESH + SEC);
    let stats = net.nodes[0].t.reach_stats();
    assert_eq!(
        (stats.live, stats.records),
        (1, 2),
        "the refreshed record and a tombstone"
    );
    assert!(!net.nodes[0].t.same_component(&net.id(1), &net.id(2)));
}

#[test]
fn two_hubs_that_mirror_records_scope_alike() {
    // Hubs 0 and 1; A1 = 2 and B1 = 4 use hub 0, A2 = 3 and B2 = 5 use hub 1. A1 - A2 and B1 - B2 hold sessions.
    let mut net = Net::new(IdentityAlg::Ed25519, 2, 4, SEC);
    net.set_primary(3, 1);
    net.set_primary(5, 1);
    // Each member reaches only its own hub, so the other hub learns its record only through the mirror.
    for (m, other) in [(2, 1), (4, 1), (3, 0), (5, 0)] {
        net.link(m, other, false);
    }
    let mut edges = Vec::new();
    session(&mut net, &mut edges, 2, 3, true);
    session(&mut net, &mut edges, 4, 5, true);
    for i in 2..=5 {
        net.subscribe(i, T);
    }
    for hub in 0..2 {
        let t = &net.nodes[hub].t;
        assert_eq!(t.reach_stats().live, 4, "hub {hub} holds every record");
        assert!(t.same_component(&net.id(2), &net.id(3)) && t.same_component(&net.id(4), &net.id(5)));
        assert!(!t.same_component(&net.id(2), &net.id(4)) && !t.same_component(&net.id(3), &net.id(5)));
    }
    let a = net.publish(2, T, b"a1 on hub 0");
    let b = net.publish(5, T, b"b2 on hub 1");
    assert!(
        got(&net, 3, a) && got(&net, 4, b),
        "each reaches its group across the hubs"
    );
    assert!(!got(&net, 4, a) && !got(&net, 5, a) && !got(&net, 2, b) && !got(&net, 3, b));
}

#[test]
fn a_scoped_member_and_an_unscoped_one_do_not_hear_each_other_and_unscoped_ones_keep_full_reach() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    adj(&mut net, 1, &[]);
    for i in 1..=3 {
        net.subscribe(i, T);
    }
    let s = net.publish(1, T, b"scoped");
    let u = net.publish(2, T, b"unscoped");
    assert!(
        !got(&net, 2, s) && !got(&net, 3, s),
        "a scoped origin reaches no unscoped member"
    );
    assert!(!got(&net, 1, u), "an unscoped origin reaches no scoped member");
    assert!(got(&net, 3, u), "unscoped members hear each other as before");
}

#[test]
fn a_record_is_taken_only_from_its_member_or_a_hub_and_only_with_its_signature() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 3, SEC);
    adj(&mut net, 1, &[3]);
    // Node 3's record, captured on its way to the hub.
    let rest = capture(&mut net, 3, &[1]);
    // Another member hands it in: refused, so the edge 1 - 3 is not made on node 1's word alone.
    ask(&mut net, 0, 2, ty::ADJ, &rest);
    assert!(!net.nodes[0].t.same_component(&net.id(1), &net.id(3)));
    // A flipped bit of the signature: refused even from its member.
    let mut bad = rest.clone();
    *bad.last_mut().unwrap() ^= 1;
    ask(&mut net, 0, 3, ty::ADJ, &bad);
    assert!(!net.nodes[0].t.same_component(&net.id(1), &net.id(3)));
    ask(&mut net, 0, 3, ty::ADJ, &rest);
    assert!(
        net.nodes[0].t.same_component(&net.id(1), &net.id(3)),
        "the genuine record from its member"
    );
}

#[test]
fn every_identity_algorithm_signs_a_record_the_hub_takes() {
    for alg in common::ALGS {
        let mut net = Net::new(alg, 1, 2, SEC);
        adj(&mut net, 1, &[2]);
        adj(&mut net, 2, &[1]);
        assert!(net.nodes[0].t.same_component(&net.id(1), &net.id(2)), "{alg:?}");
    }
}

#[test]
fn a_record_names_at_most_adj_max_peers() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 1, SEC);
    let many: Vec<NodeId> = (0..=ADJ_MAX as u32)
        .map(|i| {
            let mut id = [0u8; 32];
            id[..4].copy_from_slice(&i.to_be_bytes());
            id
        })
        .collect();
    let now = net.now;
    let n = &mut net.nodes[1];
    // One past the bound: the least ADJ_MAX ids are named, a subset of the sessions, which only narrows the reach.
    assert_eq!(n.t.set_adjacent(&mut n.h, now, &many), Ok(ADJ_MAX));
    assert_eq!(n.t.adjacent(), Some(&many[..ADJ_MAX]));
    net.pump();
    assert_eq!(net.nodes[0].t.reach_stats().live, 1, "the hub took the cut record");
}

/// The components of `edges` over `n` nodes by breadth-first search: the reference the hub's labels must equal.
fn reference(n: usize, edges: &[(usize, usize)]) -> Vec<usize> {
    let mut comp = vec![usize::MAX; n];
    for s in 0..n {
        if comp[s] != usize::MAX {
            continue;
        }
        let mut q = vec![s];
        comp[s] = s;
        while let Some(x) = q.pop() {
            for (a, b) in edges {
                for (u, v) in [(*a, *b), (*b, *a)] {
                    if u == x && comp[v] == usize::MAX {
                        comp[v] = s;
                        q.push(v);
                    }
                }
            }
        }
    }
    comp
}

#[test]
fn the_hub_components_equal_breadth_first_search_on_random_graphs_with_one_sided_claims() {
    let mut seed = 0x9e37_79b9_7f4a_7c15u64;
    let mut xorshift = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for _ in 0..40 {
        let members = 7;
        let mut net = Net::new(IdentityAlg::Ed25519, 1, members, SEC);
        // Each node claims a random set; an edge exists only where both claim it.
        let claims: Vec<Vec<usize>> = (1..=members)
            .map(|i| (1..=members).filter(|j| *j != i && xorshift() % 3 == 0).collect())
            .collect();
        for (k, c) in claims.iter().enumerate() {
            adj(&mut net, k + 1, c);
        }
        let mutual: Vec<(usize, usize)> = (0..members)
            .flat_map(|a| (0..members).map(move |b| (a, b)))
            .filter(|(a, b)| a < b && claims[*a].contains(&(b + 1)) && claims[*b].contains(&(a + 1)))
            .collect();
        let want = reference(members, &mutual);
        let hub: &Topics = &net.nodes[0].t;
        for a in 0..members {
            for b in 0..members {
                assert_eq!(
                    hub.same_component(&net.id(a + 1), &net.id(b + 1)),
                    want[a] == want[b],
                    "claims {claims:?}, nodes {a} and {b}"
                );
            }
        }
    }
}

#[test]
fn two_members_whose_records_expired_stay_scoped_and_do_not_hear_each_other() {
    let mut net = Net::new(IdentityAlg::Ed25519, 1, 2, SEC);
    adj(&mut net, 1, &[]);
    adj(&mut net, 2, &[]);
    net.subscribe(1, T);
    net.subscribe(2, T);
    // Their refreshes stop reaching the hub, and both records expire.
    net.filter = Some(Box::new(|_, _, b: &mut Vec<u8>| b.get(4) != Some(&ty::ADJ)));
    net.advance(RECORD_TTL + REFRESH + SEC);
    assert_eq!(net.nodes[0].t.reach_stats().live, 0);
    assert!(
        !net.nodes[0].t.same_component(&net.id(1), &net.id(2)),
        "each is alone, not unscoped"
    );
    assert!(!sends(&mut net, 1, 2, b"after expiry"));
    // Heard again: back in its own component, with its record.
    net.filter = None;
    net.advance(REFRESH);
    assert_eq!(net.nodes[0].t.reach_stats().live, 2);
}
