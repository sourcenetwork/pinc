//! `pinc-node`: one reconcile round between a real node (its sets layer on, small message limits, a long set
//! reference) and an honest peer that runs the `pinc-reconcile` state machine with the same limits, the node on either
//! side of the round.
//!
//! Where the expected behaviour comes from:
//! - `pinc_reconcile::Limits::max_message`: "A difference of any size is spread over as many messages as it needs, as
//!   long as the limit is at least `min_message`". Every generated limit is at least `Limits::min_message()`.
//! - `Node::sets_start` (pinc-node reconcile.rs): "The exact difference comes out of `Node::poll_event` as
//!   `NodeEvent::ReconcileDone`". So a round the node starts against an honest peer ends in `ReconcileDone` with the
//!   items the peer has and the node lacks (`missing_here`) and the items the node has and the peer lacks
//!   (`missing_there`), and a round an honest peer starts against the node ends with the peer's report exact.
//!
//! The network is one shape here, two nodes and no node that carries the relay role: a reconcile round runs on a
//! session the endpoint already holds, the same over a direct path or a relayed one.

mod node_harness;

use std::collections::BTreeSet;

use ephyra::{check_generator, check_shrinker, gens};
use node_harness::{Peer, Seen, build, exchange, node_id, node_opens, peer_opens, peer_report};
use pinc_reconcile::{Initiator, Limits, MemIndex, Responder};

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Item {
    /// 0: both sides hold it; 1: only the node; 2: only the peer.
    #[ephyra(gen = gens::int(0u8..=2))]
    owner: u8,
    /// Its length, per mille of the item limit (at least 2 bytes); the longest items fill the messages fastest.
    #[ephyra(gen = gens::frequency(vec![(2, gens::constant(1000u16).boxed()), (3, gens::int(0u16..=1000).boxed())]))]
    len_share: u16,
    tail: u32,
}

#[derive(Clone, Debug, ephyra::Arbitrary)]
struct Case {
    #[ephyra(gen = gens::frequency(vec![(3, gens::int(8usize..=64).boxed()), (1, gens::int(8usize..=600).boxed())]))]
    max_item: usize,
    /// The message limit above `min_message`.
    #[ephyra(gen = gens::frequency(vec![(4, gens::int(0usize..=64).boxed()), (1, gens::int(0usize..=8_000).boxed())]))]
    slack: usize,
    /// The set reference's length, per mille of the item limit (at least 1 byte).
    #[ephyra(gen = gens::frequency(vec![(2, gens::constant(1000u16).boxed()), (1, gens::int(0u16..=1000).boxed())]))]
    ref_share: u16,
    /// The node starts the round; else the peer does.
    node_starts: bool,
    #[ephyra(gen = gens::vec(ephyra::any::<Item>()).len(0..=300))]
    items: Vec<Item>,
}

struct World {
    limits: Limits,
    set_ref: Vec<u8>,
    node_items: Vec<Vec<u8>>,
    peer_items: Vec<Vec<u8>>,
    only_node: BTreeSet<Vec<u8>>,
    only_peer: BTreeSet<Vec<u8>>,
}

fn share(max: usize, per_mille: u16, min: usize) -> usize {
    (max * usize::from(per_mille) / 1000).clamp(min, max)
}

/// The items, distinct by construction (the first two bytes are the item's position), and the limits.
fn world(c: &Case) -> World {
    let base = Limits {
        max_item: c.max_item,
        ..Limits::default()
    };
    let limits = Limits {
        max_message: base.min_message() + c.slack,
        ..base
    };
    let set_ref = (0..share(c.max_item, c.ref_share, 1)).map(|i| (i as u8) ^ 0x5a).collect();
    let (mut node_items, mut peer_items) = (Vec::new(), Vec::new());
    let (mut only_node, mut only_peer) = (BTreeSet::new(), BTreeSet::new());
    for (i, it) in c.items.iter().enumerate() {
        let mut x = u64::from(it.tail);
        let mut item: Vec<u8> = (i as u16).to_be_bytes().to_vec();
        while item.len() < share(c.max_item, it.len_share, 2) {
            x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
            item.push(((x ^ (x >> 29)).wrapping_mul(0xbf58_476d_1ce4_e5b9) >> 56) as u8);
        }
        match it.owner {
            0 => {
                node_items.push(item.clone());
                peer_items.push(item);
            },
            1 => {
                only_node.insert(item.clone());
                node_items.push(item);
            },
            _ => {
                only_peer.insert(item.clone());
                peer_items.push(item);
            },
        }
    }
    node_items.sort();
    peer_items.sort();
    World {
        limits,
        set_ref,
        node_items,
        peer_items,
        only_node,
        only_peer,
    }
}

fn run(c: &Case) {
    let w = world(c);
    let idx = MemIndex::from_sorted(w.peer_items.iter().map(Vec::as_slice)).unwrap();
    let mut node = build(&w.set_ref, &w.node_items, w.limits);
    let peer_id = node_id(0x22);
    let mut seen = Seen::default();
    let ctx = format!(
        "max_item {}, max_message {} (min {}), set ref {} bytes, node {} items, peer {} items",
        w.limits.max_item,
        w.limits.max_message,
        w.limits.min_message(),
        w.set_ref.len(),
        w.node_items.len(),
        w.peer_items.len()
    );
    if c.node_starts {
        let opened = node_opens(&mut node, peer_id, &w.set_ref);
        assert!(opened.is_ok(), "{opened:?}; {ctx}");
        let Ok((s, x)) = opened else { return };
        let mut peer = Peer::Resp(Responder::new(w.limits));
        exchange(&mut node, s, x, &mut peer, &idx, &mut seen);
        let detail = format!(
            "{ctx}; longest bodies: node {}, peer {}; peer error {:?}; {} turns",
            seen.node_body, seen.peer_body, seen.peer_error, seen.turns
        );
        let outcome = seen.outcome.clone();
        assert!(matches!(outcome, Some(Ok(_))), "the round ended {outcome:?}; {detail}");
        let Some(Ok((here, there))) = outcome else { return };
        assert!(here == w.only_peer, "missing_here is not what the peer alone holds: {} for {}; {detail}", here.len(), w.only_peer.len());
        assert!(there == w.only_node, "missing_there is not what the node alone holds: {} for {}; {detail}", there.len(), w.only_node.len());
    } else {
        let mut init = Initiator::new(w.limits);
        let opened = peer_opens(&mut node, peer_id, &mut init, &idx, &w.set_ref, &mut seen);
        assert!(opened.is_ok(), "{opened:?}; {ctx}");
        let Ok((s, x)) = opened else { return };
        let mut peer = Peer::Init(init);
        exchange(&mut node, s, x, &mut peer, &idx, &mut seen);
        let detail = format!(
            "{ctx}; longest bodies: node {}, peer {}; {} turns",
            seen.node_body, seen.peer_body, seen.turns
        );
        assert!(seen.node_reset.is_none(), "the node reset the round's stream with code {:?}; {detail}", seen.node_reset);
        assert!(seen.peer_error.is_none(), "the honest peer refused a message of the node: {:?}; {detail}", seen.peer_error);
        let Peer::Init(init) = &peer else { return };
        let report = peer_report(init);
        assert!(report.is_some(), "the peer's round did not finish; {detail}");
        let Some((here, there)) = report else { return };
        assert!(here == w.only_node, "the peer's missing_here is not what the node alone holds: {} for {}; {detail}", here.len(), w.only_node.len());
        assert!(there == w.only_peer, "the peer's missing_there is not what it alone holds: {} for {}; {detail}", there.len(), w.only_peer.len());
    }
}

fn big<F: FnOnce() + Send + 'static>(f: F) {
    let h = std::thread::Builder::new().stack_size(256 << 20).spawn(f).unwrap();
    if let Err(e) = h.join() {
        std::panic::resume_unwind(e);
    }
}

#[test]
fn an_honest_round_through_the_node_ends_with_the_exact_difference_at_any_size() {
    big(|| {
        let config = ephyra::Config::default()
            .tests(60)
            .name("an_honest_round_through_the_node_ends_with_the_exact_difference_at_any_size");
        ephyra::check(&config, ephyra::any::<Case>(), |c: Case| run(&c)).assert_passed();
    });
}

fn in_support(c: &Case) -> bool {
    let w = world(c);
    (8..=600).contains(&c.max_item)
        && c.items.len() <= 300
        && (1..=c.max_item).contains(&w.set_ref.len())
        && w.node_items.iter().chain(&w.peer_items).all(|i| (2..=c.max_item).contains(&i.len()))
        && w.node_items.windows(2).all(|p| p[0] < p[1])
        && w.peer_items.windows(2).all(|p| p[0] < p[1])
}

#[test]
fn the_round_case_generator_stays_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    check_generator(&cfg, ephyra::any::<Case>(), in_support).assert_passed();
}

#[test]
fn the_round_case_shrinker_stays_in_support() {
    let cfg = ephyra::Config::default().tests(25);
    check_shrinker(&cfg, ephyra::any::<Case>(), in_support, case_size).assert_passed();
}

fn case_size(c: &Case) -> u64 {
    let items: u64 = c.items.iter().map(|i| 1 + u64::from(i.owner) + u64::from(i.len_share) + u64::from(i.tail)).sum();
    items + c.max_item as u64 + c.slack as u64 + u64::from(c.ref_share) + u64::from(c.node_starts)
}
