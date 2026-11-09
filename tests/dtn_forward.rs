//! Tests of spray-and-wait forwarding: copy conservation over a forwarding graph, and timers frozen while links are
//! down.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::similar_names,
    clippy::trivially_copy_pass_by_ref,
    clippy::struct_field_names,
    clippy::cast_lossless,
    clippy::range_plus_one,
    clippy::many_single_char_names,
    clippy::items_after_statements,
    clippy::needless_pass_by_value
)]

use proptest::prelude::*;
use vinc_crypto::{IdentityAlg, NodeId};
use vinc_dtn::forward::{Action, ForwardError, Forwarder, Held, Input, Policy};
use vinc_dtn::head::BundleId;
use vinc_tests::SplitMix64;

type Fwd = Forwarder<4, 8, 32, 8>;

const POLICY: Policy = Policy {
    retry_ms: 100,
    max_sends: 3,
};

fn node(n: u8) -> NodeId {
    NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [n; 32],
    }
}

const BUNDLE: BundleId = BundleId([42; 32]);

fn held(dest: u8, copies: u16, expires: u64) -> Held {
    Held {
        id: BUNDLE,
        destination: node(dest),
        expires,
        copies,
    }
}

fn drain(f: &mut Fwd) -> Vec<Action> {
    std::iter::from_fn(|| f.poll()).collect()
}

fn send(peer: u8, copies: u16, retransmit: bool) -> Action {
    Action::Send {
        peer: node(peer),
        bundle: BUNDLE,
        copies,
        retransmit,
    }
}

#[test]
fn binary_spray_halves_then_waits_for_the_destination() {
    let mut f = Fwd::new(POLICY, 0);
    f.step(0, Input::Hold(held(99, 8, 10_000))).unwrap();
    let mut given = vec![];
    for peer in 1..=4 {
        f.step(0, Input::LinkUp(node(peer))).unwrap();
        for a in drain(&mut f) {
            if let Action::Send { copies, .. } = a {
                given.push(copies);
            }
        }
    }
    // 8 -> hands 4 (keeps 4), hands 2 (keeps 2), hands 1 (keeps 1), then one copy waits.
    assert_eq!(given, vec![4, 2, 1]);
    assert_eq!(f.copies_held(&BUNDLE), Some(1));
    assert_eq!(f.copies_handed(&BUNDLE), 7);
    // The destination is served even with a single copy, with a delivery (no copies).
    f.step(0, Input::LinkUp(node(99))).unwrap();
    assert_eq!(drain(&mut f), vec![send(99, 0, false)]);
    // Never twice to the same peer: bouncing a link produces nothing new.
    f.step(1, Input::LinkDown(node(1))).unwrap();
    f.step(2, Input::LinkUp(node(1))).unwrap();
    assert!(drain(&mut f).is_empty());
    // The destination acknowledges: the bundle is done.
    f.step(
        3,
        Input::Acked {
            peer: node(99),
            bundle: BUNDLE,
        },
    )
    .unwrap();
    assert_eq!(drain(&mut f), vec![Action::Release(BUNDLE)]);
    assert_eq!(f.copies_held(&BUNDLE), None);
}

#[test]
fn bundles_expire_even_while_links_are_down() {
    let mut f = Fwd::new(POLICY, 0);
    f.step(0, Input::Hold(held(99, 2, 500))).unwrap();
    f.step(499, Input::Tick).unwrap();
    assert!(drain(&mut f).is_empty());
    f.step(500, Input::Tick).unwrap();
    assert_eq!(drain(&mut f), vec![Action::Release(BUNDLE)]);
}

#[test]
fn timers_are_frozen_while_the_link_is_down() {
    let mut f = Fwd::new(POLICY, 0);
    f.step(0, Input::Hold(held(99, 4, u64::MAX))).unwrap();
    f.step(0, Input::LinkUp(node(1))).unwrap();
    assert_eq!(drain(&mut f), vec![send(1, 2, false)]);
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), Some(100));
    f.step(40, Input::Tick).unwrap();
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), Some(60));
    f.step(40, Input::LinkDown(node(1))).unwrap();
    // A long outage: not a millisecond of it counts.
    f.step(1_000_000, Input::Tick).unwrap();
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), Some(60));
    assert!(drain(&mut f).is_empty());
    f.step(2_000_000, Input::LinkUp(node(1))).unwrap();
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), Some(60));
    f.step(2_000_059, Input::Tick).unwrap();
    assert!(drain(&mut f).is_empty());
    f.step(2_000_060, Input::Tick).unwrap();
    assert_eq!(drain(&mut f), vec![send(1, 2, true)]);
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), Some(100));
}

#[test]
fn a_timer_that_ran_out_waits_for_its_link() {
    let mut f = Fwd::new(POLICY, 0);
    f.step(0, Input::Hold(held(99, 4, u64::MAX))).unwrap();
    f.step(0, Input::LinkUp(node(1))).unwrap();
    drain(&mut f);
    f.step(100, Input::LinkDown(node(1))).unwrap();
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), Some(0));
    assert!(drain(&mut f).is_empty());
    f.step(5_000, Input::LinkUp(node(1))).unwrap();
    assert_eq!(drain(&mut f), vec![send(1, 2, true)]);
}

#[test]
fn a_transfer_is_given_up_after_max_sends_but_its_copies_stay_assigned() {
    let mut f = Fwd::new(POLICY, 0);
    f.step(0, Input::Hold(held(99, 4, u64::MAX))).unwrap();
    f.step(0, Input::LinkUp(node(1))).unwrap();
    let mut sends = drain(&mut f).len();
    for t in 1..=10 {
        f.step(t * 100, Input::Tick).unwrap();
        sends += drain(&mut f).len();
    }
    assert_eq!(sends, 3, "the first send plus two retransmissions");
    assert_eq!(f.timer_remaining(&node(1), &BUNDLE), None);
    assert_eq!(f.copies_held(&BUNDLE), Some(2));
    assert_eq!(f.copies_handed(&BUNDLE), 2, "handed copies are never taken back");
}

#[test]
fn an_acknowledged_transfer_is_not_repeated() {
    let mut f = Fwd::new(POLICY, 0);
    f.step(0, Input::Hold(held(99, 4, u64::MAX))).unwrap();
    f.step(0, Input::LinkUp(node(1))).unwrap();
    drain(&mut f);
    f.step(
        10,
        Input::Acked {
            peer: node(1),
            bundle: BUNDLE,
        },
    )
    .unwrap();
    f.step(10_000, Input::Tick).unwrap();
    assert!(drain(&mut f).is_empty());
    assert_eq!(
        f.step(
            10_000,
            Input::Acked {
                peer: node(7),
                bundle: BUNDLE
            }
        ),
        Err(ForwardError::Unknown)
    );
}

#[test]
fn inputs_are_validated_and_tables_are_bounded() {
    let mut f = Forwarder::<1, 1, 1, 1>::new(POLICY, 0);
    assert_eq!(f.step(0, Input::Hold(held(9, 0, 10))), Err(ForwardError::NoCopies));
    f.step(0, Input::Hold(held(9, 3, 10))).unwrap();
    assert_eq!(f.step(0, Input::Hold(held(9, 3, 10))), Err(ForwardError::Duplicate));
    let other = Held {
        id: BundleId([1; 32]),
        ..held(9, 3, 10)
    };
    assert_eq!(f.step(0, Input::Hold(other)), Err(ForwardError::Full));
    f.step(0, Input::LinkUp(node(1))).unwrap();
    assert_eq!(f.step(0, Input::LinkUp(node(2))), Err(ForwardError::Full));
    // One transfer slot: the second peer gets nothing until the first bundle goes.
    assert_eq!(f.poll(), Some(send(1, 1, false)));
    assert_eq!(f.poll(), None);
    assert_eq!(f.step(0, Input::Forget(BUNDLE)), Ok(()));
    assert_eq!(f.step(0, Input::Forget(BUNDLE)), Err(ForwardError::Unknown));
    // Time never runs backwards.
    f.step(50, Input::Tick).unwrap();
    f.step(10, Input::Tick).unwrap();
}

/// A message in flight between two nodes of the simulated graph.
struct Msg {
    at: u64,
    from: usize,
    to: usize,
    copies: u16,
    retransmit: bool,
}

struct Sim {
    nodes: Vec<Fwd>,
    queue: Vec<Msg>,
    now: u64,
    dest: usize,
    delivered: bool,
    budget: u16,
    dropped: u32,
    released: u32,
    sprayed: u32,
}

impl Sim {
    fn new(n: usize, budget: u16) -> Self {
        let dest = n - 1;
        let mut nodes: Vec<Fwd> = (0..n).map(|_| Fwd::new(POLICY, 0)).collect();
        nodes[0]
            .step(0, Input::Hold(held(dest as u8, budget, u64::MAX)))
            .unwrap();
        Self {
            nodes,
            queue: vec![],
            now: 0,
            dest,
            delivered: false,
            budget,
            dropped: 0,
            released: 0,
            sprayed: 0,
        }
    }

    /// Collect the actions of every node into messages.
    fn pump(&mut self, rng: &mut SplitMix64, loss_per_mille: u64) {
        for i in 0..self.nodes.len() {
            loop {
                let before = u32::from(self.nodes[i].copies_held(&BUNDLE).unwrap_or(0));
                let Some(a) = self.nodes[i].poll() else { break };
                if a == Action::Release(BUNDLE) {
                    // A finished bundle takes the copies its holder still had with it.
                    self.released += before;
                }
                if let Action::Send {
                    peer,
                    copies,
                    retransmit,
                    ..
                } = a
                {
                    let to = usize::from(peer.bytes[0]);
                    self.sprayed += u32::from(copies > 0 && !retransmit);
                    if rng.next_u64() % 1000 < loss_per_mille {
                        continue;
                    }
                    let at = self.now + rng.next_u64() % 40;
                    self.queue.push(Msg {
                        at,
                        from: i,
                        to,
                        copies,
                        retransmit,
                    });
                }
            }
        }
    }

    fn deliver_due(&mut self) {
        let now = self.now;
        let (due, rest): (Vec<Msg>, Vec<Msg>) = std::mem::take(&mut self.queue).into_iter().partition(|m| m.at <= now);
        self.queue = rest;
        for m in due {
            if m.to == self.dest {
                self.delivered = true;
            } else {
                let h = held(self.dest as u8, m.copies, u64::MAX);
                if self.nodes[m.to].step(now, Input::Hold(h)).is_err() {
                    // A node that already holds the bundle (or has no room) ignores the copies: they are lost.
                    self.dropped += u32::from(m.copies);
                }
            }
            // The acknowledgement is immediate and reliable here; loss is modelled on the data messages.
            let _ = self.nodes[m.from].step(
                now,
                Input::Acked {
                    peer: node(m.to as u8),
                    bundle: BUNDLE,
                },
            );
        }
    }

    fn held_total(&self) -> u32 {
        self.nodes
            .iter()
            .filter_map(|n| n.copies_held(&BUNDLE))
            .map(u32::from)
            .sum()
    }
}

fn run(n: usize, budget: u16, steps: usize, seed: u64, loss_per_mille: u64) -> Sim {
    let mut sim = Sim::new(n, budget);
    let mut rng = SplitMix64::new(seed);
    let mut up: Vec<(usize, usize)> = vec![];
    for _ in 0..steps {
        sim.now += 1 + rng.next_u64() % 30;
        // Flip one random link of the graph between two nodes.
        let (a, b) = ((rng.next_u64() as usize) % n, (rng.next_u64() as usize) % n);
        if a != b {
            if let Some(at) = up.iter().position(|&l| l == (a.min(b), a.max(b))) {
                up.swap_remove(at);
                let _ = sim.nodes[a].step(sim.now, Input::LinkDown(node(b as u8)));
                let _ = sim.nodes[b].step(sim.now, Input::LinkDown(node(a as u8)));
            } else {
                up.push((a.min(b), a.max(b)));
                let _ = sim.nodes[a].step(sim.now, Input::LinkUp(node(b as u8)));
                let _ = sim.nodes[b].step(sim.now, Input::LinkUp(node(a as u8)));
            }
        }
        for node in &mut sim.nodes {
            let _ = node.step(sim.now, Input::Tick);
        }
        sim.pump(&mut rng, loss_per_mille);
        sim.deliver_due();
        let held = sim.held_total();
        assert!(
            held <= u32::from(sim.budget),
            "{held} copies exist, budget {}",
            sim.budget
        );
        if loss_per_mille == 0 {
            // Nothing is lost: every copy is held, in flight, dropped by a receiver that already had the bundle, or
            // released with a finished bundle. The total is exact at every step.
            assert!(sim.queue.iter().all(|m| !m.retransmit));
            let in_flight: u32 = sim.queue.iter().map(|m| u32::from(m.copies)).sum();
            assert_eq!(held + in_flight + sim.dropped + sim.released, u32::from(sim.budget));
        }
    }
    sim
}

#[test]
fn copies_are_conserved_exactly_when_nothing_is_lost() {
    // Some seeds meet the destination before anyone else and finish at once; across seeds the graph does spray.
    let sprayed: u32 = (0..20).map(|seed| run(6, 32, 400, seed, 0).sprayed).sum();
    assert!(sprayed > 20, "only {sprayed} sprays");
}

#[test]
fn the_bundle_reaches_its_destination_under_loss() {
    let reached = (0..20u64).filter(|&seed| run(5, 16, 600, seed, 300).delivered).count();
    assert!(reached >= 15, "only {reached} of 20 runs delivered");
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn the_copy_budget_is_conserved_across_a_forwarding_graph(
        n in 3usize..7,
        budget in 1u16..40,
        seed in any::<u64>(),
        loss in 0u64..600,
    ) {
        let sim = run(n, budget, 250, seed, loss);
        prop_assert!(sim.held_total() <= u32::from(budget));
        // Every node's books balance on their own: copies held plus copies handed out never exceed what it
        // received, which for the source is the budget.
        prop_assert!(sim.nodes[0].copies_held(&BUNDLE).unwrap_or(0) as u32 + sim.nodes[0].copies_handed(&BUNDLE) <= u32::from(budget));
    }
}

#[test]
fn a_finished_bundle_is_not_held_again_before_it_expires() {
    let mut f = Forwarder::<1, 2, 2, 2>::new(POLICY, 0);
    f.step(0, Input::Hold(held(2, 4, 100))).unwrap();
    f.step(0, Input::LinkUp(node(2))).unwrap();
    assert_eq!(f.poll(), Some(send(2, 0, false)));
    f.step(
        1,
        Input::Acked {
            peer: node(2),
            bundle: BUNDLE,
        },
    )
    .unwrap();
    assert_eq!(f.poll(), Some(Action::Release(BUNDLE)));
    // A late duplicate of the hold must not create copies the budget already counted.
    assert_eq!(f.step(2, Input::Hold(held(2, 4, 100))), Err(ForwardError::Finished));
    assert_eq!(f.copies_held(&BUNDLE), None);
    assert_eq!(f.ignored_holds(), 1);
    assert_eq!(f.poll(), None);
    // The memory ends with the bundle's own expiry.
    assert_eq!(f.step(100, Input::Hold(held(2, 4, 200))), Ok(()));
    assert_eq!(f.copies_held(&BUNDLE), Some(4));
}

#[test]
fn a_forgotten_bundle_stays_finished_and_a_full_memory_refuses_new_holds() {
    let mut f = Forwarder::<2, 1, 1, 1>::new(POLICY, 0);
    f.step(0, Input::Hold(held(9, 3, 50))).unwrap();
    f.step(0, Input::Forget(BUNDLE)).unwrap();
    assert_eq!(f.step(0, Input::Hold(held(9, 3, 50))), Err(ForwardError::Finished));
    // The only memory slot belongs to the finished bundle: a new bundle is refused, the finished one is kept.
    let other = Held {
        id: BundleId([1; 32]),
        ..held(9, 3, 50)
    };
    assert_eq!(f.step(0, Input::Hold(other)), Err(ForwardError::Full));
    assert_eq!(f.step(49, Input::Hold(held(9, 3, 50))), Err(ForwardError::Finished));
    assert_eq!(f.step(50, Input::Hold(other)), Ok(()));
}
