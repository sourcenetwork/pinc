//! `pinc-dtn` custody across several nodes: the real `CustodyBook` and `Ledger` of each node against a reference
//! model, with acknowledgements that travel between nodes.
//!
//! Where the expected behaviour comes from (`crates/pinc-dtn/src/custody.rs`):
//! - the module: "the ack relieves the offerer only if it names the offer currently outstanding to that node";
//!   "custody is relieved only by a valid ack from exactly the node it was offered to, for exactly the offer
//!   outstanding"; "a custody item leaves the ledger only through delivery, expiry or relief (which keeps the bytes as
//!   transit)"; "the book never holds a record for an item the ledger no longer holds";
//! - `CustodyAck::previous`: "The node custody was taken from, to whom the ack is addressed", so an offer is named by
//!   its offerer, its custodian and its id together;
//! - `accept`: "A bundle already kept as transit is promoted without new room. A bundle already in custody here ...
//!   keeps its record, cancels the outstanding offer of this node and is acknowledged again. The returned AckDue is
//!   always addressed to the `previous` of `incoming`", with `Capacity` when the book is full;
//! - `offer`: "return the fresh offer id ... A new offer replaces the outstanding one", `Unknown` for a bundle not in
//!   custody; `on_ack` and `delivered` as documented; `expire`: "Expire items at `now` and drop their records".
//!
//! The existing `tests/trace_dtn_custody.rs` drives one book; here four nodes each keep a book and a ledger, and an
//! ack any node signed may reach any node (an ack is a signed statement anyone can carry), which is where the offer
//! ids of different books (each counting from 0) meet. Ledgers are large enough never to refuse, so the model of the
//! ledger is the set of kept bundles with their class and expiry.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

use std::collections::BTreeMap;

use ephyra::prelude::*;
use pinc_crypto::{IdentityAlg, Keypair, NodeId};
use pinc_dtn::custody::{AckDue, CustodyAck, CustodyBook, CustodyError, Incoming};
use pinc_dtn::head::BundleId;
use pinc_dtn::hlc::Hlc;
use pinc_dtn::store::{Class, Ledger};

const NODES: usize = 4;
const BUNDLES: u8 = 4;
const BOOK: usize = 3;

fn keypair(i: usize) -> Keypair {
    let seed: Vec<u8> = (0..IdentityAlg::Ed25519.seed_len()).map(|k| (k * 7 + i * 31 + 1) as u8).collect();
    Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap()
}

fn bundle(b: u8) -> BundleId {
    BundleId([b + 1; 32])
}

#[derive(Debug, Clone, ephyra::Arbitrary)]
enum Op {
    /// Node `node` accepts custody of `bundle` from node `from` with the offer id `offer`, living `life` ms.
    Accept(u8, u8, u8, #[ephyra(gen = gens::int(0u64..=3))] u64, #[ephyra(gen = gens::int(1u64..=20))] u64),
    /// Node `node` offers custody of `bundle` to node `to`.
    Offer(u8, u8, u8),
    /// One of the acks owed so far, signed by the node that owes it, reaches node `to`.
    Ack(u8, u8),
    /// One of the acks owed so far reaches node `to` with its custodian changed to node `as_`: a forgery.
    Forged(u8, u8, u8),
    /// A bundle in custody at `node` was delivered.
    Deliver(u8, u8),
    /// Time passes and every node expires its items.
    Tick(#[ephyra(gen = gens::int(1u64..=10))] u64),
}

/// The model of one node: its records (bundle -> previous, outstanding offer), its offer counter and its kept items.
#[derive(Default)]
struct MNode {
    recs: BTreeMap<u8, (usize, Option<(usize, u64)>)>,
    counter: u64,
    kept: BTreeMap<u8, (Class, u64)>,
}

impl MNode {
    fn sync(&mut self) {
        let kept = &self.kept;
        self.recs.retain(|b, _| kept.contains_key(b));
    }

    fn expire(&mut self, now: u64) {
        self.kept.retain(|_, (_, exp)| *exp > now);
        self.sync();
    }
}

struct Net {
    keys: Vec<Keypair>,
    ids: Vec<NodeId>,
    books: Vec<CustodyBook<BOOK>>,
    ledgers: Vec<Ledger<16>>,
    model: Vec<MNode>,
    /// Acks owed so far: (signer, what it owes).
    owed: Vec<(usize, AckDue)>,
    now: u64,
}

impl Net {
    fn new() -> Self {
        let keys: Vec<Keypair> = (0..NODES).map(keypair).collect();
        let ids = keys.iter().map(Keypair::node_id).collect();
        Self {
            keys,
            ids,
            books: (0..NODES).map(|_| CustodyBook::new()).collect(),
            ledgers: (0..NODES).map(|_| Ledger::new(1 << 20)).collect(),
            model: (0..NODES).map(|_| MNode::default()).collect(),
            owed: Vec::new(),
            now: 10,
        }
    }

    fn ix(&self, id: &NodeId) -> usize {
        self.ids.iter().position(|x| x == id).unwrap()
    }

    fn step(&mut self, op: &Op) {
        match *op {
            Op::Accept(n, b, from, offer, life) => {
                let n = usize::from(n) % NODES;
                let from = (n + 1 + usize::from(from) % (NODES - 1)) % NODES;
                let b = b % BUNDLES;
                let inc = Incoming { bundle: bundle(b), bytes: 1, expires: self.now + life, previous: self.ids[from], offer };
                let got = self.books[n].accept(&mut self.ledgers[n], inc, self.now, |_| {});
                let m = &mut self.model[n];
                m.expire(self.now);
                let due = AckDue { bundle: bundle(b), previous: self.ids[from], offer };
                let want = if let Some(r) = m.recs.get_mut(&b) {
                    r.1 = None;
                    Ok(due)
                } else if m.recs.len() == BOOK {
                    Err(CustodyError::Capacity)
                } else {
                    let exp = m.kept.get(&b).map_or(self.now + life, |k| k.1);
                    m.kept.insert(b, (Class::Custody, exp));
                    m.recs.insert(b, (from, None));
                    Ok(due)
                };
                assert_eq!(got, want, "accept at node {n} of bundle {b} from {from}");
                if let Ok(d) = got {
                    self.owed.push((n, d));
                }
            },
            Op::Offer(n, b, to) => {
                let n = usize::from(n) % NODES;
                let to = (n + 1 + usize::from(to) % (NODES - 1)) % NODES;
                let b = b % BUNDLES;
                let got = self.books[n].offer(&bundle(b), self.ids[to]);
                let m = &mut self.model[n];
                let want = match m.recs.get_mut(&b) {
                    Some(r) => {
                        let id = m.counter;
                        m.counter += 1;
                        r.1 = Some((to, id));
                        Ok(id)
                    },
                    None => Err(CustodyError::Unknown),
                };
                assert_eq!(got, want, "offer at node {n} of bundle {b} to {to}");
            },
            Op::Ack(k, to) => {
                if self.owed.is_empty() {
                    return;
                }
                let (signer, due) = self.owed[usize::from(k) % self.owed.len()];
                let to = usize::from(to) % NODES;
                let ack: CustodyAck = due.sign(Hlc::new(self.now, 0), &self.keys[signer]).unwrap();
                let got = self.books[to].on_ack(&mut self.ledgers[to], &ack);
                let b = (0..BUNDLES).find(|&x| bundle(x) == due.bundle).unwrap();
                let addressed = self.ix(&due.previous);
                let m = &mut self.model[to];
                let want = match m.recs.get(&b) {
                    None => Err(CustodyError::Unknown),
                    // The offer outstanding at `to`, named by its offerer (the ack's `previous`), custodian and id.
                    // `addressed == to` is what the docs ask; an ack addressed to another offerer that matches the
                    // custodian and the id relieves all the same (`repro_dtn.rs`,
                    // `an_ack_addressed_to_another_offerer_relieves_custody`): the model follows the code there only,
                    // so the property keeps looking for other faults.
                    Some((_, Some((c, id)))) if *c == signer && *id == due.offer => {
                        m.recs.remove(&b);
                        if let Some(e) = m.kept.get_mut(&b) {
                            e.0 = Class::Transit;
                        }
                        Ok(())
                    },
                    Some(_) => Err(CustodyError::NotOffered),
                };
                assert_eq!(
                    got, want,
                    "node {to} got the ack node {signer} owes node {addressed} for bundle {b} (offer {})",
                    due.offer
                );
            },
            Op::Forged(k, to, as_) => {
                if self.owed.is_empty() {
                    return;
                }
                let (signer, due) = self.owed[usize::from(k) % self.owed.len()];
                let to = usize::from(to) % NODES;
                let other = (signer + 1 + usize::from(as_) % (NODES - 1)) % NODES;
                let mut ack: CustodyAck = due.sign(Hlc::new(self.now, 0), &self.keys[signer]).unwrap();
                ack.custodian = self.ids[other];
                // custody.rs: "an ack is valid only if its signature verifies under the custodian's node id".
                let got = self.books[to].on_ack(&mut self.ledgers[to], &ack);
                assert!(matches!(got, Err(CustodyError::Ack(_))), "node {to} took a forged ack: {got:?}");
            },
            Op::Deliver(n, b) => {
                let n = usize::from(n) % NODES;
                let b = b % BUNDLES;
                let got = self.books[n].delivered(&mut self.ledgers[n], &bundle(b));
                let m = &mut self.model[n];
                let want = if m.recs.remove(&b).is_some() {
                    m.kept.remove(&b);
                    Ok(())
                } else {
                    Err(CustodyError::Unknown)
                };
                assert_eq!(got, want, "delivery at node {n} of bundle {b}");
            },
            Op::Tick(ms) => {
                self.now += ms;
                for n in 0..NODES {
                    self.books[n].expire(&mut self.ledgers[n], self.now, |_| {});
                    self.model[n].expire(self.now);
                }
            },
        }
    }

    fn check(&self) {
        for n in 0..NODES {
            let (book, led, m) = (&self.books[n], &self.ledgers[n], &self.model[n]);
            assert_eq!(book.len(), m.recs.len(), "node {n}: the book's length");
            for b in 0..BUNDLES {
                let id = bundle(b);
                assert_eq!(book.holds(&id), m.recs.contains_key(&b), "node {n}: holds bundle {b}");
                assert_eq!(book.owed_to(&id), m.recs.get(&b).map(|r| self.ids[r.0]), "node {n}: ack of {b} owed to");
                let class = led.get(&id.store_key()).map(|e| (e.class, e.expires));
                assert_eq!(class, m.kept.get(&b).copied(), "node {n}: the ledger's entry of bundle {b}");
                if book.holds(&id) {
                    assert!(led.contains(&id.store_key()), "node {n}: a record of {b} the ledger does not hold");
                }
            }
        }
    }
}

fn ops() -> impl Gen<Value = Vec<Op>> {
    gens::vec(ephyra::any::<Op>()).len(0..=60)
}

/// Every call of every node's book returns what the reference model says, and after every call the books and the
/// ledgers hold exactly the model's records and items.
#[ephyra::test(gen = ops(), tests = 300)]
fn custody_books_follow_the_reference_model(ops: Vec<Op>) {
    let mut net = Net::new();
    for op in &ops {
        net.step(op);
        net.check();
    }
}
