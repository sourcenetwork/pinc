//! Reproductions of `pinc-dtn` bugs found by the properties in `dtn_custody.rs`, each a plain test that fails on the
//! unmodified code.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::indexing_slicing)]

use pinc_crypto::{IdentityAlg, Keypair};
use pinc_dtn::custody::{CustodyBook, CustodyError, Incoming};
use pinc_dtn::head::BundleId;
use pinc_dtn::hlc::Hlc;
use pinc_dtn::store::{Class, Ledger};

fn keypair(i: usize) -> Keypair {
    let seed: Vec<u8> = (0..IdentityAlg::Ed25519.seed_len()).map(|k| (k * 7 + i * 31 + 1) as u8).collect();
    Keypair::from_seed(IdentityAlg::Ed25519, &seed).unwrap()
}

/// custody.rs, module doc: "the ack relieves the offerer only if it names the offer currently outstanding to that
/// node"; invariants: "custody is relieved only by a valid ack from exactly the node it was offered to, for exactly
/// the offer outstanding"; `CustodyAck::previous`: "The node custody was taken from, to whom the ack is addressed".
///
/// Actual: S hands custody of bundle X to B (S's offer 0); B accepts and its ack relieves S, which keeps X as transit.
/// B hands custody on to A (B's offer 0), A accepts and its ack relieves B. A then offers X back to B (A's offer 0,
/// every book counts from 0); B is busy and does not take it. A replays B's old ack to S (custodian B, previous S, offer
/// 0), which anyone who carried it holds: A's book takes it as B's answer to its own offer and relieves A. Now no
/// node holds X in custody: S, B and A all keep it as evictable transit, so it can be lost although the custody chain
/// was never closed by delivery or expiry. The same ack relieved its true addressee earlier; only its `previous`
/// tells the two offers apart, and the book never reads it. Found by `custody_books_follow_the_reference_model`
/// (shrunk input `[Accept(110, 123, 0, 0, 1), Accept(1, 191, 0, 0, 1), Offer(1, 43, 0), Ack(0, 1)]`,
/// EPHYRA_REPLAY=21:585).
///
/// Suspected fault: `CustodyBook::on_ack` (custody.rs:385-401) compares only `(ack.custodian, ack.offer)` with the
/// outstanding `Offered { to, id }`, and offer ids are per book from 0 (custody.rs:258-262, 377-378), so an ack
/// addressed to another offerer matches. The book does not know its own node id, so it cannot check `ack.previous`;
/// `pinc-node` checks it before calling (crates/pinc-node/src/dtn.rs:922-925), so the node is not affected, but any
/// other host of the public `CustodyBook` API is. Who can trigger it: any peer holding an ack the custodian signed for
/// another offerer with the same offer id (acks travel in the clear and verify anywhere).
#[test]
fn an_ack_addressed_to_another_offerer_relieves_custody() {
    let (s, b, a) = (keypair(0), keypair(1), keypair(2));
    let x = BundleId([9; 32]);
    let now = 10;
    let mut book_b: CustodyBook<4> = CustodyBook::new();
    let mut book_a: CustodyBook<4> = CustodyBook::new();
    let (mut led_b, mut led_a) = (Ledger::<8>::new(1 << 20), Ledger::<8>::new(1 << 20));
    // S's offer 0 to B; B accepts and owes S an ack for it.
    let due_b = book_b
        .accept(&mut led_b, Incoming { bundle: x, bytes: 10, expires: 1_000, previous: s.node_id(), offer: 0 }, now, |_| {})
        .unwrap();
    let ack_b_to_s = due_b.sign(Hlc::new(now, 0), &b).unwrap();
    // B's offer to A; A accepts and its ack relieves B.
    let to_a = book_b.offer(&x, a.node_id()).unwrap();
    let due_a = book_a
        .accept(&mut led_a, Incoming { bundle: x, bytes: 10, expires: 1_000, previous: b.node_id(), offer: to_a }, now, |_| {})
        .unwrap();
    book_b.on_ack(&mut led_b, &due_a.sign(Hlc::new(now, 1), &a).unwrap()).unwrap();
    assert!(!book_b.holds(&x), "B was relieved by A's ack");
    // A offers X back to B; B never takes it.
    let back = book_a.offer(&x, b.node_id()).unwrap();
    assert_eq!((back, ack_b_to_s.offer), (0, 0), "both offers have id 0");
    // B's old ack to S reaches A.
    let got = book_a.on_ack(&mut led_a, &ack_b_to_s);
    let class = led_a.get(&x.store_key()).map(|e| e.class);
    assert_eq!(
        got,
        Err(CustodyError::NotOffered),
        "an ack addressed to S relieved A; A now keeps X as {class:?} and B holds it in custody: {}",
        book_b.holds(&x)
    );
    assert_eq!(class, Some(Class::Custody), "A must still hold X in custody");
}
