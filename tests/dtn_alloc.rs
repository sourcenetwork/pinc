//! The hot paths of the delay-tolerant layer never touch the heap.
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

mod dtn_common;

use dtn_common::{ALGS, bytes, keypair, make, plan, recipient, seeds};
use vinc_crypto::{IdentityAlg, Software};
use vinc_dtn::bundle::{Outgoing, Reception, seal_bundle, serve, serve_len};
use vinc_dtn::custody::{CustodyBook, Incoming};
use vinc_dtn::forward::{Forwarder, Held, Input, Policy};
use vinc_dtn::head::{BundleId, MAX_SIGNED_HEAD_LEN, SignedHead};
use vinc_dtn::hlc::Hlc;
use vinc_dtn::rs::Rs;
use vinc_dtn::seal::decapsulate;
use vinc_dtn::store::{Class, Key, Ledger, Space};
use vinc_tests::measure;

vinc_tests::install_counting_allocator!();

#[test]
fn erasure_coding_does_not_allocate() {
    let rs = Rs::new(20, 10).unwrap();
    let len = 1024;
    let mut block = bytes(1, rs.n() * len);
    let mut present = [true; 30];
    present[..10].fill(false);
    let stats = measure(|| {
        rs.encode(len, &mut block).unwrap();
        rs.reconstruct(len, &mut block, &present).unwrap();
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}

#[test]
fn sealing_receiving_and_opening_do_not_allocate() {
    let sender = keypair(IdentityAlg::Ed25519, 1);
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    let payload = bytes(3, 20_000);
    let pl = plan(4, 2, 1);
    let layout = vinc_dtn::layout::SliceLayout::new(4, 2, 1, payload.len() as u64).unwrap();
    let mut sealed = vec![0; layout.total_len() as usize];
    let mut outboard = vec![0; layout.outboard_len().unwrap() as usize];
    let sd = seeds(9);
    let out = Outgoing {
        recipient: &to.keys,
        plan: pl,
        seeds: &sd,
    };
    let mut signed = None;
    let stats = measure(|| {
        signed = Some(seal_bundle(&Software, &sender, &out, &payload, &mut sealed, &mut outboard).unwrap());
    });
    assert_eq!(stats.count(), 0, "seal_bundle: {stats:?}");
    let signed = signed.unwrap();

    let total = layout.total_symbols();
    let mut proof = vec![0; serve_len(&layout, &(0..total)).unwrap()];
    let stats = measure(|| {
        serve(&layout, &sealed, &outboard, &(0..total), &mut proof).unwrap();
    });
    assert_eq!(stats.count(), 0, "serve: {stats:?}");

    let mut buf = vec![0; layout.total_len() as usize];
    let mut ob2 = vec![0; outboard.len()];
    let mut scratch = vec![0; layout.block_n(0) * layout.slice_len() as usize];
    let mut padded = vec![0; layout.padded_len() as usize];
    let skip = 1..3u64;
    let (p_a, p_b) = (
        {
            let mut v = vec![0; serve_len(&layout, &(0..1)).unwrap()];
            serve(&layout, &sealed, &outboard, &(0..1), &mut v).unwrap();
            v
        },
        {
            let mut v = vec![0; serve_len(&layout, &(3..total)).unwrap()];
            serve(&layout, &sealed, &outboard, &(3..total), &mut v).unwrap();
            v
        },
    );
    let stats = measure(|| {
        let mut rx = Reception::<8>::new(&signed, &mut buf, 0).unwrap();
        rx.feed(0..1, &p_a).unwrap();
        rx.feed(3..total, &p_b).unwrap();
        assert!(rx.holds(0) && !rx.holds(skip.start));
        rx.finish(&mut ob2, &mut scratch).unwrap();
        let cipher = decapsulate(&Software, &to.keys, &to.dk, &to.xs, signed.head()).unwrap();
        let n = rx.open(&Software, &cipher, &mut padded).unwrap();
        assert_eq!(n, payload.len());
    });
    assert_eq!(stats.count(), 0, "receive: {stats:?}");
    assert_eq!(&padded[..payload.len()], &payload[..]);
}

#[test]
fn heads_and_acks_do_not_allocate_for_any_algorithm() {
    let to = recipient(IdentityAlg::Ed25519, 2, 1);
    for (i, alg) in ALGS.into_iter().enumerate() {
        let sender = keypair(alg, 10 + i as u64);
        let s = make(&sender, &to, plan(2, 1, 0), &bytes(1, 100), 5);
        let mut enc = vec![0; MAX_SIGNED_HEAD_LEN];
        let stats = measure(|| {
            let n = s.signed.encode(&mut enc).unwrap();
            let back = SignedHead::decode(&enc[..n]).unwrap();
            back.verify().unwrap();
            let ack =
                vinc_dtn::custody::CustodyAck::sign(back.head().id, back.head().destination, 7, Hlc::new(1, 0), &sender)
                    .unwrap();
            ack.verify().unwrap();
        });
        assert_eq!(stats.count(), 0, "{alg:?}: {stats:?}");
    }
}

#[test]
fn store_custody_and_forwarding_do_not_allocate() {
    let node = |n: u8| vinc_crypto::NodeId {
        alg: IdentityAlg::Ed25519,
        bytes: [n; 32],
    };
    let mut ledger = Ledger::<16>::new(1_000);
    let mut book = CustodyBook::<16>::new();
    let mut fwd = Forwarder::<8, 8, 32, 64>::new(
        Policy {
            retry_ms: 50,
            max_sends: 3,
        },
        0,
    );
    let stats = measure(|| {
        for i in 0..40u8 {
            let key = Key {
                space: Space::DTN,
                id: [i; 32],
            };
            let class = if i % 3 == 0 { Class::Custody } else { Class::Transit };
            let _ = ledger.admit(key, 90, class, 500 + u64::from(i), u64::from(i), |_| {});
            let _ = book.accept(
                &mut ledger,
                Incoming {
                    bundle: BundleId([i; 32]),
                    bytes: 10,
                    expires: 900,
                    previous: node(1),
                    offer: 0,
                },
                u64::from(i),
                |_| {},
            );
            ledger.expire(u64::from(i) * 20, |_| {});
            if i % 7 == 0 {
                ledger.release(&key);
            }
            let _ = fwd.step(
                u64::from(i) * 10,
                Input::Hold(Held {
                    id: BundleId([i; 32]),
                    destination: node(200),
                    expires: 10_000,
                    copies: 8,
                }),
            );
            let _ = fwd.step(u64::from(i) * 10, Input::LinkUp(node(i % 5)));
            while fwd.poll().is_some() {}
        }
    });
    assert_eq!(stats.count(), 0, "{stats:?}");
}
