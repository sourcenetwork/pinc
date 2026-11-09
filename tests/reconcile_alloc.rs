//! The state machines allocate nothing once their buffers are warm: a second session on the same objects, over the
//! same sets, makes no allocation, in the split exchange, the cold stream and the exact pass.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::expect_used
)]

#[path = "reconcile_common.rs"]
mod common;

use common::{fixed_set, index, mutate};
use vinc_reconcile::{Initiator, Limits, MemIndex, Responder, Step};
use vinc_tests::{SplitMix64, measure};

vinc_tests::install_counting_allocator!();

/// One session with preallocated message buffers and no clones, so that only the library can allocate.
fn session(init: &mut Initiator, resp: &mut Responder, a: &MemIndex, b: &MemIndex, tx: &mut Vec<u8>, rx: &mut Vec<u8>) {
    resp.reset();
    init.start(a, b"set", tx).unwrap();
    'session: loop {
        let mut step = resp.handle(b, tx, rx).unwrap();
        loop {
            match step {
                Step::Send | Step::Last => match init.handle(a, rx, tx).unwrap() {
                    Step::Send => continue 'session,
                    Step::Last => {
                        resp.handle(b, tx, rx).unwrap();
                        return;
                    }
                    _ => return,
                },
                Step::Chunk => {
                    assert_eq!(init.handle(a, rx, tx).unwrap(), Step::Wait);
                    step = resp.resume(b, rx).unwrap();
                }
                Step::Done | Step::Wait => return,
            }
        }
    }
}

fn warm_then_measure(a: &[Vec<u8>], b: &[Vec<u8>], limits: Limits) -> (u64, usize) {
    let (ia, ib) = (index(a), index(b));
    let (mut init, mut resp) = (Initiator::new(limits), Responder::new(limits));
    let (mut tx, mut rx) = (Vec::with_capacity(1 << 20), Vec::with_capacity(1 << 20));
    session(&mut init, &mut resp, &ia, &ib, &mut tx, &mut rx);
    let found = init.report().unwrap().here_count() + init.report().unwrap().there_count();
    let stats = measure(|| session(&mut init, &mut resp, &ia, &ib, &mut tx, &mut rx));
    (stats.count(), found)
}

#[test]
fn a_warm_split_exchange_allocates_nothing() {
    let mut rng = SplitMix64::new(21);
    let a = fixed_set(&mut rng, 50_000, 40);
    let (b, ..) = mutate(&mut rng, &a, 300, 40);
    let (allocs, found) = warm_then_measure(&a, &b, Limits::default());
    assert_eq!(found, 300);
    assert_eq!(allocs, 0);
}

#[test]
fn a_warm_chunked_exchange_allocates_nothing() {
    let mut rng = SplitMix64::new(24);
    let a = fixed_set(&mut rng, 20_000, 40);
    let (b, ..) = mutate(&mut rng, &a, 6000, 40);
    let limits = Limits {
        max_message: 16_384,
        ..Limits::default()
    };
    let (allocs, found) = warm_then_measure(&a, &b, limits);
    assert_eq!(found, 6000);
    assert_eq!(allocs, 0);
}

#[test]
fn a_warm_cold_stream_allocates_nothing() {
    let mut rng = SplitMix64::new(22);
    let big = fixed_set(&mut rng, 20_000, 40);
    let small: Vec<_> = big.iter().step_by(500).cloned().collect();
    let limits = Limits {
        max_message: 32_768,
        ..Limits::default()
    };
    let (allocs, found) = warm_then_measure(&small, &big, limits);
    assert_eq!(found, big.len() - small.len());
    assert_eq!(allocs, 0);
}

#[test]
fn a_warm_identical_session_allocates_nothing() {
    let mut rng = SplitMix64::new(23);
    let a = fixed_set(&mut rng, 10_000, 40);
    assert_eq!(warm_then_measure(&a, &a, Limits::default()), (0, 0));
}
