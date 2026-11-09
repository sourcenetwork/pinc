//! Values of any size: a multi-GiB value (past 2^32 bytes) served and fetched in pieces through sparse stores.
//!
//! The provider generates the value on demand from a pattern, so it holds no value bytes, only its 16 MiB outboard;
//! the requester's store holds only what it fetched. Nothing in the protocol scales with the value length.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::assert_is_empty,
    clippy::doc_markdown,
    clippy::similar_names,
    clippy::single_range_in_vec_init,
    clippy::unreadable_literal,
    reason = "tests assert freely and name protocol rules in capitals"
)]

mod values_support;

use values_support::*;
use vinc_values::span::Span;
use vinc_values::trace::Trace;

const GROUP: u64 = 16384;

#[test]
fn a_multi_gib_value_is_fetched_in_pieces_from_several_providers() {
    let len: u64 = (1 << 32) + (3 << 20) + 12_345;
    let started = std::time::Instant::now();
    let store = PStore::pattern(0xB16, len);
    eprintln!(
        "built a {} GiB value (outboard {} MiB) in {:?}",
        len >> 30,
        store.0.outboard.len() >> 20,
        started.elapsed()
    );
    let ranges = [
        Span { off: 0, len: 40_000 },
        Span {
            off: (1 << 32) - 20_000,
            len: 100_000,
        },
        Span {
            off: (1 << 31) + 7,
            len: 3 * GROUP,
        },
        Span {
            off: len - 50_000,
            len: 50_000,
        },
    ];
    let cfgs = vec![
        ProvCfg::new(store.clone(), 20_000),
        ProvCfg::new(store.clone(), 20_000).loss(15),
        ProvCfg::new(store.clone(), 9_000),
    ];
    let mut sim = Sim::new(cfgs, ClientStore::new());
    let ps = sim.all_providers();
    sim.start_with(&ranges, &ps, None);
    sim.run(600);
    assert!(sim.rec.complete(), "{:?}", sim.rec.failed());

    // Exactly the groups the ranges touch are verified and stored, all true, nothing else.
    let mut want: Vec<(u64, u64)> = Vec::new();
    for r in &ranges {
        let (a, b) = (r.off / GROUP * GROUP, (r.off + r.len).div_ceil(GROUP) * GROUP);
        want.push((a, b.min(len)));
    }
    let wanted: u64 = {
        let mut sorted = want.clone();
        sorted.sort_unstable();
        sorted.dedup();
        sorted.iter().map(|(a, b)| b - a).sum()
    };
    assert_eq!(sim.store.covered(), wanted);
    for (a, b) in &want {
        assert!(sim.store.verified.contains_range(*a..*b));
    }
    sim.store.assert_verified_is_true(store.content());
    assert!(
        sim.store.written < 1 << 20,
        "the sparse store holds only what was fetched ({} bytes)",
        sim.store.written
    );

    // Past 1 GiB the tree is too deep for range proofs to fit a frame: no write-through proofs are sent, and the
    // lossy provider's gaps are repaired by retransmission alone.
    assert!(
        sim.provs
            .iter()
            .all(|p| !p.rec.traces.iter().any(|(_, t)| matches!(t, Trace::ProofSent { .. })))
    );

    // Resume across the 2^32 boundary: a second fetch of the same ranges asks for nothing.
    let kept = std::mem::take(&mut sim.store);
    let mut again = Sim::new(vec![ProvCfg::new(store.clone(), 20_000)], kept);
    let ps = again.all_providers();
    again.start_with(&ranges, &ps, None);
    assert!(again.rec.complete());
    assert!(
        again
            .rec
            .traces
            .iter()
            .all(|(_, t)| !matches!(t, Trace::Requested { .. }))
    );
}
