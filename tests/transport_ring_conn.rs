//! A connection whose send ring is two chunks wide, on a lossy, reordering link: frames cross chunk boundaries, the
//! chunks are released by acknowledgements that arrive late and the ring wraps, and tail repairs and resends are built
//! all the while. The receiver must read every byte as it was written at its offset, and neither end may close.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use pinc_crypto::IdentityAlg;
use pinc_tests::*;
use pinc_transport::stream;

const RING: usize = 2;
const SEEDS: u64 = 24;
const LEN: usize = 6 * 16_384 + 777;

#[test]
fn a_resend_over_a_wrapped_two_chunk_ring_never_carries_another_offsets_bytes() {
    big_stack(|| {
        let mut repairs = 0;
        let mut lost = 0;
        for seed in 0..SEEDS {
            let mut w = World::new(IdentityAlg::Ed25519);
            let mut sa = Store::<RING>::sized(256, &stream::Config::new(true));
            let mut sb = Store::<RING>::sized(256, &stream::Config::new(false));
            let p = Params::new(10 * MS)
                .loss(4.0)
                .dup(1.0)
                .reorder(4.0, 25 * MS)
                .jitter(2 * MS);
            let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(seed, p));
            assert!(net.connect(net.now + 60 * SEC), "seed {seed}: {:?}", net.a.log);
            let data = pattern(LEN, seed);
            let (_, id) = bulk(&mut net, &data, 600 * SEC);
            assert!(
                net.b.read[&id] == data,
                "seed {seed}: the receiver read bytes that were not written"
            );
            assert_eq!(net.a.closed(), None, "seed {seed}");
            assert_eq!(net.b.closed(), None, "seed {seed}");
            let s = net.a.conn.stats();
            repairs += s.repairs;
            lost += s.packets_lost;
        }
        eprintln!("{SEEDS} seeds: {lost} packets lost, {repairs} repair packets");
    });
}
