//! What the stream credit costs an opener: 16 bidirectional streams opened at once on a fresh connection, 64 KiB sent on
//! each, at 50 ms round trip, for receiver pools of 512, 1024 and 2048 chunks with the default stream window. Prints a
//! table (credit in the handshake, waves of opens, time until the last stream's first byte arrives) and pins the counts.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use vinc_crypto::IdentityAlg;
use vinc_tests::*;

const STREAMS: usize = 16;
const LEN: usize = 64 * 1024;

/// (handshake credit, waves of opens, milliseconds from the connection to the last first byte)
fn measure(chunks: usize) -> (u16, usize, u64) {
    let mut w = World::new(IdentityAlg::Ed25519);
    let (mut sa, mut sb) = (Store::with_chunks(true, 8192), Store::with_chunks(false, chunks));
    let mut net = setup(&mut w, &mut sa, &mut sb, Link::new(7, Params::new(25 * MS)));
    assert!(net.connect(net.now + 10 * SEC));
    net.run(net.now + SEC, |_| false);
    let credit = net.a.conn.peer_credit().max_streams;
    let t0 = net.now;
    let mut ids: Vec<u64> = Vec::new();
    let mut first: Vec<Option<u64>> = vec![None; STREAMS];
    let (mut waves, mut blocked) = (0usize, true);
    let mut closed: Vec<u64> = Vec::new();
    let data = vec![5u8; LEN];
    let (mut sent, mut ended) = ([0usize; STREAMS], [false; STREAMS]);
    let done = net.run(t0 + 120 * SEC, |n| {
        let before = ids.len();
        while ids.len() < STREAMS {
            match n.a.conn.open_bi() {
                Ok(id) => ids.push(id),
                Err(_) => break,
            }
        }
        // Every open stream gets its 64 KiB as the send buffer takes it, then its end.
        for (k, id) in ids.iter().enumerate() {
            while sent[k] < LEN {
                let m = n.a.conn.write(*id, &data[sent[k]..]).unwrap();
                if m == 0 {
                    break;
                }
                sent[k] += m;
            }
            if sent[k] == LEN && !ended[k] {
                n.a.conn.finish(*id).unwrap();
                ended[k] = true;
            }
        }
        if ids.len() > before && blocked {
            waves += 1;
        }
        blocked = ids.len() < STREAMS;
        for (k, id) in ids.iter().enumerate() {
            if first[k].is_none() && n.b.read.get(id).is_some_and(|v| !v.is_empty()) {
                first[k] = Some(n.now);
            }
        }
        // The receiver ends its half of every stream whose data arrived whole, as an echo service would.
        let ended: Vec<u64> = ids.iter().copied().filter(|id| n.b.fin.contains(id) && !closed.contains(id)).collect();
        for id in ended {
            n.b.conn.finish(id).unwrap();
            closed.push(id);
        }
        first.iter().all(Option::is_some)
    });
    assert!(done, "pool {chunks}: credit {credit}, opened {}, first bytes {} of {STREAMS}, at {} ms, receiver ended {}", ids.len(), first.iter().flatten().count(), (net.now - t0) / MS, closed.len());
    let last = first.iter().flatten().max().copied().unwrap();
    (credit, waves, (last - t0) / MS)
}

#[test]
fn the_cost_of_the_credit_to_an_opener_of_sixteen_streams() {
    big_stack(|| {
        println!("pool chunks | credit in the handshake | waves of opens | ms until the last first byte");
        let got: Vec<_> = [512usize, 1024, 2048]
            .into_iter()
            .map(|c| {
                let r = measure(c);
                println!("{c:>11} | {:>23} | {:>14} | {:>8}", r.0, r.1, r.2);
                r
            })
            .collect();
        // Measured on this link (the same run on the tree before the credit: credit 64, 1 wave, 260 ms for every pool).
        // With a quarter of the room as credit it was (1, 16, 784), (3, 14, 385) and (6, 11, 273).
        assert_eq!(got, [(3, 14, 385), (6, 11, 281), (12, 5, 260)]);
    });
}
