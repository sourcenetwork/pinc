//! The ring against a `VecDeque`: the same pushes, pops, peeks and refusals when full leave the same length and the
//! same FIFO order after every step, across many wraps of the block.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::similar_names
)]

use std::collections::VecDeque;

use proptest::prelude::*;
use vinc_table::{Error, Ring, Storage};

fn mem(n: usize, owned: bool) -> Storage {
    if owned {
        Storage::zeroed(n).unwrap()
    } else {
        Storage::from_static(Box::leak(vec![0xa5u8; n].into_boxed_slice()))
    }
}

fn run(ops: &[(u8, u32)], cap: usize, spare: usize, owned: bool) {
    let mut r = Ring::new(mem(Ring::bytes(cap, 4) + spare, owned), cap, 4).unwrap();
    let mut m: VecDeque<u32> = VecDeque::new();
    for (i, &(op, v)) in ops.iter().enumerate() {
        let at = format!("op {i} ({op} {v})");
        match op % 4 {
            0 | 1 => {
                let got = r.push(&v.to_le_bytes());
                if m.len() == cap {
                    assert_eq!(got, Err(Error::Full), "{at}");
                } else {
                    assert_eq!(got, Ok(()), "{at}");
                    m.push_back(v);
                }
            }
            2 => {
                let got = r.pop().map(|b| u32::from_le_bytes(b.try_into().unwrap()));
                assert_eq!(got, m.pop_front(), "{at}");
            }
            _ => {
                let got = r.peek().map(|b| u32::from_le_bytes(b.try_into().unwrap()));
                assert_eq!(got, m.front().copied(), "{at}");
            }
        }
        assert_eq!(r.len(), m.len(), "{at}");
        assert_eq!(r.is_full(), m.len() == cap, "{at}");
        assert_eq!(r.is_empty(), m.is_empty(), "{at}");
        let got: Vec<u32> = r.iter().map(|b| u32::from_le_bytes(b.try_into().unwrap())).collect();
        assert_eq!(got, m.iter().copied().collect::<Vec<_>>(), "order {at}");
        for j in 0..=m.len() {
            let got = r.get(j).map(|b| u32::from_le_bytes(b.try_into().unwrap()));
            assert_eq!(got, m.get(j).copied(), "get {j} {at}");
        }
    }
}

#[test]
fn empty_full_and_wrong_sizes() {
    let mut r = Ring::new(mem(8, true), 2, 4).unwrap();
    assert!(r.peek().is_none() && r.pop().is_none() && r.get(0).is_none());
    assert_eq!(r.push(&[1, 2, 3]), Err(Error::Length));
    assert_eq!(r.push(&[0; 5]), Err(Error::Length));
    assert!(r.is_empty());
    r.push(&[1; 4]).unwrap();
    r.push(&[2; 4]).unwrap();
    assert!(r.is_full());
    assert_eq!(r.push(&[3; 4]), Err(Error::Full));
    assert_eq!(r.pop(), Some(&[1u8; 4][..]));
    r.push(&[3; 4]).unwrap();
    assert_eq!(r.get(1), Some(&[3u8; 4][..]));
    r.clear();
    assert!(r.is_empty());
    assert_eq!(Ring::new(mem(7, true), 2, 4).unwrap_err(), Error::Storage { need: 8 });
    for owned in [true, false] {
        let mut z = Ring::new(mem(0, owned), 0, 4).unwrap();
        assert_eq!(z.push(&[0; 4]), Err(Error::Full));
        assert!(z.is_full() && z.is_empty());
        assert!(z.pop().is_none() && z.peek().is_none() && z.get(0).is_none());
        assert_eq!(z.iter().count(), 0);
    }
    // A size that saturates is a capacity, not a size to ask for.
    assert_eq!(Ring::new(mem(0, true), usize::MAX, 2).unwrap_err(), Error::Capacity);
}

#[test]
fn long_seeded_runs_match_a_vecdeque() {
    let mut x = 0x2545_f491_4f6c_dd1d_u64;
    let mut next = move || {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        x
    };
    for cap in [1usize, 2, 3, 7, 64] {
        let ops: Vec<(u8, u32)> = (0..5000).map(|_| (next() as u8, next() as u32)).collect();
        for spare in [0, 13] {
            run(&ops, cap, spare, cap % 2 == 1);
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(128))]
    #[test]
    fn any_run_matches_a_vecdeque(
        ops in proptest::collection::vec((any::<u8>(), any::<u32>()), 0..500),
        cap in 1usize..20,
        spare in 0usize..20,
        owned in any::<bool>(),
    ) {
        run(&ops, cap, spare, owned);
    }
}
