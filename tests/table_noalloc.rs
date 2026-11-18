//! The fixed tables allocate nothing once they are made: a long mixed run on each shape, over a caller's block and
//! over the zeroed block a table makes itself, touches the heap zero times.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::hint::black_box;
use vinc_table::{Array, Pool, Ring, Slot, SortedSlab, Storage};

use vinc_tests::measure;

vinc_tests::install_counting_allocator!();

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

fn blocks(n: usize) -> [Storage; 2] {
    [
        Storage::zeroed(n).unwrap(),
        Storage::from_static(Box::leak(vec![0u8; n].into_boxed_slice())),
    ]
}

#[test]
fn the_slab_allocates_nothing_after_it_is_made() {
    // A capacity on each side of the boundary between the 2-byte and the 4-byte index.
    for cap in [256usize, 65_536] {
        for mem in blocks(SortedSlab::bytes(cap, 8, 8)) {
            let mut s = SortedSlab::new(mem, cap, 8, 8).unwrap();
            let mut r = Rng(7);
            let st = measure(|| {
                for _ in 0..20_000 {
                    let k = (r.next() % 300).to_be_bytes();
                    match r.next() % 9 {
                        0 | 1 => {
                            let _ = black_box(s.insert(&k, &k));
                        }
                        2 => {
                            let _ = black_box(s.remove(&k));
                        }
                        3 => {
                            let _ = black_box(s.first_at_or_after(&k).or_else(|| s.next_after(&k)).map(|e| e.0.len()));
                        }
                        4 => {
                            let mut cur = [0u8; 8];
                            while let Some((n, _)) = s.next_after(&cur) {
                                cur.copy_from_slice(n);
                                if cur[7].trailing_zeros() >= 2 {
                                    s.remove(&cur);
                                }
                            }
                            let _ = black_box(s.iter().count());
                        }
                        5 => {
                            let _ = black_box(s.get(&k).map(<[u8]>::len));
                            let _ = black_box(s.contains(&k));
                            if let Some(v) = s.get_mut(&k) {
                                v.fill(1);
                            }
                            let _ = black_box(s.entry(r.next() as usize % 300).map(|e| e.0.len()));
                            let _ = black_box(s.first().zip(s.last()).map(|(a, b)| a.0.len() + b.0.len()));
                        }
                        6 => {
                            let salt = r.next() as u8;
                            let _ = black_box(s.retain(|key, v| {
                                v.fill(2);
                                key[7] % 3 != salt % 3
                            }));
                        }
                        7 => {
                            let _ = black_box(s.insert(&k[..7], &k));
                            let _ = black_box(s.insert(&k, &k[..7]));
                        }
                        _ => {
                            if r.next().is_multiple_of(16) {
                                s.clear();
                            }
                        }
                    }
                }
            });
            assert_eq!(st.count(), 0, "SortedSlab of {cap} allocated {} times", st.count());
        }
    }
}

#[test]
fn the_ring_allocates_nothing_after_it_is_made() {
    for mem in blocks(Ring::bytes(64, 16)) {
        let mut ring = Ring::new(mem, 64, 16).unwrap();
        let mut r = Rng(11);
        let st = measure(|| {
            for _ in 0..50_000 {
                if r.next().is_multiple_of(2) {
                    let _ = black_box(ring.push(&[1; 16]));
                } else {
                    let _ = black_box(ring.pop().map(<[u8]>::len));
                }
                let _ = black_box(ring.peek().map(<[u8]>::len));
                let _ = black_box(ring.get(r.next() as usize % 70).map(<[u8]>::len));
                let _ = black_box(ring.push(&[1; 15]));
                if r.next().is_multiple_of(1000) {
                    ring.clear();
                }
            }
            let _ = black_box(ring.iter().count());
        });
        assert_eq!(st.count(), 0);
    }
}

#[test]
fn the_array_allocates_nothing_after_it_is_made() {
    for mem in blocks(Array::bytes(64, 8)) {
        let mut a = Array::new(mem, 64, 8).unwrap();
        let keys: [u32; 64] = core::array::from_fn(|i| (i as u32 * 37) % 64);
        let mut r = Rng(13);
        let st = measure(|| {
            let _ = black_box(a.set_order(&keys));
            for _ in 0..20_000 {
                let p = (r.next() % 70) as usize;
                match r.next() % 3 {
                    0 => {
                        let _ = black_box(a.set(p, &[3; 8]));
                    }
                    1 => {
                        let _ = black_box(a.remove(p));
                    }
                    _ => {
                        let _ = black_box(a.get(p).map(<[u8]>::len));
                        if let Some(v) = a.get_mut(p) {
                            v.fill(4);
                        }
                    }
                }
                let _ = black_box(a.set(p, &[3; 7]));
                let _ = black_box(a.order().count());
            }
            let _ = black_box(a.set_order(&keys[..3]));
            let _ = black_box(a.iter().count());
        });
        assert_eq!(st.count(), 0);
    }
}

#[test]
fn the_pool_allocates_nothing_after_it_is_made() {
    for mem in blocks(Pool::<()>::bytes(64, 32)) {
        let mut p: Pool = Pool::new(mem, 64, 32).unwrap();
        let mut held: [Option<Slot>; 64] = [None; 64];
        let mut r = Rng(17);
        let st = measure(|| {
            for _ in 0..50_000 {
                let i = (r.next() % 64) as usize;
                match held[i].take() {
                    Some(s) => {
                        let _ = black_box(p.read(s).map(<[u8]>::len));
                        let _ = black_box(p.give(s));
                        let _ = black_box(p.give(s));
                        let _ = black_box(p.read(Slot::from_bytes(s.to_bytes())).map(<[u8]>::len));
                    }
                    None => {
                        if let Some(s) = p.take() {
                            let _ = black_box(p.write(s, &[5; 32]));
                            let _ = black_box(p.write(s, &[5; 33]));
                            held[i] = Some(s);
                        }
                    }
                }
            }
        });
        assert_eq!(st.count(), 0);
    }
}
