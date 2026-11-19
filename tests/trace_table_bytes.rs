//! Trace generation for the block sizes of the tables: the `bytes` of the array, the ring, the pool and the sorted
//! slab, what `new` answers to a block of each size, and what `Storage::zeroed` answers to a length, recorded as
//! ndjson (`table_bytes.ndjson`) for the TLA+ trace check (`TraceTableBytes.tla`).
//!
//! The cases are the boundary sets of `TableBytes.tla` at 64 bits (capacities and record sizes at the edges of
//! 2^j, and the tight ones that make the size land on 2^j) and 1,000 seeded random cases of each table. For each
//! case the blocks are the sizes around `bytes` (never one above 1 MiB + 1: a larger `bytes` is tried with a block
//! of 0 and of 64 bytes). The test recomputes `bytes` and the answer of `new` with `u128` arithmetic beside the code.
//! On a target of another pointer width the test does nothing; the model check covers 32 bits.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    clippy::needless_range_loop,
    clippy::too_many_arguments,
    unreachable_pub,
    clippy::len_zero,
    clippy::panic
)]

#[cfg(target_pointer_width = "64")]
mod at64 {
    use std::collections::BTreeSet;
    use std::fmt::Write as _;

    use pinc_table::{Array, Error, Pool, Ring, SortedSlab, Storage};
    use pinc_tests::{SplitMix64, soaking};

    const MIB: u128 = 1 << 20;
    const TWO64: u128 = 1 << 64;
    const KINDS: [&str; 4] = ["array", "ring", "pool", "slab"];

    /// A `u64` as the four 16-bit limbs `U64.tla` reads.
    fn limbs(v: u64) -> String {
        format!(
            "[{},{},{},{}]",
            v & 0xffff,
            (v >> 16) & 0xffff,
            (v >> 32) & 0xffff,
            v >> 48
        )
    }

    /// One table made with arguments: its kind (index into `KINDS`), capacity, record size (the slot size for a
    /// pool, 0 for a slab) and key and value lengths (slab only).
    #[derive(Clone, Copy)]
    struct Case {
        kind: usize,
        n: u64,
        r: u64,
        k: u64,
        v: u64,
    }

    /// What the cases reached, per kind.
    #[derive(Default, Clone, Copy)]
    struct Kind {
        ok: u32,
        storage: u32,
        capacity_by_need: u32,
        bytes_max: u32,
        capacity_alone: u32,
    }

    /// `bytes` of the table, from the code.
    fn bytes_of(c: Case) -> usize {
        let (n, r, k, v) = (c.n as usize, c.r as usize, c.k as usize, c.v as usize);
        match c.kind {
            0 => Array::bytes(n, r),
            1 => Ring::bytes(n, r),
            2 => Pool::<()>::bytes(n, r),
            _ => SortedSlab::bytes(n, k, v),
        }
    }

    /// `new` over `mem`: whether the table it made reports the capacity it was made with and is empty.
    fn make(c: Case, mem: Storage) -> Result<bool, Error> {
        let (n, r, k, v) = (c.n as usize, c.r as usize, c.k as usize, c.v as usize);
        match c.kind {
            0 => Array::new(mem, n, r).map(|t| t.places() == n && t.len() == 0 && t.is_empty()),
            1 => Ring::new(mem, n, r).map(|t| t.capacity() == n && t.len() == 0 && t.is_empty()),
            2 => Pool::<()>::new(mem, n, r)
                .map(|t| t.capacity() == n && t.free() == n && t.taken() == 0 && t.slot_size() == r),
            _ => SortedSlab::new(mem, n, k, v).map(|t| t.capacity() == n && t.len() == 0 && t.is_empty()),
        }
    }

    /// The exact need in `u128` (saturating, which stays above `isize::MAX`), and whether the table can number
    /// the capacity (and the slot size, and the key and value lengths).
    fn exact(c: Case) -> (u128, bool) {
        let (n, r, kv) = (u128::from(c.n), u128::from(c.r), u128::from(c.k) + u128::from(c.v));
        let (rec, ovh, numbers) = match c.kind {
            0 => (r, 3, n <= 65_535),
            1 => (r, 0, true),
            2 => (r, 12, n <= u128::from(u32::MAX) && r <= u128::from(u32::MAX)),
            _ => (
                kv,
                if n <= 65_535 { 2 } else { 4 },
                n <= u128::from(u32::MAX) && kv < TWO64,
            ),
        };
        (n.saturating_mul(rec + ovh), numbers)
    }

    /// The block lengths tried for a table whose `bytes` is `bytes`.
    fn lens(bytes: usize) -> Vec<usize> {
        if (bytes as u128) <= MIB {
            let mut l = vec![0];
            if bytes > 0 {
                l.push(bytes - 1);
            }
            l.extend([bytes, bytes + 1]);
            l
        } else {
            vec![0, 64]
        }
    }

    fn check(c: Case, out: &mut String, seen: &mut [Kind; 4], slab_kv: &mut u32) {
        let bytes = bytes_of(c);
        let (need, numbers) = exact(c);
        let want_bytes = if need < TWO64 { need as usize } else { usize::MAX };
        assert_eq!(
            bytes, want_bytes,
            "bytes of {} n={} r={} k={} v={}",
            KINDS[c.kind], c.n, c.r, c.k, c.v
        );
        let s = &mut seen[c.kind];
        s.bytes_max += u32::from(bytes == usize::MAX);
        for len in lens(bytes) {
            let got = make(c, Storage::zeroed(len).unwrap());
            let (res, shown) = match got {
                Ok(well_formed) => {
                    assert!(
                        well_formed,
                        "an accepted table is not empty with the capacity it was made with"
                    );
                    ("ok", 0)
                }
                Err(Error::Capacity) => ("capacity", 0),
                Err(Error::Storage { need }) => ("storage", need as u64),
                Err(e) => panic!("new refused with {e:?}"),
            };
            let want = if !numbers || need > isize::MAX as u128 {
                Err(Error::Capacity)
            } else if (len as u128) < need {
                Err(Error::Storage { need: need as usize })
            } else {
                Ok(true)
            };
            assert_eq!(
                got, want,
                "new of {} n={} r={} k={} v={} len={len}",
                KINDS[c.kind], c.n, c.r, c.k, c.v
            );
            match got {
                Ok(_) => s.ok += 1,
                Err(Error::Storage { .. }) => s.storage += 1,
                _ => {
                    s.capacity_by_need += u32::from(numbers);
                    s.capacity_alone += u32::from(!numbers && need <= isize::MAX as u128);
                    *slab_kv += u32::from(c.kind == 3 && u128::from(c.k) + u128::from(c.v) >= TWO64);
                }
            }
            let _ = writeln!(
                out,
                r#"{{"t":"tbytes","kind":"{}","n":{},"r":{},"k":{},"v":{},"bytes":{},"len":{},"res":"{res}","need":{}}}"#,
                KINDS[c.kind],
                limbs(c.n),
                limbs(c.r),
                limbs(c.k),
                limbs(c.v),
                limbs(bytes as u64),
                limbs(len as u64),
                limbs(shown),
            );
        }
    }

    /// `2^j - 1`, `2^j` and `2^j + 1` for each `j`, those below 2^64.
    fn edges(js: &[u32]) -> BTreeSet<u128> {
        js.iter()
            .flat_map(|&j| [(1u128 << j) - 1, 1 << j, (1 << j) + 1])
            .filter(|&x| x < TWO64)
            .collect()
    }

    pub fn all() {
        let mut rng = SplitMix64::traced(0x6279_7465);
        let mut out = String::new();
        let mut seen = [Kind::default(); 4];
        let mut slab_kv = 0u32;
        let caps = edges(&[0, 1, 2, 15, 16, 17, 30, 31, 32, 33, 62, 63, 64]);
        let rec_edges = edges(&[0, 1, 4, 16, 31, 32, 63, 64]);
        for (kind, ovh) in [(0usize, 3u128), (1, 0), (2, 12)] {
            let mut recs = rec_edges.clone();
            recs.extend(
                [4u32, 29, 30, 31, 60, 61, 62, 63, 64]
                    .map(|j| (1u128 << j) - ovh)
                    .into_iter()
                    .filter(|&x| x < TWO64),
            );
            for &n in &caps {
                for &r in &recs {
                    let c = Case {
                        kind,
                        n: n as u64,
                        r: r as u64,
                        k: 0,
                        v: 0,
                    };
                    check(c, &mut out, &mut seen, &mut slab_kv);
                }
            }
        }
        let mut kvs: BTreeSet<(u128, u128)> = BTreeSet::new();
        let lengths = [0u128, 1, 4, 1 << 31, (1 << 32) - 1, (1 << 63) - 1, 1 << 63, TWO64 - 1];
        for &k in &lengths {
            for &v in &lengths {
                kvs.insert((k, v));
            }
        }
        for j in [4u32, 29, 30, 31, 60, 61, 62, 63] {
            for w in [2u128, 4] {
                kvs.insert(((1 << j) - w, 0));
            }
        }
        for &n in &caps {
            for &(k, v) in &kvs {
                let c = Case {
                    kind: 3,
                    n: n as u64,
                    r: 0,
                    k: k as u64,
                    v: v as u64,
                };
                check(c, &mut out, &mut seen, &mut slab_kv);
            }
        }
        // random cases, each of the four tables in turn
        for _ in 0..1000 {
            for kind in 0..4 {
                let s = rng.next_u64() % 64;
                let n = rng.next_u64() >> s;
                let draw = |rng: &mut SplitMix64| {
                    let t = rng.next_u64() % 64;
                    rng.next_u64() >> t
                };
                let c = if kind == 3 {
                    let (k, v) = (draw(&mut rng), draw(&mut rng));
                    Case { kind, n, r: 0, k, v }
                } else {
                    Case {
                        kind,
                        n,
                        r: draw(&mut rng),
                        k: 0,
                        v: 0,
                    }
                };
                check(c, &mut out, &mut seen, &mut slab_kv);
            }
        }
        // Storage::zeroed: past isize::MAX is refused with nothing allocated, a short length is made
        for len in [
            isize::MAX as usize + 1,
            isize::MAX as usize + 2,
            usize::MAX - 1,
            usize::MAX,
            0,
            1,
            4096,
        ] {
            let got = Storage::zeroed(len);
            let refused = len > isize::MAX as usize;
            let res = match &got {
                Ok(m) => {
                    assert_eq!(m.len(), len);
                    "ok"
                }
                Err(Error::Capacity) => "capacity",
                Err(e) => panic!("zeroed refused with {e:?}"),
            };
            assert_eq!(got.is_err(), refused, "zeroed({len})");
            let _ = writeln!(out, r#"{{"t":"tzero","len":{},"res":"{res}"}}"#, limbs(len as u64));
        }
        if !soaking() {
            for (name, s) in KINDS.iter().zip(&seen) {
                assert!(s.ok > 0, "no {name} was made");
                assert!(s.storage > 0, "no {name} was refused a block too small");
                assert!(
                    s.capacity_by_need > 0,
                    "no {name} was refused for a need above isize::MAX with a capacity it can number"
                );
                assert!(s.bytes_max > 0, "no {name} had a bytes of usize::MAX");
            }
            for kind in [0, 2, 3] {
                assert!(
                    seen[kind].capacity_alone > 0,
                    "no {} was refused for its capacity alone",
                    KINDS[kind]
                );
            }
            assert!(slab_kv > 0, "no slab was refused for a key and value past usize::MAX");
        }
        if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
            std::fs::create_dir_all(&dir).unwrap();
            std::fs::write(std::path::Path::new(&dir).join("table_bytes.ndjson"), &out).unwrap();
        }
    }
}

#[test]
fn the_block_sizes_match_the_model() {
    #[cfg(target_pointer_width = "64")]
    at64::all();
}
