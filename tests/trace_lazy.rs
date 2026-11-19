//! Trace generation for the lazy table (`pinc-transport`, built with the `trace` feature): real tables of 1, 5 and
//! 64 entries driven through `LazyProbe`, recorded as ndjson (`lazy.ndjson`) for the TLA+ trace check
//! (`TraceLazy.tla`).
//!
//! Each size has a boundary sequence (every refused call, the sweep of `get`, `clear`) and 20 tables of 60 seeded
//! calls. After every call the table shows its written prefix, the `N` entries `iter` reads and whether the room
//! reserved when it was made (capacity and address) is the same.
//!
//! The test compares every call with a naive array and a written length, so it is meaningful without the proof
//! tools. The trace is written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::stream::LazyProbe;

/// What the runs exercised: refused calls of each kind.
#[derive(Default)]
struct Seen {
    inits: u32,
    get_refused: u32,
    set_refused: u32,
    wset_refused: u32,
    pset_refused: u32,
}

/// One table, its naive model and the file it records to.
struct Run<'a, const N: usize> {
    t: LazyProbe<N>,
    vals: Vec<u32>,
    wlen: usize,
    out: &'a mut String,
    seen: &'a mut Seen,
}

impl<const N: usize> Run<'_, N> {
    /// The table after a call, as the model reads it; checks it against the naive one.
    fn view(&self) -> String {
        let (w, all) = (self.t.written(), self.t.all());
        assert_eq!(all, self.vals, "iter is not the N entries");
        assert_eq!(w, self.vals[..self.wlen], "written is not the written prefix");
        assert!(self.t.room_kept(), "the reserved room changed");
        let list = |v: &[u32]| v.iter().map(u32::to_string).collect::<Vec<_>>().join(",");
        format!(
            r#"{{"w":[{}],"all":[{}],"room":{}}}"#,
            list(&w),
            list(&all),
            self.t.room_kept()
        )
    }

    fn init(&mut self) {
        let v = self.view();
        self.seen.inits += 1;
        let _ = writeln!(self.out, r#"{{"t":"lazy","op":"init","n":{N},"blank":0,"v":{v}}}"#);
    }

    fn get(&mut self, i: usize) {
        let got = self.t.get(i);
        assert_eq!(got, self.vals.get(i).copied());
        self.seen.get_refused += u32::from(got.is_none());
        let v = self.view();
        let _ = writeln!(
            self.out,
            r#"{{"t":"lazy","op":"get","i":{i},"ok":{},"val":{},"v":{v}}}"#,
            got.is_some(),
            got.unwrap_or(0)
        );
    }

    fn set(&mut self, i: usize, val: u32) {
        let ok = self.t.set(i, val);
        assert_eq!(ok, i < N);
        if ok {
            self.vals[i] = val;
            self.wlen = self.wlen.max(i + 1);
        }
        self.seen.set_refused += u32::from(!ok);
        let v = self.view();
        let _ = writeln!(
            self.out,
            r#"{{"t":"lazy","op":"set","i":{i},"val":{val},"ok":{ok},"v":{v}}}"#
        );
    }

    fn wset(&mut self, i: usize, val: u32) {
        let ok = self.t.wset(i, val);
        assert_eq!(ok, i < self.wlen);
        if ok {
            self.vals[i] = val;
        }
        self.seen.wset_refused += u32::from(!ok);
        let v = self.view();
        let _ = writeln!(
            self.out,
            r#"{{"t":"lazy","op":"wset","i":{i},"val":{val},"ok":{ok},"v":{v}}}"#
        );
    }

    fn pset(&mut self, k: usize, val: u32) {
        let ok = self.t.pset(k, val);
        assert_eq!(ok, k <= self.wlen);
        if ok {
            self.vals[..k].fill(val);
        }
        self.seen.pset_refused += u32::from(!ok);
        let v = self.view();
        let _ = writeln!(
            self.out,
            r#"{{"t":"lazy","op":"pset","k":{k},"val":{val},"ok":{ok},"v":{v}}}"#
        );
    }

    fn clear(&mut self) {
        self.t.clear();
        self.vals.fill(0);
        self.wlen = 0;
        let v = self.view();
        let _ = writeln!(self.out, r#"{{"t":"lazy","op":"clear","v":{v}}}"#);
    }
}

fn table<const N: usize>(out: &mut String, seen: &mut Seen, rng: &mut SplitMix64, seeded: bool) {
    let mut r = Run::<N> {
        t: LazyProbe::new(),
        vals: vec![0; N],
        wlen: 0,
        out,
        seen,
    };
    r.init();
    if !seeded {
        let h = N / 2;
        r.get(0);
        r.get(N - 1);
        r.get(N);
        r.get(N + 3);
        r.wset(0, 7);
        r.pset(1, 7);
        r.set(N, 1);
        r.set(N + 5, 1);
        r.set(0, 1);
        r.set(N - 1, 2);
        for i in 0..=N {
            r.get(i);
        }
        r.wset(N - 1, 3);
        r.wset(N, 3);
        r.pset(0, 4);
        r.pset(N, 5);
        r.pset(N + 1, 6);
        r.clear();
        r.wset(0, 1);
        r.get(N - 1);
        r.set(h, 9);
        r.pset(h + 1, 8);
        r.pset(h + 2, 8);
        r.clear();
        return;
    }
    let mut below = |n: usize| (rng.next_u64() % n as u64) as usize;
    for _ in 0..60 {
        let op = below(20);
        let i = below(N + 2);
        let val = 1 + below(1000) as u32;
        match op {
            0..=5 => r.get(i),
            6..=10 => r.set(i, val),
            11..=14 => r.wset(i, val),
            15..=18 => r.pset(i, val),
            _ => r.clear(),
        }
    }
}

fn sized<const N: usize>(out: &mut String, seen: &mut Seen, rng: &mut SplitMix64) {
    table::<N>(out, seen, rng, false);
    for _ in 0..20 {
        table::<N>(out, seen, rng, true);
    }
}

#[test]
fn the_lazy_table_matches_the_model() {
    let mut rng = SplitMix64::traced(0x6c61_7a79);
    let (mut out, mut seen) = (String::new(), Seen::default());
    sized::<1>(&mut out, &mut seen, &mut rng);
    sized::<5>(&mut out, &mut seen, &mut rng);
    sized::<64>(&mut out, &mut seen, &mut rng);
    assert_eq!(seen.inits, 63, "three sizes of 21 tables");
    assert!(seen.get_refused > 0, "no get was refused");
    assert!(seen.set_refused > 0, "no set was refused");
    assert!(seen.wset_refused > 0, "no wset was refused");
    assert!(seen.pset_refused > 0, "no pset was refused");
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("lazy.ndjson"), &out).unwrap();
    }
}
