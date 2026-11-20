//! Trace generation for the array by position: seeded runs of a real `Array` (`pinc-table`), recorded as ndjson
//! (`table_array.ndjson`) for the TLA+ trace check (`TraceTableArray.tla`).
//!
//! A run makes an array of 0, 1, 2, 3, 7 or 64 places of 2-byte records, sets every place once in a shuffled order,
//! and then drives it with random sets (present and absent places, places past the end, records of the wrong
//! length), removals (also past the end) and key vectors for `set_order` (many equal keys, distinct keys, a slice of
//! the wrong length). After every call the array shows its length, every place, its order and its walk.
//!
//! The test compares every call with a reference (a vector of the places and the last key vector accepted, sorted
//! with a stable sort) and checks that a refused call changes nothing.
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
    clippy::panic
)]

use std::fmt::Write as _;

use pinc_table::{Array, Error, Storage};
use pinc_tests::{SplitMix64, soaking, trace_cases};

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    full: u32,
    set_present: u32,
    position: u32,
    length: u32,
    remove_true: u32,
    remove_false: u32,
    order_length: u32,
    order_moved: u32,
}

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn val(record: &[u8]) -> u16 {
    u16::from_be_bytes(<[u8; 2]>::try_from(record).unwrap())
}

/// An array beside its reference and its record.
struct Rig<'a> {
    a: Array,
    places: usize,
    held: Vec<Option<u16>>,
    keys: Option<Vec<u32>>,
    out: &'a mut String,
    run: u32,
    last: String,
}

impl Rig<'_> {
    /// The positions in the order the reference expects.
    fn want_order(&self) -> Vec<usize> {
        let mut o: Vec<usize> = (0..self.places).collect();
        if let Some(k) = &self.keys {
            o.sort_by_key(|&p| k[p]);
        }
        o
    }

    /// Checks the array against the reference and returns the view the models read.
    fn view(&self, seen: &mut Seen) -> String {
        let a = &self.a;
        assert_eq!(a.places(), self.places);
        assert_eq!(
            a.len(),
            self.held.iter().flatten().count(),
            "len is not the places present"
        );
        let mut get = Vec::new();
        for pos in 0..self.places + 2 {
            let want = self.held.get(pos).copied().flatten().map(u16::to_be_bytes);
            assert_eq!(a.get(pos), want.as_ref().map(<[u8; 2]>::as_slice), "get({pos})");
            if pos < self.places {
                get.push(want.map_or_else(|| "[]".to_owned(), |_| format!("[{}]", self.held[pos].unwrap())));
            }
        }
        let order: Vec<usize> = a.order().collect();
        assert_eq!(order, self.want_order(), "order");
        let mut sorted = order.clone();
        sorted.sort_unstable();
        assert!(sorted.iter().copied().eq(0..self.places), "order is not a permutation");
        let want_iter: Vec<(usize, u16)> = order.iter().filter_map(|&p| self.held[p].map(|x| (p, x))).collect();
        let got_iter: Vec<(usize, u16)> = a.iter().map(|(p, r)| (p, val(r))).collect();
        assert_eq!(got_iter, want_iter, "iter");
        seen.full += u32::from(self.places >= 1 && a.len() == self.places);
        let order_s: Vec<String> = order.iter().map(usize::to_string).collect();
        let iter_s: Vec<String> = got_iter.iter().map(|(p, x)| format!("[{p},{x}]")).collect();
        format!(
            r#"{{"len":{},"get":[{}],"order":[{}],"iter":[{}]}}"#,
            a.len(),
            get.join(","),
            order_s.join(","),
            iter_s.join(",")
        )
    }

    /// Records the event, and checks a call that must change nothing left the view as it was.
    fn emit(&mut self, head: &str, unchanged: bool, v: String) {
        if unchanged {
            assert_eq!(v, self.last, "a refused call changed the array");
        }
        let _ = writeln!(self.out, r#"{{"t":"tarr","run":{},{head},"v":{v}}}"#, self.run);
        self.last = v;
    }

    fn set(&mut self, seen: &mut Seen, pos: usize, record: &[u8], value: u16) {
        let good = record.len() == 2;
        let want = if pos >= self.places {
            Err(Error::Position)
        } else if !good {
            Err(Error::Length)
        } else {
            Ok(self.held[pos].is_some())
        };
        let got = self.a.set(pos, record);
        assert_eq!(got, want, "set({pos})");
        let res = match got {
            Ok(true) => "true",
            Ok(false) => "false",
            Err(Error::Position) => "position",
            Err(Error::Length) => "length",
            Err(e) => panic!("set refused with {e:?}"),
        };
        seen.set_present += u32::from(got == Ok(true));
        seen.position += u32::from(got == Err(Error::Position));
        seen.length += u32::from(got == Err(Error::Length));
        if got.is_ok() {
            self.held[pos] = Some(value);
        }
        let v = self.view(seen);
        let value = if good { value } else { 0 };
        self.emit(
            &format!(r#""op":"set","pos":{pos},"good":{good},"val":{value},"res":"{res}""#),
            got.is_err(),
            v,
        );
    }

    fn remove(&mut self, seen: &mut Seen, pos: usize) {
        let want = self.held.get(pos).copied().flatten().is_some();
        let got = self.a.remove(pos);
        assert_eq!(got, want, "remove({pos})");
        seen.remove_true += u32::from(got);
        seen.remove_false += u32::from(!got);
        if got {
            self.held[pos] = None;
        }
        let v = self.view(seen);
        self.emit(&format!(r#""op":"remove","pos":{pos},"res":"{got}""#), !got, v);
    }

    fn order(&mut self, seen: &mut Seen, keys: &[u32]) {
        let want = keys.len() == self.places;
        let got = self.a.set_order(keys);
        let res = match got {
            Ok(()) => "ok",
            Err(Error::Length) => "length",
            Err(e) => panic!("set_order refused with {e:?}"),
        };
        assert_eq!(got.is_ok(), want, "set_order of {} keys", keys.len());
        seen.order_length += u32::from(!want);
        if want {
            self.keys = Some(keys.to_vec());
        }
        let v = self.view(seen);
        seen.order_moved += u32::from(want && self.a.order().ne(0..self.places));
        let ks: Vec<String> = keys.iter().map(u32::to_string).collect();
        self.emit(
            &format!(r#""op":"order","keys":[{}],"res":"{res}""#, ks.join(",")),
            !want,
            v,
        );
    }
}

/// A place past the end: `places`, `places + 1` or `places + 1000`.
fn past(rng: &mut SplitMix64, places: usize) -> usize {
    places + [0, 1, 1000][below(rng, 3) as usize]
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, places: usize, calls: u32, seen: &mut Seen) {
    let a = Array::new(Storage::zeroed(Array::bytes(places, 2)).unwrap(), places, 2).unwrap();
    let mut r = Rig {
        a,
        places,
        held: vec![None; places],
        keys: None,
        out,
        run: id,
        last: String::new(),
    };
    let v = r.view(seen);
    r.emit(&format!(r#""op":"init","places":{places}"#), false, v);
    let value = |rng: &mut SplitMix64| (rng.next_u64() & 0xffff) as u16;
    // fill: every place once, in a random order
    let mut order: Vec<usize> = (0..places).collect();
    for i in (1..places).rev() {
        order.swap(i, below(rng, i as u64 + 1) as usize);
    }
    for &pos in &order {
        let x = value(rng);
        r.set(seen, pos, &x.to_be_bytes(), x);
    }
    for _ in 0..calls {
        let in_range = |rng: &mut SplitMix64| {
            if places == 0 {
                past(rng, 0)
            } else {
                below(rng, places as u64) as usize
            }
        };
        match below(rng, 20) {
            0..=6 => {
                let (pos, x) = (in_range(rng), value(rng));
                r.set(seen, pos, &x.to_be_bytes(), x);
            }
            7 => {
                let (pos, x) = (past(rng, places), value(rng));
                r.set(seen, pos, &x.to_be_bytes(), x);
            }
            8 => {
                let pos = in_range(rng);
                let n = if below(rng, 2) == 0 { 1 } else { 3 };
                let record = vec![value(rng) as u8; n];
                r.set(seen, pos, &record, 0);
            }
            9..=13 => {
                let pos = in_range(rng);
                r.remove(seen, pos);
            }
            14 => {
                let pos = past(rng, places);
                r.remove(seen, pos);
            }
            15..=17 => {
                let keys: Vec<u32> = (0..places).map(|_| below(rng, 4) as u32).collect();
                r.order(seen, &keys);
            }
            18 => {
                let keys: Vec<u32> = (0..places).map(|_| below(rng, 1 << 31) as u32).collect();
                r.order(seen, &keys);
            }
            _ => {
                let n = if places == 0 || below(rng, 2) == 0 {
                    places + 1
                } else {
                    places - 1
                };
                r.order(seen, &vec![0; n]);
            }
        }
    }
}

#[test]
fn the_array_matches_the_model() {
    let mut rng = SplitMix64::traced(0x7461_7272);
    let mut out = String::new();
    let mut seen = Seen::default();
    let mut id = 1u32;
    for (places, quick, runs, calls) in [
        (0, 1, 4, 20),
        (1, 2, 8, 60),
        (2, 2, 8, 80),
        (3, 3, 12, 120),
        (7, 3, 12, 150),
        (64, 1, 6, 400),
    ] {
        for _ in 0..trace_cases(quick, runs) {
            run(&mut rng, &mut out, id, places, calls, &mut seen);
            id += 1;
        }
    }
    if !soaking() {
        assert!(seen.full > 0, "no array was full");
        assert!(seen.set_present > 0, "no set of a present place");
        assert!(seen.position > 0, "no set past the end");
        assert!(seen.length > 0, "no record of the wrong length");
        assert!(
            seen.remove_true > 0 && seen.remove_false > 0,
            "removals did not both succeed and fail"
        );
        assert!(seen.order_length > 0, "no key slice of the wrong length");
        assert!(seen.order_moved > 0, "no key vector changed the order");
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("table_array.ndjson"), &out).unwrap();
    }
}
