//! Trace generation for the ring: seeded runs of a real `Ring` (`pinc-table`, built with the `trace` feature),
//! recorded as ndjson (`table_ring.ndjson`) for the TLA+ trace check (`TraceTableRing.tla`).
//!
//! A run makes a ring of 0, 1, 2, 3, 7 or 64 records of 2 bytes and drives it with pushes, pops, clears, records of
//! the wrong length and bursts to full (and one push past it), so that the head wraps around the block many times.
//! After every call the ring shows its head, its records, its oldest record and whether it is full.
//!
//! The test compares every call with a `VecDeque` reference bounded by the capacity, and checks that a refused push
//! and a pop of an empty ring change nothing.
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
    unreachable_pub,
    clippy::panic
)]

use std::collections::VecDeque;
use std::fmt::Write as _;

use pinc_table::{Error, Ring, Storage};
use pinc_tests::{SplitMix64, soaking};

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    wrapped_full: u32,
    full: u32,
    length: u32,
    pop_none: u32,
    clear_some: u32,
}

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

fn val(record: &[u8]) -> u16 {
    u16::from_be_bytes(<[u8; 2]>::try_from(record).unwrap())
}

/// A ring beside its reference and its record.
struct Rig<'a> {
    r: Ring,
    cap: usize,
    q: VecDeque<u16>,
    out: &'a mut String,
    run: u32,
    last: String,
}

impl Rig<'_> {
    /// Checks the ring against the reference and returns the view the models read.
    fn view(&self, seen: &mut Seen) -> String {
        let r = &self.r;
        assert_eq!(r.len(), self.q.len(), "len");
        assert!(r.len() <= self.cap, "the ring holds more than its capacity");
        assert_eq!(r.is_full(), self.q.len() == self.cap, "is_full");
        assert_eq!(r.is_empty(), self.q.is_empty());
        assert_eq!(r.capacity(), self.cap);
        let head = r.trace_head();
        if self.cap > 0 {
            assert!(head < self.cap, "the head is outside the block");
        } else {
            assert_eq!(head, 0);
        }
        for i in 0..r.len() + 2 {
            let want = self.q.get(i).copied().map(u16::to_be_bytes);
            assert_eq!(r.get(i), want.as_ref().map(<[u8; 2]>::as_slice), "get({i})");
        }
        let items: Vec<u16> = r.iter().map(val).collect();
        assert!(items.iter().eq(self.q.iter()), "iter");
        let peek = self.q.front().copied().map(u16::to_be_bytes);
        assert_eq!(r.peek(), peek.as_ref().map(<[u8; 2]>::as_slice), "peek");
        seen.wrapped_full += u32::from(r.is_full() && head > 0);
        let items_s: Vec<String> = items.iter().map(u16::to_string).collect();
        let peek_s = peek.map_or_else(String::new, |b| u16::from_be_bytes(b).to_string());
        format!(
            r#"{{"head":{head},"len":{},"items":[{}],"peek":[{peek_s}],"full":{}}}"#,
            r.len(),
            items_s.join(","),
            r.is_full()
        )
    }

    /// Records the event, and checks a call that must change nothing left the view as it was.
    fn emit(&mut self, head: &str, unchanged: bool, v: String) {
        if unchanged {
            assert_eq!(v, self.last, "a refused call changed the ring");
        }
        let _ = writeln!(self.out, r#"{{"t":"tring","run":{},{head},"v":{v}}}"#, self.run);
        self.last = v;
    }

    fn push(&mut self, seen: &mut Seen, record: &[u8], value: u16) {
        let good = record.len() == 2;
        let want = if !good {
            Err(Error::Length)
        } else if self.q.len() == self.cap {
            Err(Error::Full)
        } else {
            Ok(())
        };
        let got = self.r.push(record);
        assert_eq!(got, want, "push");
        let res = match got {
            Ok(()) => "ok",
            Err(Error::Full) => "full",
            Err(Error::Length) => "length",
            Err(e) => panic!("push refused with {e:?}"),
        };
        seen.full += u32::from(got == Err(Error::Full));
        seen.length += u32::from(got == Err(Error::Length));
        if got.is_ok() {
            self.q.push_back(value);
        }
        let v = self.view(seen);
        let value = if good { value } else { 0 };
        self.emit(
            &format!(r#""op":"push","good":{good},"val":{value},"res":"{res}""#),
            got.is_err(),
            v,
        );
    }

    fn pop(&mut self, seen: &mut Seen) {
        let want = self.q.pop_front();
        let got = self.r.pop().map(val);
        assert_eq!(got, want, "pop");
        seen.pop_none += u32::from(got.is_none());
        let v = self.view(seen);
        let (res, x) = got.map_or(("none", 0), |x| ("some", x));
        self.emit(&format!(r#""op":"pop","res":"{res}","val":{x}"#), got.is_none(), v);
    }

    fn clear(&mut self, seen: &mut Seen) {
        seen.clear_some += u32::from(!self.q.is_empty());
        self.r.clear();
        self.q.clear();
        let v = self.view(seen);
        self.emit(r#""op":"clear""#, false, v);
    }
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, cap: usize, calls: u32, seen: &mut Seen) {
    let r = Ring::new(Storage::zeroed(Ring::bytes(cap, 2)).unwrap(), cap, 2).unwrap();
    let mut g = Rig {
        r,
        cap,
        q: VecDeque::new(),
        out,
        run: id,
        last: String::new(),
    };
    let v = g.view(seen);
    g.emit(&format!(r#""op":"init","cap":{cap}"#), false, v);
    let value = |rng: &mut SplitMix64| (rng.next_u64() & 0xffff) as u16;
    for _ in 0..calls {
        match below(rng, 16) {
            0..=6 => {
                let x = value(rng);
                g.push(seen, &x.to_be_bytes(), x);
            }
            7 => {
                let n = if below(rng, 2) == 0 { 1 } else { 3 };
                let record = vec![value(rng) as u8; n];
                g.push(seen, &record, 0);
            }
            8..=13 => g.pop(seen),
            14 => g.clear(seen),
            _ => {
                while !g.r.is_full() {
                    let x = value(rng);
                    g.push(seen, &x.to_be_bytes(), x);
                }
                let x = value(rng);
                g.push(seen, &x.to_be_bytes(), x);
            }
        }
    }
}

#[test]
fn the_ring_matches_the_model() {
    let mut rng = SplitMix64::traced(0x7472_696e);
    let mut out = String::new();
    let mut seen = Seen::default();
    let mut id = 1u32;
    for (cap, runs, calls) in [
        (0, 4, 20),
        (1, 8, 80),
        (2, 8, 120),
        (3, 12, 200),
        (7, 12, 300),
        (64, 4, 1000),
    ] {
        for _ in 0..runs {
            run(&mut rng, &mut out, id, cap, calls, &mut seen);
            id += 1;
        }
    }
    if !soaking() {
        assert!(
            seen.wrapped_full > 0,
            "no full ring had its head past the start of the block"
        );
        assert!(seen.full > 0, "no push was refused as full");
        assert!(seen.length > 0, "no record of the wrong length");
        assert!(seen.pop_none > 0, "no pop of an empty ring");
        assert!(seen.clear_some > 0, "no clear of a non-empty ring");
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("table_ring.ndjson"), &out).unwrap();
    }
}
