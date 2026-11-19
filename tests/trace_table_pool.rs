//! Trace generation for the slot pool: seeded runs of a real `Pool` (`pinc-table`, built with the `trace`
//! feature), recorded as ndjson (`table_pool.ndjson`) for the TLA+ trace check (`TraceTablePool.tla`).
//!
//! A run makes a pool of 0, 1, 2, 5 or 32 slots of 0 to 8 bytes and drives it with takes (to the exhausted pool and
//! past it), give-backs of held, given-back and forged handles, writes of 0 bytes, a prefix, the whole slot and one
//! byte too many, and reads of every kind of handle. After every call the pool shows its free stack, every slot's
//! generation and every slot's written length.
//!
//! The test compares every call with a reference (the generation, the bytes and the written length of each slot and
//! the free stack), checks every slot is either out or on the stack, and that a refused call and a read change
//! nothing.
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
    clippy::cast_possible_wrap,
    clippy::expect_used,
    clippy::panic,
    clippy::single_match_else
)]

use std::fmt::Write as _;

use pinc_table::{Error, Pool, Slot, Storage};
use pinc_tests::{SplitMix64, soaking};

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    exhausted: u32,
    take_none: u32,
    second_give: u32,
    forged_give: u32,
    forged_write: u32,
    forged_read: u32,
    write_length: u32,
    write_zero: u32,
    shorter_after_longer: u32,
    retaken: u32,
}

/// A value below `n` (`n > 0`).
fn below(rng: &mut SplitMix64, n: u64) -> u64 {
    rng.next_u64() % n
}

/// The handle of slot `idx` in generation `gn`, as any bytes make one.
fn handle(idx: usize, gn: u32) -> Slot {
    let mut b = [0u8; 8];
    b[..4].copy_from_slice(&(idx as u32).to_le_bytes());
    b[4..].copy_from_slice(&gn.to_le_bytes());
    Slot::from_bytes(b)
}

fn json_bytes(bytes: &[u8]) -> String {
    let body: Vec<String> = bytes.iter().map(u8::to_string).collect();
    format!("[{}]", body.join(","))
}

/// A handle the test took, and whether it gave it back.
#[derive(Clone, Copy)]
struct Hd {
    idx: usize,
    gn: u32,
    given: bool,
}

/// A pool beside its reference and its record.
struct Rig<'a> {
    p: Pool,
    n: usize,
    z: usize,
    gn: Vec<u32>,
    out: Vec<bool>,
    bytes: Vec<Vec<u8>>,
    written: Vec<usize>,
    stack: Vec<usize>,
    hs: Vec<Hd>,
    sink: &'a mut String,
    run: u32,
    last: String,
}

impl Rig<'_> {
    /// Whether the reference accepts the handle.
    fn live(&self, idx: usize, gn: u32) -> bool {
        gn & 1 == 1 && idx < self.n && self.gn[idx] == gn
    }

    /// Checks the pool against the reference and returns the view the models read.
    fn view(&self, seen: &mut Seen) -> String {
        let p = &self.p;
        assert_eq!((p.capacity(), p.slot_size()), (self.n, self.z));
        assert_eq!(p.free(), self.stack.len(), "free");
        assert_eq!(
            p.free() + p.taken(),
            p.capacity(),
            "free and taken are not the capacity"
        );
        assert_eq!(p.taken(), self.out.iter().filter(|&&o| o).count(), "taken");
        let stack: Vec<usize> = (0..p.free()).map(|k| p.trace_stack(k).unwrap()).collect();
        assert_eq!(p.trace_stack(p.free()), None);
        assert_eq!(stack, self.stack, "the free stack");
        let mut on_stack = vec![false; self.n];
        for &s in &stack {
            assert!(!on_stack[s], "slot {s} is on the stack twice");
            on_stack[s] = true;
        }
        for i in 0..self.n {
            let g = p.trace_generation(i).unwrap();
            assert_eq!(g, self.gn[i], "generation of {i}");
            assert!(g < i32::MAX as u32, "a generation reached 2^31 - 1");
            assert_eq!(g & 1 == 1, self.out[i], "slot {i} out and its generation disagree");
            assert_eq!(
                on_stack[i], !self.out[i],
                "slot {i} is out or on the stack, not both or neither"
            );
            assert_eq!(p.trace_written(i).unwrap(), self.written[i], "written length of {i}");
            let want = self.out[i].then(|| &self.bytes[i][..self.written[i]]);
            assert_eq!(p.read(handle(i, g)), want, "read of the current handle of {i}");
        }
        assert_eq!(p.trace_generation(self.n), None);
        assert_eq!(p.trace_written(self.n), None);
        seen.exhausted += u32::from(self.n > 0 && p.free() == 0);
        let st: Vec<String> = stack.iter().map(usize::to_string).collect();
        let gn: Vec<String> = self.gn.iter().map(u32::to_string).collect();
        let wr: Vec<String> = self.written.iter().map(usize::to_string).collect();
        format!(
            r#"{{"free":{},"stack":[{}],"gen":[{}],"written":[{}]}}"#,
            p.free(),
            st.join(","),
            gn.join(","),
            wr.join(",")
        )
    }

    /// Records the event, and checks a call that must change nothing left the view as it was.
    fn emit(&mut self, head: &str, unchanged: bool, v: String) {
        if unchanged {
            assert_eq!(v, self.last, "a refused call changed the pool");
        }
        let _ = writeln!(self.sink, r#"{{"t":"tpool","run":{},{head},"v":{v}}}"#, self.run);
        self.last = v;
    }

    /// A take; whether it handed a slot out.
    fn take(&mut self, seen: &mut Seen) -> bool {
        let got = self.p.take();
        let (res, idx, gn) = if let Some(s) = got {
            let top = self.stack.pop().expect("a slot was handed out of an empty stack");
            let gn = u32::from_le_bytes(<[u8; 4]>::try_from(&s.to_bytes()[4..8]).unwrap());
            assert_eq!(s.index(), top, "take did not hand out the top of the stack");
            assert!(!self.out[top]);
            assert_eq!(gn, self.gn[top] + 1, "the generation is not the old one plus one");
            assert_eq!(gn & 1, 1);
            self.gn[top] = gn;
            self.out[top] = true;
            self.written[top] = 0;
            self.hs.push(Hd {
                idx: top,
                gn,
                given: false,
            });
            if gn >= 3 {
                assert_eq!(self.p.read(handle(top, gn - 2)), None, "an old handle reads");
                seen.retaken += 1;
            }
            ("ok", top as i64, i64::from(gn))
        } else {
            assert!(
                self.stack.is_empty() && self.out.iter().all(|&o| o),
                "take is None with a slot free"
            );
            seen.take_none += 1;
            ("none", -1, -1)
        };
        let v = self.view(seen);
        self.emit(
            &format!(r#""op":"take","res":"{res}","idx":{idx},"gen":{gn}"#),
            got.is_none(),
            v,
        );
        got.is_some()
    }

    fn give(&mut self, seen: &mut Seen, idx: usize, gn: u32, forged: bool, second: bool) {
        let live = self.live(idx, gn);
        let got = self.p.give(handle(idx, gn));
        let res = match got {
            Ok(()) => "ok",
            Err(Error::Stale) => "stale",
            Err(e) => panic!("give refused with {e:?}"),
        };
        assert_eq!(got.is_ok(), live, "give({idx}, {gn})");
        if live {
            self.gn[idx] += 1;
            self.out[idx] = false;
            self.stack.push(idx);
            if let Some(h) = self.hs.iter_mut().find(|h| h.idx == idx && h.gn == gn) {
                h.given = true;
            }
        }
        seen.forged_give += u32::from(forged && !live);
        seen.second_give += u32::from(second && !live);
        let v = self.view(seen);
        self.emit(
            &format!(r#""op":"give","idx":{idx},"gen":{gn},"res":"{res}""#),
            !live,
            v,
        );
    }

    fn write(&mut self, seen: &mut Seen, idx: usize, gn: u32, data: &[u8], forged: bool) {
        let live = self.live(idx, gn);
        let before = if live { self.written[idx] } else { 0 };
        let want = if !live {
            Err(Error::Stale)
        } else if data.len() > self.z {
            Err(Error::Length)
        } else {
            Ok(())
        };
        let got = self.p.write(handle(idx, gn), data);
        assert_eq!(got, want, "write({idx}, {gn})");
        let res = match got {
            Ok(()) => "ok",
            Err(Error::Stale) => "stale",
            Err(Error::Length) => "length",
            Err(e) => panic!("write refused with {e:?}"),
        };
        seen.forged_write += u32::from(forged && !live);
        seen.write_length += u32::from(got == Err(Error::Length));
        if got.is_ok() {
            self.bytes[idx][..data.len()].copy_from_slice(data);
            self.written[idx] = before.max(data.len());
            seen.write_zero += u32::from(data.is_empty());
            seen.shorter_after_longer += u32::from(data.len() < before);
        }
        let v = self.view(seen);
        self.emit(
            &format!(
                r#""op":"write","idx":{idx},"gen":{gn},"data":{},"res":"{res}""#,
                json_bytes(data)
            ),
            got.is_err(),
            v,
        );
    }

    fn read(&mut self, seen: &mut Seen, idx: usize, gn: u32, forged: bool) {
        let live = self.live(idx, gn);
        let want = live.then(|| self.bytes[idx][..self.written[idx]].to_vec());
        let got = self.p.read(handle(idx, gn)).map(<[u8]>::to_vec);
        assert_eq!(got, want, "read({idx}, {gn})");
        seen.forged_read += u32::from(forged && !live);
        let v = self.view(seen);
        let data = got.as_deref().map_or_else(|| "[]".to_owned(), json_bytes);
        self.emit(
            &format!(
                r#""op":"read","idx":{idx},"gen":{gn},"ok":{},"data":{data}"#,
                got.is_some()
            ),
            true,
            v,
        );
    }

    /// A handle the test took and still holds (`given` false) or gave back (`given` true), at random.
    fn pick(&self, rng: &mut SplitMix64, given: bool) -> Option<Hd> {
        let of: Vec<Hd> = self.hs.iter().copied().filter(|h| h.given == given).collect();
        (!of.is_empty()).then(|| of[below(rng, of.len() as u64) as usize])
    }

    /// A forged handle: a taken index with an even generation or the generation plus 2, or an index past the
    /// capacity.
    fn forged(&self, rng: &mut SplitMix64) -> (usize, u32) {
        let out = |rng: &mut SplitMix64| {
            let idx = [self.n, self.n + 1, i32::MAX as usize][below(rng, 3) as usize];
            (idx, 1)
        };
        if self.hs.is_empty() {
            return out(rng);
        }
        let h = self.hs[below(rng, self.hs.len() as u64) as usize];
        match below(rng, 3) {
            0 => (h.idx, h.gn + 1),
            1 => (h.idx, h.gn + 2),
            _ => out(rng),
        }
    }
}

fn run(rng: &mut SplitMix64, sink: &mut String, id: u32, n: usize, z: usize, calls: u32, seen: &mut Seen) {
    let p = Pool::<()>::new(Storage::zeroed(Pool::<()>::bytes(n, z)).unwrap(), n, z).unwrap();
    let mut g = Rig {
        p,
        n,
        z,
        gn: vec![0; n],
        out: vec![false; n],
        bytes: vec![vec![0; z]; n],
        written: vec![0; n],
        stack: (0..n).rev().collect(),
        hs: Vec::new(),
        sink,
        run: id,
        last: String::new(),
    };
    let v = g.view(seen);
    g.emit(&format!(r#""op":"init","n":{n},"z":{z}"#), false, v);
    let data = |rng: &mut SplitMix64, len: usize| -> Vec<u8> { (0..len).map(|_| rng.next_u64() as u8).collect() };
    for _ in 0..calls {
        match below(rng, 24) {
            0..=5 => {
                g.take(seen);
            }
            6..=9 => match g.pick(rng, false) {
                Some(h) => g.give(seen, h.idx, h.gn, false, false),
                None => {
                    g.take(seen);
                }
            },
            10 => match g.pick(rng, true) {
                Some(h) => g.give(seen, h.idx, h.gn, false, true),
                None => {
                    g.take(seen);
                }
            },
            11 => {
                let (idx, gn) = g.forged(rng);
                g.give(seen, idx, gn, true, false);
            }
            12..=15 => {
                let held_first = below(rng, 4) < 3;
                let h = g.pick(rng, !held_first).or_else(|| g.pick(rng, held_first));
                if let Some(h) = h {
                    let len = [0, 1, z / 2, z, z + 1][below(rng, 5) as usize];
                    let d = data(rng, len);
                    g.write(seen, h.idx, h.gn, &d, false);
                } else {
                    g.take(seen);
                }
            }
            16 => {
                let (idx, gn) = g.forged(rng);
                let d = data(rng, 1);
                g.write(seen, idx, gn, &d, true);
            }
            17..=21 => {
                let class = match below(rng, 5) {
                    0..=2 => Some(false),
                    3 => Some(true),
                    _ => None,
                };
                match class.and_then(|c| g.pick(rng, c)) {
                    Some(h) => g.read(seen, h.idx, h.gn, false),
                    None => {
                        let (idx, gn) = g.forged(rng);
                        g.read(seen, idx, gn, true);
                    }
                }
            }
            22 => while g.take(seen) {},
            _ => {
                let mut held: Vec<Hd> = g.hs.iter().copied().filter(|h| !h.given).collect();
                for i in (1..held.len()).rev() {
                    held.swap(i, below(rng, i as u64 + 1) as usize);
                }
                for h in held {
                    g.give(seen, h.idx, h.gn, false, false);
                }
            }
        }
    }
}

#[test]
fn the_pool_matches_the_model() {
    let mut rng = SplitMix64::traced(0x706f_6f6c);
    let mut out = String::new();
    let mut seen = Seen::default();
    let mut id = 1u32;
    for (n, z, runs, calls) in [
        (0, 0, 2, 20),
        (0, 4, 2, 20),
        (1, 0, 4, 60),
        (1, 3, 6, 100),
        (2, 1, 6, 150),
        (5, 4, 8, 300),
        (32, 8, 4, 1000),
    ] {
        for _ in 0..runs {
            run(&mut rng, &mut out, id, n, z, calls, &mut seen);
            id += 1;
        }
    }
    if !soaking() {
        assert!(seen.exhausted > 0, "no pool was exhausted");
        assert!(seen.take_none > 0, "no take of an exhausted pool");
        assert!(seen.second_give > 0, "no second give-back was refused");
        assert!(
            seen.forged_give > 0 && seen.forged_write > 0 && seen.forged_read > 0,
            "a forged handle was not refused by each of give, write and read"
        );
        assert!(seen.write_length > 0, "no write of too many bytes");
        assert!(seen.write_zero > 0, "no write of 0 bytes");
        assert!(seen.shorter_after_longer > 0, "no shorter write after a longer one");
        assert!(seen.retaken > 0, "no slot was taken again after a give-back");
    }
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("table_pool.ndjson"), &out).unwrap();
    }
}
