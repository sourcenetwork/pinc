//! Trace generation for the ring of extension frames held for the application: seeded runs of a real ring
//! (`vinc-core`, built with the `trace` feature), recorded as ndjson (`ext_in.ndjson`) for the TLA+ trace check
//! (`TraceExtIn.tla`) and the Lean replay (`Vinc/TraceExtIn.lean`).
//!
//! A run puts frames of a few sessions and types, with bodies of every length that matters (empty, short, exactly the
//! limit of 1200 bytes, one over it and well over it), takes them with buffers that are too small, just right and
//! large, and lets the ring fill, drop its oldest frame and wrap its head. A body is a run of one byte (its `tag`),
//! so the body read back is checked whole and the record carries its first byte. A put records whether the frame was
//! kept and how many frames the ring gave up for it. After every call the record shows the head, the length and the
//! frames held, oldest first.
//!
//! The test compares every call with a naive queue (a deque of whole bodies, written from the module's doc), and
//! checks the rules itself: a body over the limit is refused and changes nothing, a full ring drops its oldest
//! frame, keeps the new one and says it gave one up, frames leave in arrival order with their bodies intact, a frame
//! that does not fit the buffer stays held, the ring never holds more than its places.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::items_after_statements,
    clippy::cognitive_complexity,
    unreachable_pub
)]

use std::collections::VecDeque;
use std::fmt::Write as _;

use vinc_core::ExtInProbe;
use vinc_tests::SplitMix64;

const CAP: usize = ExtInProbe::SLOTS;
const MAX: usize = ExtInProbe::BODY_MAX;

/// A frame as the naive ring holds it: session, type, body.
type Frame = (u64, u64, Vec<u8>);

fn json_frame(session: u64, ty: u64, len: usize, tag: u8) -> String {
    format!("[{session},{ty},{len},{tag}]")
}

fn tag_of(body: &[u8]) -> u8 {
    body.first().copied().unwrap_or(0)
}

struct Naive {
    q: VecDeque<Frame>,
    head: usize,
}

impl Naive {
    /// `None` for a body over the limit, else how many frames the ring gave up for it.
    fn put(&mut self, f: Frame) -> Option<u64> {
        if f.2.len() > MAX {
            return None;
        }
        let full = self.q.len() == CAP;
        if full {
            self.q.pop_front();
            self.head = (self.head + 1) % CAP;
        }
        self.q.push_back(f);
        Some(u64::from(full))
    }
}

fn view(p: &ExtInProbe, nv: &Naive) -> String {
    assert_eq!(p.len(), nv.q.len());
    assert!(p.len() <= CAP, "the ring holds more than its places");
    assert_eq!(p.is_empty(), nv.q.is_empty());
    assert_eq!(p.head(), nv.head);
    let frames: Vec<String> = (0..p.len())
        .map(|k| {
            let (s, t, l, g) = p.frame(k).unwrap();
            json_frame(s, t, l, g)
        })
        .collect();
    format!(
        r#"{{"head":{},"len":{},"q":[{}]}}"#,
        p.head(),
        p.len(),
        frames.join(",")
    )
}

#[derive(Default)]
struct Seen {
    dropped_oldest: u32,
    refused: u32,
    refused_full: u32,
    at_limit: u32,
    wrapped: u32,
    stayed: u32,
    taken: u32,
    took_empty: u32,
    zero_len: u32,
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, steps: u32, seen: &mut Seen) {
    let mut p = ExtInProbe::new();
    let mut nv = Naive {
        q: VecDeque::new(),
        head: 0,
    };
    let _ = writeln!(
        out,
        r#"{{"t":"cox","run":{id},"op":"init","n":{CAP},"mx":{MAX},"v":{}}}"#,
        view(&p, &nv)
    );
    // the share of calls that are puts, and how often a body is long
    let put_pct = [20u64, 50, 80][(rng.next_u64() % 3) as usize];
    let long_pct = [0u64, 5, 30][(rng.next_u64() % 3) as usize];
    let mut last_head = 0usize;
    for _ in 0..steps {
        let op = if rng.next_u64() % 100 < put_pct {
            let session = rng.next_u64() % 4;
            let ty = [0x40u64, 0x49, 0x4f, 0x7fff][(rng.next_u64() % 4) as usize];
            let len = if rng.next_u64() % 100 < long_pct {
                [MAX - 1, MAX, MAX + 1, MAX + 1, MAX + 100, 3 * MAX][(rng.next_u64() % 6) as usize]
            } else {
                [0usize, 1, 2, 3, 10, 40, 200][(rng.next_u64() % 7) as usize]
            };
            let tag = (rng.next_u64() % 256) as u8;
            let body = vec![tag; len];
            let was_len = nv.q.len();
            let second = nv.q.get(1).cloned();
            let got = p.put(session, ty, &body);
            let want = nv.put((session, ty, body));
            assert_eq!(got, want, "put differs from the naive ring");
            let ok = got.is_some();
            assert_eq!(ok, len <= MAX, "a body is kept exactly when it is within the limit");
            assert_eq!(
                got.unwrap_or(0),
                u64::from(ok && was_len == CAP),
                "a put gives up a frame exactly when the ring was full"
            );
            if ok {
                seen.at_limit += u32::from(len == MAX);
                seen.zero_len += u32::from(len == 0);
                if was_len == CAP {
                    seen.dropped_oldest += 1;
                    assert_eq!(
                        nv.q.front(),
                        second.as_ref(),
                        "the frame after the oldest is not the oldest now"
                    );
                    assert_eq!(nv.q.len(), CAP, "a full ring grew");
                }
                assert_eq!(
                    nv.q.back().map(|f| f.0),
                    Some(session),
                    "the new frame is not the newest held"
                );
            } else {
                seen.refused += 1;
                seen.refused_full += u32::from(was_len == CAP);
                assert_eq!(nv.q.len(), was_len, "a refused body changed the ring");
            }
            format!(
                r#""op":"put","f":{},"ok":{ok},"gave":{}"#,
                json_frame(session, ty, len, if len == 0 { 0 } else { tag }),
                got.unwrap_or(0)
            )
        } else {
            // buffers too small by one, just right, and large
            let front_len = nv.q.front().map_or(0, |f| f.2.len());
            let oc = [front_len.saturating_sub(1), front_len, front_len, MAX, 3, 0][(rng.next_u64() % 6) as usize];
            let mut buf = vec![0xeeu8; oc.max(1)];
            let buf = &mut buf[..oc];
            let got = p.take(buf);
            let (res, o, need) = match got {
                Ok(None) => {
                    assert!(nv.q.is_empty());
                    seen.took_empty += 1;
                    ("none", "[]".to_owned(), 0)
                }
                Ok(Some((s, t, l))) => {
                    let f = nv.q.pop_front().unwrap();
                    nv.head = (nv.head + 1) % CAP;
                    assert_eq!(
                        (s, t, l),
                        (f.0, f.1, f.2.len()),
                        "take gave another frame than the oldest"
                    );
                    assert_eq!(&buf[..l], &f.2[..], "the body read back is not the body put");
                    seen.taken += 1;
                    ("ok", json_frame(s, t, l, tag_of(&f.2)), 0)
                }
                Err(l) => {
                    let f = nv.q.front().unwrap();
                    assert_eq!(l, f.2.len());
                    assert!(l > oc, "a frame that fits the buffer was refused");
                    seen.stayed += 1;
                    ("err", "[]".to_owned(), l)
                }
            };
            format!(r#""op":"take","oc":{oc},"res":"{res}","out":{o},"need":{need}"#)
        };
        seen.wrapped += u32::from(p.head() < last_head);
        last_head = p.head();
        // the ring is the naive queue after every call, bodies and all
        for (k, f) in nv.q.iter().enumerate() {
            assert_eq!(
                p.frame(k),
                Some((f.0, f.1, f.2.len(), tag_of(&f.2))),
                "the ring differs from the naive queue"
            );
        }
        assert_eq!(p.frame(nv.q.len()), None);
        let v = view(&p, &nv);
        let _ = writeln!(out, r#"{{"t":"cox","run":{id},{op},"v":{v}}}"#);
    }
    // the ring drains in the order the frames came, and then holds nothing
    let want: Vec<Frame> = nv.q.iter().cloned().collect();
    let mut big = vec![0u8; MAX];
    for f in want {
        let (s, t, l) = p.take(&mut big).unwrap().unwrap();
        assert_eq!((s, t, &big[..l]), (f.0, f.1, &f.2[..]));
        nv.q.pop_front();
        nv.head = (nv.head + 1) % CAP;
        let v = view(&p, &nv);
        let _ = writeln!(
            out,
            r#"{{"t":"cox","run":{id},"op":"take","oc":{MAX},"res":"ok","out":{},"need":0,"v":{v}}}"#,
            json_frame(s, t, l, tag_of(&f.2))
        );
    }
    assert_eq!(p.take(&mut big), Ok(None));
    let v = view(&p, &nv);
    let _ = writeln!(
        out,
        r#"{{"t":"cox","run":{id},"op":"take","oc":{MAX},"res":"none","out":[],"need":0,"v":{v}}}"#
    );
}

#[test]
fn the_extension_ring_matches_the_models() {
    let mut rng = SplitMix64::new(0x6578_7472);
    let mut out = String::new();
    let mut seen = Seen::default();
    for id in 1..=80u32 {
        run(&mut rng, &mut out, id, 300, &mut seen);
    }
    assert!(seen.dropped_oldest > 0, "no full ring dropped its oldest frame");
    assert!(seen.refused > 0, "no body over the limit was refused");
    assert!(seen.refused_full > 0, "no body was refused by a full ring");
    assert!(seen.at_limit > 0, "no body of exactly the limit was kept");
    assert!(seen.wrapped > 0, "the head never went round");
    assert!(seen.stayed > 0, "no frame stayed held for a short buffer");
    assert!(seen.taken > 0, "no frame was taken");
    assert!(seen.took_empty > 0, "no take found the ring empty");
    assert!(seen.zero_len > 0, "no empty body was kept");
    if let Ok(dir) = std::env::var("VINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("ext_in.ndjson"), &out).unwrap();
    }
}
