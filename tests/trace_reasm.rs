//! Trace generation for the handshake fragment reassembly: seeded runs of a real reassembly (`pinc-transport`, built
//! with the `trace` feature), recorded as ndjson (`reasm.ndjson`) for the TLA+ trace check (`TraceReasm.tla`) and the
//! Lean replay (`Pinc/TraceReasm.lean`).
//!
//! A run cuts messages of random lengths (up to the largest message and past it) into fragments and hands them in
//! order, reversed, shuffled, repeated, overlapping, cut off at the end of the message and with a message of another
//! length in between (an empty reassembly takes it and then refuses the fragments of the message it was cut from;
//! one that holds the message refuses it); the sparse mode sends every other fragment first so the table of runs fills. After every call
//! the reassembly shows its runs and the message length being assembled.
//!
//! The test checks the bytes itself: a message reported complete is, byte for byte, the message that was cut, and no
//! run ever covers a byte that was not sent.
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

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::conn::{ReasmProbe, ReasmView};

fn view_json(v: &ReasmView) -> String {
    let runs: Vec<String> = v.runs.iter().map(|(s, e)| format!("[{s},{e}]")).collect();
    format!(r#"{{"runs":[{}],"total":{}}}"#, runs.join(","), v.total)
}

fn run(rng: &mut SplitMix64, out: &mut String, id: u32, sparse: bool) {
    let mut p = ReasmProbe::new();
    let max = ReasmProbe::MAX_MESSAGE;
    let _ = writeln!(
        out,
        r#"{{"t":"txrs","run":{id},"op":"init","max":{max},"nr":{},"v":{}}}"#,
        ReasmProbe::RUNS,
        view_json(&p.view())
    );
    for _ in 0..4 {
        let total = match rng.next_u64() % 8 {
            0 => 1 + (rng.next_u64() % 12) as usize,
            1 => max,
            2 => max + 1 + (rng.next_u64() % 4) as usize,
            _ => 1 + (rng.next_u64() % 2400) as usize,
        };
        // a message of another length first, so that no run of the last message is taken for a run of this one
        for other in [1usize, 2] {
            let r = p.add(other, 0, &[]);
            let _ = writeln!(
                out,
                r#"{{"t":"txrs","run":{id},"op":"add","total":{other},"off":0,"len":0,"out":{},"v":{}}}"#,
                r.map_or(-1, |t| i64::try_from(t).unwrap()),
                view_json(&p.view())
            );
        }
        // A message that did not complete leaves its runs: the next message of that length agrees with them where it
        // overlaps and adds its own bytes elsewhere, so the bytes are the cut message's only from an empty start.
        let dirty = !p.view().runs.is_empty();
        let mut msg = vec![0u8; total];
        rng.fill(&mut msg);
        // The bytes held for this length are this message's at every covered run, so it agrees with them where it
        // overlaps (the reassembly refuses a byte that differs and keeps the first).
        let held = p.view();
        if dirty && held.total == total {
            for &(a, b) in &held.runs {
                if let (Some(dst), Some(src)) = (msg.get_mut(a..b), p.buffer().get(a..b)) {
                    dst.copy_from_slice(src);
                }
            }
        }
        let width = 1 + (rng.next_u64() % 200) as usize;
        let mut frags: Vec<(usize, usize)> = (0..total).step_by(width).map(|o| (o, (o + width).min(total))).collect();
        match rng.next_u64() % 4 {
            0 => frags.reverse(),
            1 => {
                for i in (1..frags.len()).rev() {
                    frags.swap(i, (rng.next_u64() % (i as u64 + 1)) as usize);
                }
            }
            _ => {}
        }
        if sparse {
            let odd: Vec<_> = frags
                .iter()
                .copied()
                .enumerate()
                .filter(|(i, _)| i % 2 == 1)
                .map(|x| x.1)
                .collect();
            let even: Vec<_> = frags
                .iter()
                .copied()
                .enumerate()
                .filter(|(i, _)| i.is_multiple_of(2))
                .map(|x| x.1)
                .collect();
            frags = odd.into_iter().chain(even).collect();
        }
        let mut sent_cover = vec![false; total.min(max)];
        let mut done = false;
        let mut i = 0;
        while i < frags.len() && !done {
            let (s, e) = frags[i];
            i += 1;
            // sometimes repeat, overlap, run past the end, or interleave a message of another length
            let mut start = s;
            let mut stop = e;
            match rng.next_u64() % 8 {
                0 => start = start.saturating_sub((rng.next_u64() % 30) as usize),
                1 => stop += (rng.next_u64() % 50) as usize,
                2 => frags.push((s, e)),
                3 => {
                    let other = total ^ 1;
                    let r = p.add(other, s, &[7; 5]);
                    let _ = writeln!(
                        out,
                        r#"{{"t":"txrs","run":{id},"op":"add","total":{},"off":{s},"len":5,"out":{},"v":{}}}"#,
                        other,
                        r.map_or(-1, |t| i64::try_from(t).unwrap()),
                        view_json(&p.view())
                    );
                    // an empty reassembly takes it and then holds that message; one holding this message refuses it
                }
                _ => {}
            }
            let stop_c = stop.min(total.max(1) + 30);
            let data: Vec<u8> = (start..stop_c).map(|k| msg.get(k).copied().unwrap_or(0xaa)).collect();
            let before = p.view();
            let r = p.add(total, start, &data);
            let after = p.view();
            let _ = writeln!(
                out,
                r#"{{"t":"txrs","run":{id},"op":"add","total":{total},"off":{start},"len":{},"out":{},"v":{}}}"#,
                data.len(),
                r.map_or(-1, |t| i64::try_from(t).unwrap()),
                view_json(&after)
            );
            if !before.runs.is_empty() && before.total != total {
                // another message holds the reassembly: the fragment is refused and the runs keep that message
                assert_eq!(after, before, "a fragment of another length changed the reassembly");
                assert!(r.is_none());
                continue;
            }
            if total == 0 || total > max {
                assert_eq!(after, before, "a refused length changed the reassembly");
                continue;
            }
            if before.total != total {
                sent_cover.fill(false);
            }
            if let Some(t) = r {
                assert_eq!(t, total);
                assert!(
                    dirty || p.buffer()[..total] == msg[..],
                    "the message reported complete differs from the message cut"
                );
                assert!(after.runs.is_empty() && after.total == 0);
                done = true;
            } else {
                // every run is inside the message and the table never overflows
                assert!(after.runs.len() <= ReasmProbe::RUNS);
                for w in after.runs.windows(2) {
                    assert!(w[0].1 < w[1].0);
                }
                for (a, b) in &after.runs {
                    assert!(a < b && *b <= total);
                    assert!(
                        dirty || p.buffer()[*a..*b] == msg[*a..*b],
                        "a run holds bytes that were not sent"
                    );
                    for c in sent_cover.iter_mut().take(*b).skip(*a) {
                        *c = true;
                    }
                }
            }
        }
    }
}

#[test]
fn reassembly_runs_match_the_models() {
    let mut rng = SplitMix64::traced(0x5253_0001);
    let mut out = String::new();
    for id in 1..=80u32 {
        run(&mut rng, &mut out, id, id.is_multiple_of(3));
    }
    assert!(out.contains(r#""op":"add""#));
    assert!(
        pinc_tests::soaking() || out.contains(r#""out":-1"#) && out.matches(r#""runs":[]"#).count() > 80,
        "no message was ever completed"
    );
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("reasm.ndjson"), &out).unwrap();
    }
}
