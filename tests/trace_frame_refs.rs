//! Trace generation for the frame descriptors of a sent packet (`pinc-transport`, built with the `trace` feature):
//! real `FrameRefs` lists, recorded as ndjson (`frame_refs.ndjson`) for the TLA+ trace check (`TraceFrameRefs.tla`).
//!
//! A list is filled with stream and control descriptors, with ids, offsets and lengths at their extremes and the
//! descriptor every place holds at the start, and pushed on past the point it is full. After every push the list
//! shows what `as_slice`, `iter` and `into_iter` read, its length and whether it is empty.
//!
//! The test compares every call with a naive vector, so it is meaningful without the proof tools. The trace is
//! written to `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::too_many_lines,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub,
    clippy::borrow_deref_ref,
    clippy::indexing_slicing,
    clippy::manual_is_multiple_of
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::recovery::{FrameRef, FrameRefs, MAX_FRAME_REFS};

/// `n` little-endian 16-bit limbs of `v`.
fn limbs(v: u64, n: usize) -> String {
    let l: Vec<String> = (0..n).map(|i| ((v >> (16 * i)) & 0xffff).to_string()).collect();
    format!("[{}]", l.join(","))
}

/// A descriptor as the trace writes it.
fn enc(f: &FrameRef) -> String {
    match *f {
        FrameRef::Stream { id, offset, len, fin } => {
            format!(
                r#"["s",{},{},{},{fin}]"#,
                limbs(id, 4),
                limbs(offset, 4),
                limbs(u64::from(len), 2)
            )
        }
        FrameRef::Control { kind, id } => format!(r#"["c",{kind},{}]"#, limbs(id, 4)),
    }
}

fn list<'a>(it: impl Iterator<Item = &'a FrameRef>) -> String {
    format!("[{}]", it.map(enc).collect::<Vec<_>>().join(","))
}

/// The list as the model sees it, checked against the naive vector.
fn view(r: &FrameRefs, naive: &[FrameRef]) -> String {
    assert_eq!(r.as_slice(), naive);
    assert!(r.iter().eq(naive.iter()));
    assert!((&*r).into_iter().eq(naive.iter()));
    assert_eq!(r.len(), naive.len());
    assert_eq!(r.is_empty(), naive.is_empty());
    assert!(r.len() <= MAX_FRAME_REFS);
    format!(
        r#"{{"slice":{},"iter":{},"into":{},"len":{},"empty":{}}}"#,
        list(r.as_slice().iter()),
        list(r.iter()),
        list((&*r).into_iter()),
        r.len(),
        r.is_empty()
    )
}

/// One list: a `init` event, then each descriptor pushed.
fn run(out: &mut String, refused: &mut u32, pushes: impl IntoIterator<Item = FrameRef>) {
    let mut r = FrameRefs::new();
    let mut naive: Vec<FrameRef> = Vec::new();
    let d0 = enc(&FrameRef::Control { kind: 0, id: 0 });
    let _ = writeln!(
        out,
        r#"{{"t":"frame_refs","op":"init","max":{MAX_FRAME_REFS},"d0":{d0},"v":{}}}"#,
        view(&r, &naive)
    );
    for f in pushes {
        let before = r;
        let ok = r.push(f).is_ok();
        assert_eq!(
            ok,
            naive.len() < MAX_FRAME_REFS,
            "a push was refused or accepted wrongly"
        );
        if ok {
            naive.push(f);
        } else {
            *refused += 1;
            assert_eq!(r, before, "a refused push changed the list");
        }
        let _ = writeln!(
            out,
            r#"{{"t":"frame_refs","op":"push","f":{},"ok":{ok},"v":{}}}"#,
            enc(&f),
            view(&r, &naive)
        );
    }
}

#[test]
fn the_frame_refs_match_the_model() {
    let mut rng = SplitMix64::traced(0x6672_6566);
    let (mut out, mut refused) = (String::new(), 0u32);
    let big = [0u64, 1, 2, 1 << 31, 1 << 32, 1 << 63, u64::MAX];
    // the six values the i-th push picks from
    let six = [0u64, 1, 1 << 31, 1 << 32, 1 << 63, u64::MAX];
    let lens = [0u32, 1, u32::MAX];
    let kinds = [0u8, 2, 5, 6, 7, 8, 255];
    let ids = [0u64, 1, u64::MAX];
    assert_eq!(big.len(), 7);

    // 1. the descriptor every place holds at the start
    run(
        &mut out,
        &mut refused,
        (0..10).map(|_| FrameRef::Control { kind: 0, id: 0 }),
    );
    // 2. stream descriptors at their extremes
    let stream = |i: usize| FrameRef::Stream {
        id: six[i % 6],
        offset: six[5 - i % 6],
        len: lens[i % 3],
        fin: i % 2 == 0,
    };
    run(&mut out, &mut refused, (0..10).map(stream));
    // 3. control descriptors at their extremes
    let control = |i: usize| FrameRef::Control {
        kind: kinds[i % 7],
        id: ids[i % 3],
    };
    run(&mut out, &mut refused, (0..10).map(control));
    // 4. stream and control in turn, each pushed twice in a row
    run(
        &mut out,
        &mut refused,
        (0..10).map(|i| {
            if (i / 2) % 2 == 0 {
                stream(i / 2)
            } else {
                control(i / 2)
            }
        }),
    );
    // seeded lists
    for _ in 0..200 {
        let n = 1 + (rng.next_u64() % 12) as usize;
        let fs: Vec<FrameRef> = (0..n)
            .map(|_| {
                if rng.next_u64() % 2 == 0 {
                    FrameRef::Stream {
                        id: rng.next_u64(),
                        offset: rng.next_u64(),
                        len: rng.next_u64() as u32,
                        fin: rng.next_u64() & 1 == 1,
                    }
                } else {
                    FrameRef::Control {
                        kind: rng.next_u64() as u8,
                        id: rng.next_u64(),
                    }
                }
            })
            .collect();
        run(&mut out, &mut refused, fs);
    }
    assert!(refused > 0, "no push was refused");
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("frame_refs.ndjson"), &out).unwrap();
    }
}
