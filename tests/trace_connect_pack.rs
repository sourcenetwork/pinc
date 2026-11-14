//! Trace generation for the batch builder: seeded random runs of the real `BatchBuilder` through its public API,
//! recorded as ndjson (`connect_pack.ndjson`) for the TLA+ trace check (`TraceConnectPack.tla`) and the Lean replay
//! (`Vinc/TraceConnectPack.lean`).
//!
//! A run is a sequence of batches in one buffer, whose length comes from the run (the real `MAX_FRAME_LEN`, with
//! room to spare, with none to spare, and every shortage down to a buffer smaller than the header room). A batch is
//! built by offering frames of every kind and size: PING, packets of every length up to the maximum with a short
//! and a long header, SEND and SEND-by-alias frames, sleep notices of every length (so that 16384 bytes is passed
//! by a few frames), BATCH frames, and frames whose encoder refuses them (an empty or too long packet, an alias out
//! of range). Every few offers the builder is dropped and rebuilt from its `BatchState` (`resume`). Each answer is
//! checked against a plain reference written here (the rules of the module documentation), and every finished
//! record is decoded with the real `Frame::decode` and compared with the frames that were accepted, in order.
//! The trace is written to the directory in `VINC_TRACE_DIR` when it is set; otherwise nothing is written.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines,
    clippy::items_after_statements,
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::type_complexity,
    unreachable_pub
)]

mod connect_common;

use std::fmt::Write as _;

use connect_common::nid;
use vinc_connect::carrier::{
    BATCH_MAX_BYTES, BATCH_MAX_FRAMES, BatchBuilder, Frame, FrameError, MAX_FRAME_LEN, MAX_PACKET_LEN, NODE_ID_LEN,
    Offer,
};
use vinc_tests::SplitMix64;

/// `MAX_NOTICE_LEN` of the code.
const MAX_NOTICE_LEN: usize = 8192;
/// `BATCH_HEAD_MAX` of the code: two bytes and three per frame.
const HEAD: usize = 2 + BATCH_MAX_FRAMES * 3;

/// An owned frame: what the test offers.
#[derive(Clone)]
enum Spec {
    Ping,
    Pong,
    SelfSend(Vec<u8>),
    Send(Vec<u8>),
    SendAlias(u8, Vec<u8>),
    Sleep(Vec<u8>),
    Batch(Vec<u8>),
}

impl Spec {
    fn frame(&self) -> Frame<'_> {
        match self {
            Self::Ping => Frame::Ping,
            Self::Pong => Frame::Pong,
            Self::SelfSend(p) => Frame::SelfSend { packet: p },
            Self::Send(p) => Frame::Send {
                dst: nid(7),
                flag: 3,
                packet: p,
            },
            Self::SendAlias(a, p) => Frame::SendAlias {
                alias: *a,
                flag: 1,
                packet: p,
            },
            Self::Sleep(n) => Frame::Sleep { notice: n },
            Self::Batch(b) => Frame::decode(b).unwrap(),
        }
    }
}

/// What the encoder does with a frame given room enough: its length, or the bytes written before it refuses and the
/// error it names.
fn shape(s: &Spec) -> (usize, Option<&'static str>) {
    let f = s.frame();
    let mut big = vec![0u8; MAX_FRAME_LEN + 64];
    match f.encode(&mut big) {
        Ok(n) => (n, None),
        Err(FrameError::PacketSize) => (
            match s {
                Spec::Send(_) => 1 + NODE_ID_LEN + 1,
                Spec::SendAlias(..) => 1 + 1 + 1,
                _ => 1,
            },
            Some("packet"),
        ),
        Err(FrameError::Alias(_)) => (1, Some("alias")),
        Err(e) => panic!("unexpected encoder error {e:?}"),
    }
}

fn packet(rng: &mut SplitMix64, long: bool, len: usize) -> Vec<u8> {
    let mut p: Vec<u8> = (0..len).map(|_| rng.next_u64() as u8).collect();
    if let Some(b) = p.first_mut() {
        *b = if long { *b | 0x80 } else { *b & 0x7f };
    }
    p
}

fn pick(rng: &mut SplitMix64) -> Spec {
    let len = |rng: &mut SplitMix64, max: usize| match rng.next_u64() % 6 {
        0 => 1,
        1 => max,
        2 => max / 2,
        _ => (rng.next_u64() as usize % max) + 1,
    };
    match rng.next_u64() % 16 {
        0 => Spec::Ping,
        1 => Spec::Pong,
        2..=4 => {
            let l = len(rng, MAX_PACKET_LEN);
            Spec::SelfSend(packet(rng, false, l))
        }
        5 => {
            let l = len(rng, MAX_PACKET_LEN);
            Spec::SelfSend(packet(rng, true, l))
        }
        6 => {
            let l = len(rng, MAX_PACKET_LEN);
            let long = rng.next_u64().is_multiple_of(4);
            Spec::Send(packet(rng, long, l))
        }
        7 => {
            let l = len(rng, MAX_PACKET_LEN);
            Spec::SendAlias((rng.next_u64() % 32) as u8, packet(rng, false, l))
        }
        8..=9 => {
            let l = len(rng, MAX_NOTICE_LEN);
            Spec::Sleep(vec![0x55; l])
        }
        10 => {
            let mut buf = vec![0u8; MAX_FRAME_LEN + 64];
            let mut b = BatchBuilder::new(&mut buf);
            assert_eq!(b.offer(&Frame::Ping).unwrap(), Offer::Added);
            assert_eq!(b.offer(&Frame::Pong).unwrap(), Offer::Added);
            Spec::Batch(b.finish().unwrap().unwrap().to_vec())
        }
        // a frame whose encoder refuses it
        11 => Spec::SelfSend(Vec::new()),
        12 => Spec::SelfSend(packet(rng, false, MAX_PACKET_LEN + 1)),
        13 => Spec::SendAlias(32 + (rng.next_u64() % 200) as u8, vec![1]),
        14 => Spec::Send(Vec::new()),
        _ => Spec::SelfSend(packet(rng, false, 3)),
    }
}

/// The reference: the rules of the module documentation, with the buffer length of the run.
struct Reference {
    cap: usize,
    lens: Vec<usize>,
}

impl Reference {
    fn used(&self) -> usize {
        self.lens.iter().sum()
    }
    /// `(answer, error)`: "added", "refused" or "err" with the error name.
    fn offer(&mut self, s: &Spec) -> (&'static str, &'static str) {
        let f = s.frame();
        let (n, bad) = shape(s);
        if matches!(f, Frame::Batch(_)) || f.is_long_header() || self.lens.len() >= BATCH_MAX_FRAMES {
            return ("refused", "");
        }
        let start = HEAD + self.used();
        if start > self.cap {
            return ("err", "noroom");
        }
        if n > self.cap - start {
            return if self.lens.is_empty() {
                ("err", "small")
            } else {
                ("refused", "")
            };
        }
        if let Some(e) = bad {
            return ("err", e);
        }
        if self.used() + n > BATCH_MAX_BYTES {
            return ("refused", "");
        }
        self.lens.push(n);
        ("added", "")
    }
}

fn err_name(e: &FrameError) -> &'static str {
    match e {
        FrameError::NoRoom => "noroom",
        FrameError::Wire(_) => "small",
        FrameError::PacketSize => "packet",
        FrameError::Alias(_) => "alias",
        other => panic!("unexpected error {other:?}"),
    }
}

fn run(seed: u64, cap: usize, out: &mut Vec<String>) {
    let mut rng = SplitMix64::new(seed);
    let mut buf = vec![0u8; cap];
    out.push(format!(
        r#"{{"t":"bbnew","f":{BATCH_MAX_FRAMES},"b":{BATCH_MAX_BYTES},"head":{HEAD},"cap":{cap}}}"#
    ));
    for _ in 0..12 {
        let mut r = Reference { cap, lens: Vec::new() };
        let mut accepted: Vec<Spec> = Vec::new();
        let mut b = BatchBuilder::new(&mut buf);
        let frames = rng.next_u64() % 90;
        // some batches are filled with small frames so that the count bound is reached
        let small = rng.next_u64().is_multiple_of(4);
        for _ in 0..frames {
            let s = if small && !rng.next_u64().is_multiple_of(8) {
                let l = 1 + (rng.next_u64() % 40) as usize;
                Spec::SelfSend(packet(&mut rng, false, l))
            } else {
                pick(&mut rng)
            };
            if rng.next_u64().is_multiple_of(3) {
                let st = b.state();
                b = BatchBuilder::resume(&mut buf, st);
            }
            let (want, want_err) = r.offer(&s);
            let got = b.offer(&s.frame());
            let (res, e) = match got {
                Ok(Offer::Added) => ("added", ""),
                Ok(Offer::Refused) => ("refused", ""),
                Err(ref e) => ("err", err_name(e)),
            };
            assert_eq!((want, want_err), (res, e), "offer disagrees with the reference");
            if res == "added" {
                accepted.push(s.clone());
            }
            assert_eq!(b.len(), r.lens.len());
            assert_eq!(b.state().len(), r.lens.len());
            assert!(r.lens.len() <= BATCH_MAX_FRAMES && r.used() <= BATCH_MAX_BYTES);
            let (n, bad) = shape(&s);
            out.push(format!(
                r#"{{"t":"bboffer","n":{n},"long":{},"isbatch":{},"bad":{},"err":"{}","res":"{res}","e":"{e}","cnt":{}}}"#,
                s.frame().is_long_header(),
                matches!(s, Spec::Batch(_)),
                bad.is_some(),
                bad.unwrap_or(""),
                b.len()
            ));
        }
        let used = r.used();
        let rec = b.finish().unwrap().map(<[u8]>::to_vec);
        let (kind, len, lens) = match (&rec, accepted.len()) {
            (None, 0) => ("none", 0, Vec::new()),
            (Some(rec), 1) => {
                // one frame alone: the frame itself, no header
                let mut one = vec![0u8; MAX_FRAME_LEN + 64];
                let n = accepted[0].frame().encode(&mut one).unwrap();
                assert_eq!(rec[..], one[..n]);
                assert_eq!(Frame::decode(rec).unwrap(), accepted[0].frame());
                ("single", rec.len(), vec![n])
            }
            (Some(rec), k) if k >= 2 => {
                assert_eq!(rec[0], 13);
                assert!(rec.len() <= MAX_FRAME_LEN);
                let Frame::Batch(batch) = Frame::decode(rec).unwrap() else {
                    panic!("a batch record that is not a batch")
                };
                let got: Vec<Frame<'_>> = batch.frames().collect();
                let want: Vec<Frame<'_>> = accepted.iter().map(Spec::frame).collect();
                assert_eq!(got, want, "the batch reads back as it was written");
                assert_eq!(batch.len(), k);
                assert_eq!(batch.frames().count(), k);
                assert!(rec.len() > used);
                ("batch", rec.len(), r.lens.clone())
            }
            other => panic!("finish: {other:?} for {} accepted frames", accepted.len()),
        };
        let lens = lens.iter().map(ToString::to_string).collect::<Vec<_>>().join(",");
        out.push(format!(
            r#"{{"t":"bbfin","kind":"{kind}","len":{len},"lens":[{lens}]}}"#
        ));
    }
}

#[test]
fn the_batch_builder_matches_the_reference_and_records_its_trace() {
    let mut out = Vec::new();
    let caps = [
        MAX_FRAME_LEN,
        MAX_FRAME_LEN + 64,
        MAX_FRAME_LEN + 1,
        HEAD + 3000,
        HEAD + 1500,
        HEAD + 20,
        HEAD + 1,
        HEAD,
        HEAD - 1,
        10,
        0,
    ];
    for seed in 0..66u64 {
        run(seed, caps[(seed as usize) % caps.len()], &mut out);
    }
    let Some(dir) = std::env::var_os("VINC_TRACE_DIR") else {
        return;
    };
    let dir = std::path::PathBuf::from(dir);
    std::fs::create_dir_all(&dir).unwrap();
    let mut text = String::new();
    for l in &out {
        writeln!(text, "{l}").unwrap();
    }
    std::fs::write(dir.join("connect_pack.ndjson"), text).unwrap();
}
