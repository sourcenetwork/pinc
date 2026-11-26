//! `pinc-transport` streams: a sending stream table and a receiving one joined by a script that delivers, repeats,
//! reorders and drops each frame and feeds the sender the acknowledgement, loss and late acknowledgement the
//! connection's recovery would, with the receiver's window updates carried back the same way.
//!
//! Where the expected behaviour comes from:
//! - `stream` module docs: "a frame takes free chunks or is held back (answered with nothing, so its sender repeats
//!   it)"; "a limit, once advertised or received, never shrinks, and a final size, once fixed, never changes"; "every
//!   chunk a stream, queue or buffer holds is charged to the pool and returned when its owner closes or drains".
//! - `StreamError` docs: `FlowControl`, `FinalSize`, `Conflict`, `StreamState`, `StreamLimit` are "violations by the
//!   peer"; an honest sender that follows the table's own frames and limits never causes one. `Exhausted` and
//!   `Fragmented` are local shortages: "nothing was stored and the packet should go unacknowledged".
//! - `Streams::next_stream_frame`: "retransmissions first (lowest hole first), then new data"; `copy_out` copies the
//!   frame's data; `on_lost` "queue its range again"; `on_late_acked` "cancel its queued retransmission".
//! - `Streams::consume`: "Consuming zero bytes after the end (or a reset) was seen lets the stream close".
//! - The universal rules: the bytes read are the bytes written, once and in order; no panic; after the link turns
//!   clean the transfer completes in a bounded number of rounds.
#![allow(clippy::unwrap_used, clippy::indexing_slicing, clippy::cast_possible_truncation)]

use std::collections::BTreeMap;

use ephyra::prelude::*;
use ephyra::{Arbitrary, gens};
use pinc_transport::stream::pool::{BufferPool, CHUNK_SIZE};
use pinc_transport::stream::{Config, ControlFrame, NoSource, PeerLimits, RecvStatus, StreamError, Streams};

type Table = Streams<NoSource, 8, 1025>;

#[derive(Clone, Debug, Arbitrary)]
enum Op {
    /// Open the next planned stream.
    Open,
    Write {
        #[ephyra(gen = gens::int(0u8..=7))]
        stream: u8,
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(0usize..=3000).boxed()), (2, gens::int(0usize..=70_000).boxed())]))]
        len: usize,
    },
    Finish(#[ephyra(gen = gens::int(0u8..=7))] u8),
    /// Build up to `count` frames of at most `budget` bytes.
    Send {
        #[ephyra(gen = gens::int(1u8..=8))]
        count: u8,
        #[ephyra(gen = gens::frequency(vec![(3, gens::int(1usize..=1400).boxed()), (1, gens::int(0usize..=20).boxed()), (1, gens::int(1usize..=40_000).boxed())]))]
        budget: usize,
    },
    /// Hand frame `which` (counted from the oldest unsettled one) to the receiver.
    Deliver(#[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Hand every frame in flight to the receiver, oldest first or newest first.
    DeliverAll(#[ephyra(gen = gens::bool())] bool),
    /// Acknowledge a delivered frame.
    Ack(#[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Declare a frame lost (delivered or not: a loss can be spurious).
    Lose(#[ephyra(gen = gens::int(0u8..=15))] u8),
    /// Acknowledge a frame declared lost that did arrive.
    LateAck(#[ephyra(gen = gens::int(0u8..=15))] u8),
    /// The receiver reads up to `len` bytes of a stream.
    Read {
        #[ephyra(gen = gens::int(0u8..=7))]
        stream: u8,
        #[ephyra(gen = gens::frequency(vec![(2, gens::int(0usize..=5000).boxed()), (1, gens::constant(usize::MAX).boxed())]))]
        len: usize,
    },
    /// Carry the receiver's control frames to the sender, or lose them.
    Control(#[ephyra(gen = gens::bool_with(0.8))] bool),
}

#[derive(Clone, Debug)]
struct Case {
    rchunks: usize,
    schunks: usize,
    window: u64,
    max_streams: u64,
    /// The length of each stream and whether it ends.
    plan: Vec<(usize, bool)>,
    ops: Vec<Op>,
}

fn case() -> impl Gen<Value = Case> {
    (
        gens::frequency(vec![(1, gens::int(2usize..=12).boxed()), (2, gens::int(12usize..=200).boxed())]),
        gens::frequency(vec![(1, gens::int(2usize..=12).boxed()), (2, gens::int(12usize..=200).boxed())]),
        gens::pick_from(vec![CHUNK_SIZE as u64, 20_000, 64 * 1024, 100_001, 1_310_720]),
        gens::int(1u64..=8),
        gens::vec((
            gens::frequency(vec![(2, gens::int(0usize..=5000).boxed()), (2, gens::int(0usize..=200_000).boxed())]),
            gens::bool_with(0.8),
        ))
        .len(1..=5),
        gens::vec(ephyra::any::<Op>()).len(0..=150),
    )
        .map(|(rchunks, schunks, window, max_streams, plan, ops)| Case {
            rchunks,
            schunks,
            window,
            max_streams,
            plan,
            ops,
        })
        .with_shrink(shrink_case)
}

fn shrink_case(c: &Case, visit: &mut dyn FnMut(Case) -> std::ops::ControlFlow<()>) -> std::ops::ControlFlow<()> {
    let n = c.ops.len();
    for cut in [n / 2, n * 3 / 4, n.saturating_sub(1)] {
        if cut < n {
            visit(Case { ops: c.ops[..cut].to_vec(), ..c.clone() })?;
        }
    }
    for i in 0..n {
        let mut ops = c.ops.clone();
        ops.remove(i);
        visit(Case { ops, ..c.clone() })?;
    }
    if c.plan.len() > 1 {
        visit(Case { plan: c.plan[..c.plan.len() - 1].to_vec(), ..c.clone() })?;
    }
    for (i, &(len, fin)) in c.plan.iter().enumerate() {
        if len > 0 {
            let mut plan = c.plan.clone();
            plan[i] = (len / 2, fin);
            visit(Case { plan, ..c.clone() })?;
        }
    }
    for (rchunks, schunks) in [(c.rchunks / 2, c.schunks), (c.rchunks, c.schunks / 2)] {
        if rchunks >= 2 && schunks >= 2 && (rchunks, schunks) != (c.rchunks, c.schunks) {
            visit(Case { rchunks, schunks, ..c.clone() })?;
        }
    }
    std::ops::ControlFlow::Continue(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fate {
    InFlight,
    Lost,
    Done,
}

#[derive(Debug)]
struct Frame {
    id: u64,
    offset: u64,
    data: Vec<u8>,
    fin: bool,
    /// The receiver stored it at least once (it returned `Ok`), so a packet with it could be acknowledged.
    stored: bool,
    fate: Fate,
}

/// One planned stream on the sender's side.
#[derive(Debug, Default)]
struct Planned {
    id: Option<u64>,
    data: Vec<u8>,
    len: usize,
    fin: bool,
    written: usize,
    finished: bool,
}

struct World {
    rpool: BufferPool<'static>,
    spool: BufferPool<'static>,
    r: Box<Table>,
    s: Box<Table>,
    plan: Vec<Planned>,
    /// What the receiver read, per stream id.
    read: BTreeMap<u64, Vec<u8>>,
    /// The streams whose end the receiver reported (`consume` returned `Finished`).
    ended: std::collections::BTreeSet<u64>,
    flight: Vec<Frame>,
    /// The send limit the sender may use per stream, as the receiver told it.
    limit: BTreeMap<u64, u64>,
    window: u64,
    now: u64,
    sent_frames: usize,
}

fn pattern(len: usize, seed: u64) -> Vec<u8> {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    (0..len)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x as u8
        })
        .collect()
}

impl World {
    fn new(c: &Case) -> Self {
        let rpool = BufferPool::new_boxed(c.rchunks);
        let spool = BufferPool::new_boxed(c.schunks);
        let mut rcfg = Config::new(false);
        rcfg.initial_stream_window = c.window;
        rcfg.max_streams = c.max_streams;
        let r = Box::new(Table::new(&rcfg, &rpool));
        let mut scfg = Config::new(true);
        let window = r.recv_window();
        scfg.peer = PeerLimits {
            window,
            max_streams: r.advertised_streams(),
        };
        let s = Box::new(Table::new(&scfg, &spool));
        let plan = c
            .plan
            .iter()
            .enumerate()
            .map(|(i, &(len, fin))| Planned {
                data: pattern(len, i as u64 + 1),
                len,
                fin,
                ..Planned::default()
            })
            .collect();
        Self {
            rpool,
            spool,
            r,
            s,
            plan,
            read: BTreeMap::new(),
            ended: std::collections::BTreeSet::new(),
            flight: Vec::new(),
            limit: BTreeMap::new(),
            window,
            now: 1_000_000_000,
            sent_frames: 0,
        }
    }

    fn open(&mut self) {
        let Some(p) = self.plan.iter_mut().find(|p| p.id.is_none()) else { return };
        match self.s.open_stream(&self.spool, false) {
            Ok(id) => {
                assert!(!self.limit.contains_key(&id), "stream id {id} opened twice");
                self.limit.insert(id, self.window);
                p.id = Some(id);
            },
            Err(e) => assert!(
                matches!(e, StreamError::StreamLimit | StreamError::TableFull | StreamError::Exhausted),
                "open refused with {e:?}"
            ),
        }
    }

    fn write(&mut self, i: usize, len: usize) {
        let Some(p) = self.plan.get_mut(i) else { return };
        let Some(id) = p.id else { return };
        if p.finished {
            // A finished stream refuses writes, and is forgotten once everything was acknowledged.
            return;
        }
        let end = (p.written + len).min(p.len);
        let r = self.s.write(&mut self.spool, id, &p.data[p.written..end], u64::MAX);
        let n = r.unwrap_or_else(|e| panic!("write on {id} refused: {e:?}"));
        assert!(n <= end - p.written, "write on {id} took more than it was given");
        p.written += n;
    }

    /// End a stream whose bytes are all written: during the chaos only a stream planned to end, on the clean link
    /// every one (a stream left open keeps the window it was granted, and the docs say a window is granted only while
    /// the ledger fits the pool, so an idle open stream may hold back another one for good).
    fn finish(&mut self, i: usize, all: bool) {
        let Some(p) = self.plan.get_mut(i) else { return };
        let Some(id) = p.id else { return };
        if !(p.fin || all) || p.written < p.len || p.finished {
            return;
        }
        assert_eq!(self.s.finish(id), Ok(()), "finish of {id}");
        p.finished = true;
    }

    fn planned(&self, id: u64) -> &Planned {
        self.plan.iter().find(|p| p.id == Some(id)).unwrap()
    }

    fn send(&mut self, count: usize, budget: usize) {
        for _ in 0..count {
            let Some(chunk) = self.s.next_stream_frame(&mut self.spool, budget) else { return };
            assert!(chunk.len <= budget, "a frame of {} bytes for a budget of {budget}", chunk.len);
            let mut buf = vec![0u8; chunk.len];
            let n = self.s.copy_out(&mut self.spool, &chunk, &mut buf);
            assert_eq!(n, Ok(chunk.len), "copy_out of {chunk:?}");
            let p = self.planned(chunk.id);
            let end = chunk.offset + chunk.len as u64;
            assert!(end <= p.written as u64, "frame {chunk:?} reaches past the {} bytes written", p.written);
            assert!(
                buf == p.data[chunk.offset as usize..end as usize],
                "frame {chunk:?} carries bytes other than those written"
            );
            if chunk.fin {
                assert!(p.finished, "frame {chunk:?} ends a stream that was not finished");
                assert_eq!(end, p.written as u64, "frame {chunk:?} ends the stream short of its length");
            } else {
                assert!(chunk.len > 0, "an empty frame without the end: {chunk:?}");
            }
            let limit = self.limit.get(&chunk.id).copied().unwrap_or(0);
            assert!(end <= limit, "frame {chunk:?} passes the stream's limit {limit}");
            self.sent_frames += 1;
            self.flight.push(Frame {
                id: chunk.id,
                offset: chunk.offset,
                data: buf,
                fin: chunk.fin,
                stored: false,
                fate: Fate::InFlight,
            });
        }
    }

    /// The index of the `which`-th frame (modulo) among those `ok` accepts.
    fn pick(&self, which: u8, ok: impl Fn(&Frame) -> bool) -> Option<usize> {
        let idx: Vec<usize> = (0..self.flight.len()).filter(|&i| ok(&self.flight[i])).collect();
        if idx.is_empty() {
            return None;
        }
        Some(idx[usize::from(which) % idx.len()])
    }

    fn deliver(&mut self, i: usize) {
        let f = &mut self.flight[i];
        let r = self.r.on_stream_frame(&mut self.rpool, f.id, f.offset, &f.data, f.fin);
        match r {
            Ok(()) => f.stored = true,
            Err(StreamError::Exhausted | StreamError::Fragmented) => {},
            Err(e) => panic!("the receiver refused an honest frame of {} at {} (+{}): {e:?}", f.id, f.offset, f.data.len()),
        }
    }

    fn settle(&mut self, i: usize, to: Fate) {
        let f = &mut self.flight[i];
        let (id, offset, len, fin) = (f.id, f.offset, f.data.len() as u64, f.fin);
        let from = f.fate;
        f.fate = to;
        match (from, to) {
            (Fate::InFlight, Fate::Done) => self.s.on_acked(&mut self.spool, id, offset, len, fin),
            (Fate::InFlight, Fate::Lost) => self.s.on_lost(&mut self.spool, id, offset, len, fin),
            (Fate::Lost, Fate::Done) => self.s.on_late_acked(&mut self.spool, id, offset, len, fin),
            _ => unreachable!(),
        }
    }

    fn read(&mut self, i: usize, max: usize) {
        let Some(id) = self.plan.get(i).and_then(|p| p.id) else { return };
        let mut left = max;
        let mut turns = 0usize;
        while left > 0 {
            turns += 1;
            assert!(turns <= 100_000, "stream {id}: reading did not end after 100,000 chunks");
            let Some(chunk) = self.r.read_chunk(&self.rpool, id) else { break };
            let n = chunk.len().min(left);
            assert!(n > 0, "an empty readable chunk on {id}");
            let got = self.read.entry(id).or_default();
            got.extend_from_slice(&chunk[..n]);
            left -= n;
            self.now += 1_000_000;
            let r = self.r.consume(&mut self.rpool, id, n, self.now, 10_000_000);
            assert!(r.is_ok(), "consume of {n} readable bytes on {id}: {r:?}");
            if r == Ok(RecvStatus::Finished) {
                self.ended.insert(id);
            }
        }
        if max == usize::MAX {
            // Let a stream whose end was seen close.
            if self.r.consume(&mut self.rpool, id, 0, self.now, 10_000_000) == Ok(RecvStatus::Finished) {
                self.ended.insert(id);
            }
        }
        let p = self.planned(id);
        let got = self.read.get(&id).map_or(&[][..], Vec::as_slice);
        assert!(got.len() <= p.written, "stream {id}: read {} bytes of {} written", got.len(), p.written);
        assert!(got == &p.data[..got.len()], "stream {id}: the bytes read differ from those written");
    }

    fn control(&mut self, carry: bool) {
        // As the connection does before it writes control frames.
        self.r.regrant(&self.rpool);
        self.s.regrant(&self.spool);
        while let Some(f) = self.r.pending_control() {
            if !carry {
                self.r.on_control_lost(&f);
                continue;
            }
            match f {
                ControlFrame::MaxStreamData { id, max } => {
                    let l = self.limit.entry(id).or_insert(0);
                    *l = (*l).max(max);
                    let r = self.s.on_max_stream_data(&self.spool, id, max);
                    assert!(r.is_ok(), "the sender refused MAX_STREAM_DATA {max} for {id}: {r:?}");
                },
                ControlFrame::MaxStreams { limit } => self.s.on_max_streams(limit),
                other => panic!("the receiver sent {other:?} with no stop or reset asked"),
            }
            self.r.on_control_acked(&mut self.rpool, &f);
        }
        assert!(self.s.pending_control().is_none(), "the sender has control frames with no reset asked");
    }

    fn step(&mut self, op: &Op) {
        match *op {
            Op::Open => self.open(),
            Op::Write { stream, len } => self.write(usize::from(stream), len),
            Op::Finish(i) => self.finish(usize::from(i), false),
            Op::Send { count, budget } => self.send(usize::from(count), budget),
            Op::Deliver(w) => {
                if let Some(i) = self.pick(w, |_| true) {
                    self.deliver(i);
                }
            },
            Op::DeliverAll(newest_first) => {
                let mut idx: Vec<usize> = (0..self.flight.len()).filter(|&i| self.flight[i].fate == Fate::InFlight).collect();
                if newest_first {
                    idx.reverse();
                }
                for i in idx {
                    self.deliver(i);
                }
            },
            Op::Ack(w) => {
                if let Some(i) = self.pick(w, |f| f.fate == Fate::InFlight && f.stored) {
                    self.settle(i, Fate::Done);
                }
            },
            Op::Lose(w) => {
                if let Some(i) = self.pick(w, |f| f.fate == Fate::InFlight) {
                    self.settle(i, Fate::Lost);
                }
            },
            Op::LateAck(w) => {
                if let Some(i) = self.pick(w, |f| f.fate == Fate::Lost && f.stored) {
                    self.settle(i, Fate::Done);
                }
            },
            Op::Read { stream, len } => self.read(usize::from(stream), len),
            Op::Control(carry) => self.control(carry),
        }
        if self.flight.len() > 64 {
            self.flight.retain(|f| f.fate != Fate::Done);
        }
    }

    fn done(&self) -> bool {
        self.plan.iter().all(|p| {
            p.id.is_some_and(|id| {
                let got = self.read.get(&id).map_or(0, Vec::len);
                got == p.len && self.ended.contains(&id)
            })
        })
    }

    /// One round of a clean link: everything goes, arrives in order, and is acknowledged or found missing.
    fn clean_round(&mut self) {
        self.open();
        for i in 0..self.plan.len() {
            self.write(i, usize::MAX / 2);
            self.finish(i, true);
        }
        self.send(64, 1200);
        for i in 0..self.flight.len() {
            if self.flight[i].fate == Fate::InFlight {
                self.flight[i].stored = false;
                self.deliver(i);
                let to = if self.flight[i].stored { Fate::Done } else { Fate::Lost };
                self.settle(i, to);
            }
        }
        self.flight.retain(|f| f.fate == Fate::InFlight);
        for i in 0..self.plan.len() {
            self.read(i, usize::MAX);
        }
        self.control(true);
    }
}

fn run(c: &Case) {
    let mut w = World::new(c);
    for (step, op) in c.ops.iter().enumerate() {
        let _ = step;
        w.step(op);
    }
    // Every frame still in flight is found lost (a spurious loss for those that arrived), then the link is clean.
    for i in 0..w.flight.len() {
        if w.flight[i].fate == Fate::InFlight {
            w.settle(i, Fate::Lost);
        }
    }
    w.flight.clear();
    let total: usize = c.plan.iter().map(|p| p.0).sum();
    let bound = 200 + 4 * total / 1200;
    let mut rounds = 0;
    while !w.done() {
        rounds += 1;
        assert!(
            rounds <= bound,
            "the transfer did not complete within {bound} clean rounds: read {:?} of {:?}, frames sent {}; pools in use {} / {}, buffered {}, views {:?}, limits {:?}",
            w.read.iter().map(|(k, v)| (*k, v.len())).collect::<Vec<_>>(),
            w.plan.iter().map(|p| (p.id, p.len, p.written, p.finished)).collect::<Vec<_>>(),
            w.sent_frames,
            w.spool.used_chunks(),
            w.rpool.used_chunks(),
            w.s.buffered(),
            w.plan.iter().filter_map(|p| p.id).map(|id| (w.s.send_view(id), w.r.recv_status(id))).collect::<Vec<_>>(),
            w.limit
        );
        w.clean_round();
    }
    for p in &w.plan {
        let id = p.id.unwrap();
        assert!(w.read.get(&id).map_or(&[][..], Vec::as_slice) == p.data, "stream {id}: the bytes read differ from those written");
    }
    // Once every stream ended, was read and acknowledged, every chunk is back in both pools.
    {
        for _ in 0..4 {
            w.clean_round();
        }
        assert!(!w.s.has_data_to_send(), "the sender still has data after every stream was acknowledged");
        assert_eq!(w.r.open_streams(), 0, "the receiver keeps streams that ended and were read");
        assert_eq!(w.s.open_streams(), 0, "the sender keeps streams that ended and were acknowledged");
        assert_eq!(w.rpool.used_chunks(), 0, "the receiver's pool holds chunks after every stream closed");
        assert_eq!(w.spool.used_chunks(), 0, "the sender's pool holds chunks after every stream closed");
    }
}

#[ephyra::test(gen = case(), tests = 600)]
fn streams_deliver_exactly_the_bytes_written(c: Case) {
    run(&c);
}

fn case_size(c: &Case) -> u64 {
    (c.ops.len() + c.plan.len() + c.plan.iter().map(|p| p.0).sum::<usize>() + c.rchunks + c.schunks) as u64
}

fn in_support(c: &Case) -> bool {
    c.rchunks >= 2 && c.schunks >= 2 && (1..=5).contains(&c.plan.len()) && c.ops.len() <= 150 && (1..=8).contains(&c.max_streams)
}

#[test]
fn the_stream_case_generator_and_shrinker_stay_in_support() {
    let cfg = ephyra::Config::default().tests(300);
    ephyra::check_generator(&cfg, case(), in_support).assert_passed();
    ephyra::check_shrinker(&cfg, case(), in_support, case_size).assert_passed();
}
