//! Trace generation for the datagram queues (`pinc-transport`, built with the `trace` feature): real
//! `Datagrams<4, 2>` and `Datagrams<64, 16>` over real pools of a few chunks, recorded as ndjson
//! (`dgram_queue.ndjson`) for the TLA+ trace check (`TraceDgramQueue.tla`).
//!
//! Datagrams of 0 bytes, 1, the lengths around the chunk size and seeded random ones are sent and received and
//! taken out; the queues are cleared; the test takes and gives back chunks of the pool itself and lowers and raises
//! its budget. After every call the record shows the two drop counters, the chunks the pool charges and the oldest
//! datagram of each queue (its length and its tag; every byte of a datagram is its tag).
//!
//! The test asserts what it can itself (every datagram read has the length and bytes it was offered with and the
//! queues keep the order, the counters never fall, an empty queue holds no chunk, the size limits), so it is
//! meaningful without the proof tools. It does not assert how the drop counters count a refusal: the code differs
//! from its documentation there, and the trace check replays both countings. The trace is written to
//! `PINC_TRACE_DIR` when it is set.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::too_many_lines,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::items_after_statements,
    unreachable_pub,
    clippy::struct_excessive_bools
)]

use std::fmt::Write as _;

use pinc_tests::SplitMix64;
use pinc_transport::stream::datagram::{DatagramError, Datagrams};
use pinc_transport::stream::pool::{BufferPool, CHUNK_SIZE, Chunk};

const LENS: [usize; 9] = [0, 1, 100, 8191, 8192, 8193, 16383, 16384, 16385];

/// What the runs exercised.
#[derive(Default)]
struct Seen {
    refused_by_pool: bool,
    send_made_room: bool,
    recv_made_room: bool,
    over_budget: bool,
}

/// One queue's order check: the datagrams offered, and how far the ones read have come.
#[derive(Default)]
struct Order {
    offered: Vec<(usize, u8)>,
    at: usize,
}

impl Order {
    fn read(&mut self, got: Option<&[u8]>) {
        let Some(d) = got else { return };
        let tag = d.first().copied().unwrap_or(0);
        assert!(d.iter().all(|b| *b == tag), "a datagram's bytes are not all its tag");
        let key = (d.len(), tag);
        if self.offered.get(self.at) == Some(&key) {
            return;
        }
        let j = self.offered[self.at.min(self.offered.len())..]
            .iter()
            .position(|o| *o == key)
            .expect("a datagram that was never offered, or one out of order");
        self.at += j;
    }
}

struct Run<'a, const Q: usize, const C: usize> {
    dg: Datagrams<Q, C>,
    pool: BufferPool<'static>,
    held: Vec<Chunk>,
    pools: usize,
    budget: usize,
    seq: usize,
    sorder: Order,
    rorder: Order,
    sd: u64,
    rd: u64,
    out: &'a mut String,
    seen: &'a mut Seen,
}

/// `[len, first byte or 0]` of a datagram, `[]` for none.
fn front(d: Option<&[u8]>) -> String {
    d.map_or_else(
        || "[]".to_owned(),
        |d| format!("[{},{}]", d.len(), d.first().copied().unwrap_or(0)),
    )
}

impl<const Q: usize, const C: usize> Run<'_, Q, C> {
    fn view(&mut self) -> String {
        let (s, r) = (self.dg.peek_send(&self.pool), self.dg.recv_datagram(&self.pool));
        self.sorder.read(s);
        self.rorder.read(r);
        let (sf, rf) = (front(s), front(r));
        let (sd, rd) = (self.dg.send_dropped(), self.dg.recv_dropped());
        assert!(sd >= self.sd && rd >= self.rd, "a drop counter fell");
        (self.sd, self.rd) = (sd, rd);
        if s.is_none() && r.is_none() {
            assert_eq!(self.pool.used_chunks(), self.held.len(), "an empty queue holds a chunk");
        }
        format!(
            r#"{{"sd":{sd},"rd":{rd},"used":{},"sf":{sf},"rf":{rf}}}"#,
            self.pool.used_chunks()
        )
    }

    fn log(&mut self, body: &str) {
        let v = self.view();
        let _ = writeln!(self.out, r#"{{"t":"dgram",{body},"v":{v}}}"#);
    }

    fn init(&mut self) {
        let p = self.pools;
        self.log(&format!(r#""op":"init","q":{Q},"c":{C},"p":{p}"#));
    }

    /// A datagram of `len` bytes: its tag and its bytes.
    fn make(&mut self, len: usize) -> (u8, Vec<u8>) {
        let tag = if len == 0 { 0 } else { 1 + (self.seq % 250) as u8 };
        self.seq += 1;
        (tag, vec![tag; len])
    }

    fn free_under_budget(&self) -> bool {
        self.pool.used_chunks() < self.budget
    }

    fn send(&mut self, len: usize, max: usize) {
        let (tag, data) = self.make(len);
        let free = self.free_under_budget();
        let sd = self.dg.send_dropped();
        let r = self.dg.send_datagram(&mut self.pool, &data, max);
        let want_large = len > max || len > CHUNK_SIZE;
        assert_eq!(matches!(r, Err(DatagramError::TooLarge { .. })), want_large);
        if let Err(DatagramError::TooLarge { max_size }) = r {
            assert_eq!(max_size, if len > max { max } else { CHUNK_SIZE });
        }
        assert!(
            !(free && r == Err(DatagramError::Exhausted)),
            "refused with a chunk free"
        );
        self.seen.refused_by_pool |= r == Err(DatagramError::Exhausted);
        self.seen.send_made_room |= r.is_ok() && self.dg.send_dropped() > sd;
        if r.is_ok() {
            self.sorder.offered.push((len, tag));
        }
        let (res, limit) = match r {
            Ok(()) => ("ok", String::new()),
            Err(DatagramError::TooLarge { max_size }) => ("toolarge", format!(r#","limit":{max_size}"#)),
            Err(DatagramError::Exhausted) => ("exhausted", String::new()),
        };
        self.log(&format!(
            r#""op":"send","len":{len},"tag":{tag},"max":{max},"res":"{res}"{limit}"#
        ));
    }

    fn recv(&mut self, len: usize) {
        let (tag, data) = self.make(len);
        let free = self.free_under_budget();
        let rd = self.dg.recv_dropped();
        self.dg.on_datagram_frame(&mut self.pool, &data);
        // a datagram the queue may hold is offered; one it dropped on arrival is never read, which the order allows
        self.rorder.offered.push((len, tag));
        self.seen.recv_made_room |= free && len <= CHUNK_SIZE && self.dg.recv_dropped() > rd;
        self.log(&format!(r#""op":"recv","len":{len},"tag":{tag}"#));
    }

    fn pop_send(&mut self) {
        self.dg.pop_send(&mut self.pool);
        self.log(r#""op":"pop_send""#);
    }

    fn release(&mut self) {
        self.dg.release(&mut self.pool);
        self.log(r#""op":"release""#);
    }

    fn clear(&mut self) {
        self.dg.clear(&mut self.pool);
        self.log(r#""op":"clear""#);
        assert_eq!(
            self.pool.used_chunks(),
            self.held.len(),
            "a cleared queue holds a chunk"
        );
    }

    fn take(&mut self) {
        let ok = match self.pool.alloc_chunk() {
            Ok(c) => {
                self.held.push(c);
                true
            }
            Err(_) => false,
        };
        self.log(&format!(r#""op":"take","ok":{ok}"#));
    }

    /// Give back the last chunk taken; nothing when the test holds none.
    fn give(&mut self) {
        if let Some(c) = self.held.pop() {
            self.pool.free_chunk(c);
            self.log(r#""op":"give""#);
        }
    }

    fn budget(&mut self, b: usize) {
        self.seen.over_budget |= b < self.pool.used_chunks();
        self.pool.set_budget_bytes((b * CHUNK_SIZE) as u64);
        self.budget = b.min(self.pools);
        self.log(&format!(r#""op":"budget","b":{b}"#));
    }

    /// Pop each queue until it shows nothing: at most `Q` pops each; then one more of each.
    fn drain(&mut self) {
        let mut n = 0;
        while self.dg.peek_send(&self.pool).is_some() {
            self.pop_send();
            n += 1;
            assert!(n <= Q, "more than Q sends came out");
        }
        n = 0;
        while self.dg.recv_datagram(&self.pool).is_some() {
            self.release();
            n += 1;
            assert!(n <= Q, "more than Q datagrams were received");
        }
        self.pop_send();
        self.release();
    }
}

fn run<const Q: usize, const C: usize>(
    out: &mut String,
    seen: &mut Seen,
    pools: usize,
    body: impl FnOnce(&mut Run<'_, Q, C>),
) {
    let mut r = Run::<Q, C> {
        dg: Datagrams::new(),
        pool: BufferPool::new_boxed(pools),
        held: Vec::new(),
        pools,
        budget: pools,
        seq: 0,
        sorder: Order::default(),
        rorder: Order::default(),
        sd: 0,
        rd: 0,
        out,
        seen,
    };
    r.init();
    body(&mut r);
}

fn seeded<const Q: usize, const C: usize>(r: &mut Run<'_, Q, C>, rng: &mut SplitMix64) {
    let mut below = |n: usize| (rng.next_u64() % n as u64) as usize;
    for _ in 0..200 {
        let op = below(100);
        let mut len = || {
            if below(2) == 0 { LENS[below(9)] } else { below(16386) }
        };
        match op {
            0..=34 => {
                let l = len();
                let max = if below(10) == 0 { below(16386) } else { CHUNK_SIZE };
                r.send(l, max);
            }
            35..=69 => {
                let l = len();
                r.recv(l);
            }
            70..=79 => r.pop_send(),
            80..=89 => r.release(),
            90..=92 => r.take(),
            93..=95 => {
                if r.held.is_empty() {
                    r.take();
                } else {
                    r.give();
                }
            }
            96..=97 => {
                let b = below(r.pools + 1);
                r.budget(b);
            }
            _ => r.clear(),
        }
    }
}

#[test]
fn the_datagram_queues_match_the_model() {
    let mut rng = SplitMix64::traced(0x6467_7271);
    let (mut out, mut seen) = (String::new(), Seen::default());

    // 1. boundary lengths on both queues, then drained
    run::<4, 2>(&mut out, &mut seen, 3, |r| {
        r.send(0, CHUNK_SIZE);
        r.send(16384, CHUNK_SIZE);
        r.send(1, CHUNK_SIZE);
        r.send(16385, 20000);
        r.send(100, 50);
        for _ in 0..4 {
            r.send(8192, CHUNK_SIZE);
        }
        for l in [0, 16384, 1, 8192, 8192, 8192, 8192] {
            r.recv(l);
        }
        r.drain();
    });

    // 2. a pool the test empties itself
    run::<4, 2>(&mut out, &mut seen, 2, |r| {
        r.take();
        r.take();
        r.send(1, CHUNK_SIZE);
        r.recv(1);
        r.give();
        r.send(1, CHUNK_SIZE);
        r.recv(1);
        r.take();
        r.give();
        r.give();
        r.clear();
    });

    // 3. a budget lowered under what is charged
    run::<4, 2>(&mut out, &mut seen, 4, |r| {
        r.recv(8192);
        r.recv(8192);
        r.budget(0);
        r.recv(1);
        r.budget(4);
        r.send(8192, CHUNK_SIZE);
        r.send(8192, CHUNK_SIZE);
        r.budget(0);
        r.send(1, CHUNK_SIZE);
        r.budget(4);
        r.send(1, CHUNK_SIZE);
        r.clear();
    });

    // 4. seeded runs
    for _ in 0..20 {
        run::<4, 2>(&mut out, &mut seen, 4, |r| seeded(r, &mut rng));
    }
    for _ in 0..40 {
        run::<64, 16>(&mut out, &mut seen, 16, |r| seeded(r, &mut rng));
    }

    assert!(seen.refused_by_pool, "no send was refused by the pool");
    assert!(
        seen.send_made_room,
        "no datagram was dropped from the send queue to make room"
    );
    assert!(
        seen.recv_made_room,
        "no datagram was dropped from the receive queue to make room"
    );
    assert!(seen.over_budget, "no call ran with the budget below what was charged");
    if let Ok(dir) = std::env::var("PINC_TRACE_DIR") {
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(std::path::Path::new(&dir).join("dgram_queue.ndjson"), &out).unwrap();
    }
}
