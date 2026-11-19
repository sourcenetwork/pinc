//! Shared helpers for the `transport_stream*` test targets: the table and pool setup, readers and drains, and a
//! source-backed stream source.
//!
//! Included with `#[path]`; not a test target itself.
#![allow(
    dead_code,
    unreachable_pub,
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation
)]

use std::cell::RefCell;

use pinc_tests::SplitMix64;
use pinc_transport::stream::pool::BufferPool;
use pinc_transport::stream::{Config, ControlFrame, NoSource, PeerLimits, StreamChunk, StreamSource, Streams};

pub const MIB: u64 = 1 << 20;
/// A send buffer cap that never binds.
pub const NO_CAP: u64 = u64::MAX;
pub type Table = Streams<NoSource, 8, 1025>;

pub fn peer() -> PeerLimits {
    PeerLimits {
        window: 5 * MIB / 4,
        max_streams: 100,
    }
}

/// A server-side table over a heap pool of `chunks` chunks.
pub fn setup(chunks: usize, edit: impl FnOnce(&mut Config)) -> (BufferPool<'static>, Box<Table>) {
    let pool = BufferPool::new_boxed(chunks);
    let mut config = Config::new(false);
    config.peer = peer();
    // These tests exercise the pool and window rules on their own; the stream credit has its own tests.
    config.credit = false;
    edit(&mut config);
    let table = Box::new(Table::new(&config, &pool));
    (pool, table)
}

/// A server-side table with the stream credit on, over a heap pool of `chunks` chunks.
pub fn setup_credit(chunks: usize, edit: impl FnOnce(&mut Config)) -> (BufferPool<'static>, Box<Table>) {
    setup(chunks, |c| {
        c.credit = true;
        edit(c);
    })
}

/// The next control frame, the stream-credit raises (see the credit tests) left out.
pub fn next_control<S: StreamSource, const N: usize, const C: usize>(t: &mut Streams<S, N, C>) -> Option<ControlFrame> {
    std::iter::from_fn(|| t.pending_control()).find(|f| !matches!(f, ControlFrame::MaxStreams { .. }))
}

pub fn pattern(len: usize, seed: u64) -> Vec<u8> {
    let mut v = vec![0u8; len];
    SplitMix64::new(seed).fill(&mut v);
    v
}

/// Read and consume everything readable on `id`.
pub fn read_all<S: StreamSource, const N: usize, const C: usize>(
    t: &mut Streams<S, N, C>,
    pool: &mut BufferPool<'_>,
    id: u64,
) -> Vec<u8> {
    let mut out = Vec::new();
    while let Some(chunk) = t.read_chunk(pool, id) {
        let n = chunk.len();
        out.extend_from_slice(chunk);
        t.consume(pool, id, n, 0, 0).unwrap();
    }
    out
}

/// Every control frame the table wants to send, the stream-credit raises left out (see `credit_raises`).
pub fn drain_control(t: &mut Table) -> Vec<ControlFrame> {
    std::iter::from_fn(|| t.pending_control())
        .filter(|f| !matches!(f, ControlFrame::MaxStreams { .. }))
        .collect()
}

/// Build every frame the table wants to send now, copying out the data.
pub fn drain_frames(t: &mut Table, pool: &BufferPool<'_>, budget: usize) -> Vec<(StreamChunk, Vec<u8>)> {
    let mut frames = Vec::new();
    while let Some(chunk) = t.next_stream_frame(budget) {
        let mut buf = vec![0u8; chunk.len];
        assert_eq!(t.copy_out(pool, &chunk, &mut buf).unwrap(), chunk.len);
        frames.push((chunk, buf));
    }
    frames
}

#[derive(Debug)]
pub struct Src<'a> {
    pub data: &'a [u8],
    pub log: &'a RefCell<Vec<(u64, usize)>>,
}

impl StreamSource for Src<'_> {
    fn read_at(&mut self, offset: u64, dst: &mut [u8]) -> usize {
        self.log.borrow_mut().push((offset, dst.len()));
        let start = offset as usize;
        let n = dst.len().min(self.data.len().saturating_sub(start));
        dst[..n].copy_from_slice(&self.data[start..start + n]);
        n
    }
}
