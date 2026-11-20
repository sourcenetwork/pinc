//! Unit tests of the stream table over an endpoint's chunk store.

use super::*;
use crate::stream::store::{ChunkStore, floor_chunks};

/// A window is granted only once the store has reserved it (a grant it has no room for waits in the store's queue), so
/// a session that then takes every chunk the store will give it cannot take the chunks that window's data needs: all
/// of it is stored and none is held back (`shortage_backed` stays 0). Granted against the soft room instead, the
/// window's last frames found no chunk.
#[test]
fn a_granted_window_keeps_its_chunks_when_another_session_takes_the_rest_of_the_store() {
    let floor = floor_chunks(64);
    let mut store = ChunkStore::new(8 * floor, 2, 64);
    let (mut pa, mut pb) = (BufferPool::over_store(0, 64), BufferPool::over_store(1, 64));
    let mut cfg = Config::new(false);
    // The opening window is the floor: everything past it is a window `grant` gave.
    cfg.initial_stream_window = floor as u64 * CHUNK_SIZE as u64;
    let mut t: Streams<NoSource, 8, 65> = Streams::new(&cfg, &pa);
    let block = [5u8; CHUNK_SIZE];
    let step = CHUNK_SIZE as u64;

    // Each round fills the window and drains it within a round trip, so the next window is twice the last.
    pa.lend_store(core::mem::take(&mut store));
    let (mut off, mut limit, mut now) = (0, cfg.initial_stream_window, 0);
    while limit - off <= step * floor as u64 {
        while off < limit {
            t.on_stream_frame(&mut pa, 0, off, &block, false).unwrap();
            off += step;
        }
        now += 1_000;
        while let Some(k) = t.read_chunk(pa.mem(), 0).map(<[u8]>::len) {
            t.consume(&mut pa, 0, k, now, 1_000).unwrap();
        }
        limit = t.stream_recv_window(0).unwrap().1;
        assert!(now < 10_000, "the window stopped growing at {limit}");
    }
    store = pa.return_store();

    pb.lend_store(core::mem::take(&mut store));
    let mut held = alloc::vec::Vec::new();
    while let Ok(c) = pb.alloc_chunk() {
        held.push(c);
    }
    store = pb.return_store();
    assert!(held.len() > floor, "b took burst room too");

    pa.lend_store(core::mem::take(&mut store));
    while off < limit {
        let n = (limit - off).min(step) as usize;
        let r = t.on_stream_frame(&mut pa, 0, off, block.get(..n).unwrap(), false);
        assert_eq!(r, Ok(()), "the frame at {off} of a window granted up to {limit}");
        off += n as u64;
    }
    store = pa.return_store();
    assert_eq!(store.stats().shortage_backed, 0);
}
