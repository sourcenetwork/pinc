//! The transport buffer pool, the datagram queues and the early-data buffer: accounting, bounds, drop policy and the
//! absence of per-operation allocation.
#![allow(
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_possible_truncation,
    clippy::too_many_lines
)]

use std::collections::VecDeque;

use proptest::prelude::*;
use pinc_tests::measure;
use pinc_transport::stream::datagram::{DatagramError, Datagrams, EarlyData, MAX_EARLY_PACKETS};
use pinc_transport::stream::pool::{BufferPool, CHUNK_SIZE, PoolExhausted};

pinc_tests::install_counting_allocator!();

#[test]
fn pool_exhausts_with_a_typed_result_and_recovers() {
    let mut pool = BufferPool::new_boxed(4);
    let chunks: Vec<_> = (0..4).map(|_| pool.alloc_chunk().unwrap()).collect();
    assert_eq!(pool.used_chunks(), 4);
    assert_eq!(pool.available_chunks(), 0);
    assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
    for c in chunks {
        pool.free_chunk(c);
    }
    assert_eq!(pool.used_chunks(), 0);
    assert_eq!(pool.available_chunks(), 4);
    let again: Vec<_> = (0..4).map(|_| pool.alloc_chunk().unwrap()).collect();
    assert_eq!(again.len(), 4);
    assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
}

#[test]
fn pool_charges_bytes_against_the_budget() {
    let mut slab = vec![[0u8; CHUNK_SIZE]; 8];
    let mut pool = BufferPool::from_slab(&mut slab);
    assert_eq!(pool.budget_bytes(), 8 * CHUNK_SIZE as u64);
    pool.set_budget_bytes(3 * CHUNK_SIZE as u64 + 5);
    assert_eq!(pool.budget_bytes(), 3 * CHUNK_SIZE as u64);
    let a = pool.alloc_chunk().unwrap();
    let b = pool.alloc_chunk().unwrap();
    assert_eq!(pool.used_bytes(), 2 * CHUNK_SIZE as u64);
    assert_eq!(pool.available_bytes(), CHUNK_SIZE as u64);
    let c = pool.alloc_chunk().unwrap();
    assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
    // Lowering the budget below the usage keeps the live chunks and refuses new ones.
    pool.set_budget_bytes(CHUNK_SIZE as u64);
    assert_eq!(pool.available_chunks(), 0);
    pool.free_chunk(a);
    pool.free_chunk(b);
    assert_eq!(pool.available_chunks(), 0);
    pool.free_chunk(c);
    assert_eq!(pool.available_chunks(), 1);
}

#[test]
fn chunks_are_distinct_and_keep_their_bytes() {
    let mut pool = BufferPool::new_boxed(3);
    let a = pool.alloc_chunk().unwrap();
    let b = pool.alloc_chunk().unwrap();
    pool.bytes_mut(&a).fill(0xAA);
    pool.bytes_mut(&b).fill(0xBB);
    assert!(pool.bytes(&a).iter().all(|&x| x == 0xAA));
    assert!(pool.bytes(&b).iter().all(|&x| x == 0xBB));
    assert_eq!(pool.bytes(&a).len(), CHUNK_SIZE);
    pool.free_chunk(a);
    let c = pool.alloc_chunk().unwrap();
    assert!(
        pool.bytes(&b).iter().all(|&x| x == 0xBB),
        "a free list must not touch live chunks"
    );
    pool.free_chunk(b);
    pool.free_chunk(c);
}

#[test]
fn alloc_and_free_do_not_allocate() {
    let mut pool = BufferPool::new_boxed(16);
    let stats = measure(|| {
        for _ in 0..100 {
            let a = pool.alloc_chunk().unwrap();
            let b = pool.alloc_chunk().unwrap();
            pool.free_chunk(a);
            pool.free_chunk(b);
        }
    });
    assert_eq!(stats.count(), 0);
}

#[test]
fn datagram_too_large_is_a_typed_error() {
    let mut pool = BufferPool::new_boxed(4);
    let mut dg = Datagrams::<4, 2>::new();
    assert_eq!(
        dg.send_datagram(&mut pool, &[0; 1201], 1200),
        Err(DatagramError::TooLarge { max_size: 1200 })
    );
    assert!(dg.send_datagram(&mut pool, &[7; 1200], 1200).is_ok());
    assert_eq!(dg.peek_send(&pool).unwrap().len(), 1200);
    assert_eq!(pool.used_chunks(), 1);
    assert_eq!(dg.send_dropped(), 0);
}

#[test]
fn full_send_queue_drops_the_oldest() {
    let mut pool = BufferPool::new_boxed(4);
    let mut dg = Datagrams::<3, 2>::new();
    for i in 0u8..5 {
        dg.send_datagram(&mut pool, &[i; 100], 1200).unwrap();
    }
    assert_eq!(dg.send_dropped(), 2);
    let mut seen = Vec::new();
    while let Some(d) = dg.peek_send(&pool) {
        seen.push(d[0]);
        dg.pop_send(&mut pool);
    }
    assert_eq!(seen, [2, 3, 4]);
    assert_eq!(pool.used_chunks(), 0, "an empty queue holds no chunk");
}

#[test]
fn full_receive_queue_drops_the_oldest_and_counts() {
    let mut pool = BufferPool::new_boxed(4);
    let mut dg = Datagrams::<2, 2>::new();
    for i in 0u8..4 {
        dg.on_datagram_frame(&mut pool, &[i; 10]);
    }
    assert_eq!(dg.recv_dropped(), 2);
    assert_eq!(dg.recv_datagram(pool.mem()).unwrap(), &[2; 10]);
    dg.release(&mut pool);
    assert_eq!(dg.recv_datagram(pool.mem()).unwrap(), &[3; 10]);
    dg.release(&mut pool);
    assert!(dg.recv_datagram(pool.mem()).is_none());
    assert_eq!(pool.used_chunks(), 0);
}

#[test]
fn datagrams_spanning_chunks_are_freed_as_the_head_moves() {
    let mut pool = BufferPool::new_boxed(8);
    let mut dg = Datagrams::<8, 4>::new();
    // Three 6000-byte datagrams do not fit in one 16 KiB chunk together: the third starts a second chunk.
    for i in 0u8..3 {
        dg.send_datagram(&mut pool, &[i; 6000], 6000).unwrap();
    }
    assert_eq!(pool.used_chunks(), 2);
    dg.pop_send(&mut pool);
    dg.pop_send(&mut pool);
    assert_eq!(pool.used_chunks(), 1);
    assert_eq!(dg.peek_send(&pool).unwrap(), &[2; 6000][..]);
    dg.pop_send(&mut pool);
    assert_eq!(pool.used_chunks(), 0);
}

#[test]
fn an_exhausted_pool_drops_old_datagrams_then_refuses() {
    let mut pool = BufferPool::new_boxed(1);
    let hog = pool.alloc_chunk().unwrap();
    let mut dg = Datagrams::<4, 2>::new();
    assert_eq!(
        dg.send_datagram(&mut pool, &[1; 10], 100),
        Err(DatagramError::Exhausted)
    );
    dg.on_datagram_frame(&mut pool, &[1; 10]);
    assert_eq!(dg.recv_dropped(), 1);
    pool.free_chunk(hog);
    assert!(dg.send_datagram(&mut pool, &[1; 10], 100).is_ok());
}

#[test]
fn early_data_holds_at_most_eight_packets() {
    let mut pool = BufferPool::new_boxed(16);
    let mut early = EarlyData::new();
    for i in 0..MAX_EARLY_PACKETS {
        assert!(early.push(&mut pool, &[i as u8; 1200]));
    }
    assert!(!early.push(&mut pool, &[99; 1200]));
    assert!(!early.push(&mut pool, &[98; 1200]));
    assert_eq!(early.dropped(), 2);
    for i in 0..MAX_EARLY_PACKETS {
        assert_eq!(early.front(&pool).unwrap(), &[i as u8; 1200][..]);
        early.pop(&mut pool);
    }
    assert!(early.front(&pool).is_none());
    assert_eq!(pool.used_chunks(), 0);
    assert!(early.push(&mut pool, &[1; 10]));
    early.clear(&mut pool);
    assert_eq!(pool.used_chunks(), 0);
}

#[test]
fn early_data_drops_when_the_pool_is_empty() {
    let mut pool = BufferPool::new_boxed(1);
    let hog = pool.alloc_chunk().unwrap();
    let mut early = EarlyData::new();
    assert!(!early.push(&mut pool, &[1; 10]));
    assert_eq!(early.dropped(), 1);
    pool.free_chunk(hog);
}

#[test]
fn datagram_and_early_paths_do_not_allocate() {
    let mut pool = BufferPool::new_boxed(8);
    let mut dg = Datagrams::<8, 4>::new();
    let mut early = EarlyData::new();
    let payload = [5u8; 1000];
    let stats = measure(|| {
        for _ in 0..200 {
            dg.send_datagram(&mut pool, &payload, 1200).unwrap();
            assert_eq!(dg.peek_send(&pool).unwrap().len(), 1000);
            dg.pop_send(&mut pool);
            dg.on_datagram_frame(&mut pool, &payload);
            assert_eq!(dg.recv_datagram(pool.mem()).unwrap().len(), 1000);
            dg.release(&mut pool);
            assert!(early.push(&mut pool, &payload));
            early.pop(&mut pool);
        }
    });
    assert_eq!(stats.count(), 0);
    assert_eq!(pool.used_chunks(), 0);
}

proptest! {
    /// The send queue behaves as a bounded FIFO that drops its oldest entry, and never leaks a chunk.
    #[test]
    fn datagram_queue_matches_a_model(ops in proptest::collection::vec((0u8..3, 0usize..3000), 1..200)) {
        let mut pool = BufferPool::new_boxed(8);
        let mut dg = Datagrams::<5, 3>::new();
        let mut model: VecDeque<Vec<u8>> = VecDeque::new();
        let mut dropped = 0u64;
        let mut tag = 0u8;
        for (op, len) in ops {
            if op < 2 {
                tag = tag.wrapping_add(1);
                let data = vec![tag; len];
                if dg.send_datagram(&mut pool, &data, 3000).is_ok() {
                    model.push_back(data);
                    // The chunk bound can drop more than the entry bound: mirror what the queue reports.
                    let reported = dg.send_dropped();
                    while dropped < reported {
                        model.pop_front();
                        dropped += 1;
                    }
                }
            } else if let Some(front) = dg.peek_send(&pool) {
                prop_assert_eq!(Some(front), model.front().map(Vec::as_slice));
                dg.pop_send(&mut pool);
                model.pop_front();
            } else {
                prop_assert!(model.is_empty());
            }
            prop_assert!(model.len() <= 5);
            prop_assert!(pool.used_chunks() <= 3);
        }
        while let Some(front) = dg.peek_send(&pool) {
            prop_assert_eq!(Some(front), model.front().map(Vec::as_slice));
            dg.pop_send(&mut pool);
            model.pop_front();
        }
        prop_assert!(model.is_empty());
        prop_assert_eq!(pool.used_chunks(), 0);
    }
}
