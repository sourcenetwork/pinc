use alloc::vec::Vec;

use super::super::{BufferPool, CHUNK_SIZE, Chunk, PoolExhausted};
use super::{OWN_CHUNKS, SEGMENT_CHUNKS, SEGMENT_DECAY, Segments};

/// The segment sizes the grown pool is tested with: one chunk (wasm, 32-bit), a few, and the mapped segment.
const SEGS: [usize; 3] = [1, 4, SEGMENT_CHUNKS];

/// More chunks than a pool keeps on their own: a session that takes them needs a segment.
const PAST_OWN: usize = OWN_CHUNKS + 1;

/// A segment of chunks no system can reserve: a pool asking for one is refused.
const REFUSED: usize = isize::MAX as usize / CHUNK_SIZE + 1;

#[test]
fn a_grown_pool_makes_a_chunk_when_it_is_first_needed_and_never_more_than_its_budget() {
    for seg in SEGS {
        let cap = 35;
        let mut pool = BufferPool::new_grown_in(cap, seg);
        assert_eq!((pool.held_chunks(), pool.available_chunks()), (0, cap));
        let mut held = Vec::new();
        for i in 0..cap {
            held.push(pool.alloc_chunk().unwrap());
            assert_eq!(pool.held_chunks(), i + 1, "after chunk {i}");
        }
        assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
        assert_eq!((pool.held_chunks(), pool.available_chunks()), (cap, 0));
        // Each chunk is its own memory.
        for (i, ch) in held.iter().enumerate() {
            pool.bytes_mut(ch).fill(u8::try_from(i).unwrap());
        }
        for (i, ch) in held.iter().enumerate() {
            let v = u8::try_from(i).unwrap();
            assert!(pool.bytes(ch).len() == CHUNK_SIZE && pool.bytes(ch).iter().all(|x| *x == v));
        }
        // A returned chunk is handed out again; nothing new is made for it.
        let last = held.pop().unwrap();
        pool.free_chunk(last);
        let again = pool.alloc_chunk().unwrap();
        assert!(pool.bytes(&again).iter().all(|x| usize::from(*x) == cap - 1));
        assert_eq!(pool.held_chunks(), cap);
    }
}

#[test]
fn a_grown_pool_frees_its_chunks_when_it_is_reset() {
    for seg in SEGS {
        let mut pool = BufferPool::new_grown_in(64, seg);
        let held: Vec<Chunk> = (0..17).map(|_| pool.alloc_chunk().unwrap()).collect();
        assert_eq!(pool.held_chunks(), 17);
        drop(held);
        pool.reset();
        assert_eq!(
            (pool.held_chunks(), pool.used_chunks(), pool.available_chunks()),
            (0, 0, 64)
        );
        // The pool is as new: it makes each chunk again as it hands it out.
        let again: Vec<Chunk> = (0..64).map(|_| pool.alloc_chunk().unwrap()).collect();
        assert_eq!((again.len(), pool.held_chunks()), (64, 64));
        assert_eq!(pool.alloc_chunk(), Err(PoolExhausted));
    }
}

#[test]
fn a_grown_pool_keeps_returned_chunks_until_a_trim() {
    for seg in SEGS {
        let mut pool = BufferPool::new_grown_in(64, seg);
        let mut held: Vec<Chunk> = (0..20).map(|_| pool.alloc_chunk().unwrap()).collect();
        assert_eq!(pool.held_chunks(), 20);
        // Returned chunks keep their memory, so a busy session allocates nothing for the chunks it reuses.
        for _ in 0..10 {
            pool.free_chunk(held.pop().unwrap());
        }
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (10, 20));
        let again: Vec<Chunk> = (0..10).map(|_| pool.alloc_chunk().unwrap()).collect();
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (20, 20));
        // A trim frees every segment with no chunk in use, never one with a chunk in use.
        for ch in held.drain(..).chain(again) {
            pool.free_chunk(ch);
        }
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (0, 20));
        pool.trim();
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (0, 0));
        let in_use: Vec<Chunk> = (0..5).map(|_| pool.alloc_chunk().unwrap()).collect();
        pool.trim();
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (5, 5));
        // A chunk handed out after a trim has its memory, whole.
        assert!(in_use.iter().all(|c| pool.bytes(c).len() == CHUNK_SIZE));
    }
}

#[test]
fn a_trim_keeps_a_segment_with_a_chunk_in_use_and_frees_the_others_whole() {
    for seg in SEGS {
        let mut pool = BufferPool::new_grown_in(64, seg);
        let mut held: Vec<Chunk> = (0..20).map(|_| pool.alloc_chunk().unwrap()).collect();
        for ch in &held {
            pool.bytes_mut(ch).fill(0xa5);
        }
        // The first chunk of the first segment stays in use; the 19 others come back.
        let first = held.remove(OWN_CHUNKS);
        for ch in held.drain(..) {
            pool.free_chunk(ch);
        }
        pool.trim();
        // Its segment keeps the memory of every chunk of it handed out (at most `seg`, and the 20 less the chunks of
        // their own); every other segment, and every chunk of its own, is freed.
        let kept = seg.min(20 - OWN_CHUNKS);
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (1, kept), "seg {seg}");
        assert!(pool.bytes(&first).iter().all(|x| *x == 0xa5));
        pool.free_chunk(first);
        pool.trim();
        assert_eq!((pool.used_chunks(), pool.held_chunks()), (0, 0));
        // A freed segment's memory is gone: a chunk handed out again comes from new, zeroed memory.
        let again: Vec<Chunk> = (0..20).map(|_| pool.alloc_chunk().unwrap()).collect();
        assert!(again.iter().all(|c| pool.bytes(c).iter().all(|x| *x == 0)));
    }
}

/// A pool of `SEGMENT_CHUNKS` chunks a segment that takes its segments from `spare`.
fn shared(spare: &Segments) -> BufferPool<'static> {
    let mut p = BufferPool::new_grown_in(64, SEGMENT_CHUNKS);
    p.share_segments(spare);
    p
}

/// Hand out `n` chunks of every pool of `pools` at once, each filled with `fill`, then take them back and trim each:
/// sessions busy together that go quiet.
fn burst_with(pools: &mut [BufferPool<'static>], n: usize, fill: u8) {
    let held: Vec<Vec<Chunk>> = pools
        .iter_mut()
        .map(|p| {
            (0..n)
                .map(|_| {
                    let c = p.alloc_chunk().unwrap();
                    p.bytes_mut(&c).fill(fill);
                    c
                })
                .collect()
        })
        .collect();
    for (p, chunks) in pools.iter_mut().zip(held) {
        for c in chunks {
            p.free_chunk(c);
        }
        p.trim();
    }
}

fn burst(pools: &mut [BufferPool<'static>], n: usize) {
    burst_with(pools, n, 0x11);
}

#[test]
fn a_pool_maps_no_segment_for_its_first_chunks() {
    // What a session holds at once to shake hands and move a first byte each way: the handshake gives its chunk back
    // before the stream takes one (`a_session_that_shakes_hands_and_moves_a_first_byte_maps_no_segment`).
    const HELLO: usize = 1;
    if SEGMENT_CHUNKS == 1 {
        return;
    }
    let spare = Segments::new();
    let mut a = [shared(&spare)];
    // Such a session maps no segment: none goes spare when it is quiet.
    burst(&mut a, HELLO);
    assert_eq!((a[0].held_chunks(), spare.kept()), (0, 0));
    // A session that takes more takes a segment, which goes spare when it is quiet.
    burst(&mut a, HELLO.max(PAST_OWN));
    assert_eq!((a[0].held_chunks(), spare.kept()), (0, 1));
}

#[test]
fn a_quiet_pool_frees_its_segment_to_the_spares_and_the_next_pool_takes_it() {
    let spare = Segments::new();
    let mut a = [shared(&spare)];
    // However much of it the session wrote, its segment stays spare: nothing goes to the system on a trim.
    burst(&mut a, 40);
    assert_eq!((a[0].held_chunks(), spare.kept()), (0, 1));
    let mut b = shared(&spare);
    let c: Vec<Chunk> = (0..PAST_OWN).map(|_| b.alloc_chunk().unwrap()).collect();
    assert_eq!((b.held_chunks(), spare.kept()), (PAST_OWN, 0));
    drop(c);
    b.reset();
    assert_eq!(spare.kept(), 1);
}

#[test]
fn a_segment_that_passes_to_another_session_shows_nothing_of_the_last_one() {
    let spare = Segments::new();
    // A session writes its secret into 40 chunks and goes quiet: its segment is spare, with the secret in it.
    let mut a = [shared(&spare)];
    burst_with(&mut a, 40, 0xa5);
    assert_eq!(spare.kept(), 1);
    // Another session takes the segment: every chunk it is handed reads as zeros, wherever the chunk lies.
    let mut b = shared(&spare);
    let held: Vec<Chunk> = (0..40).map(|_| b.alloc_chunk().unwrap()).collect();
    assert_eq!(spare.kept(), 0);
    for c in &held {
        assert!(
            b.bytes(c).iter().all(|x| *x == 0),
            "a chunk of the next session holds the last session's bytes"
        );
    }
    // The same for the next session of the same slot: a reset makes the pool a new session.
    drop(held);
    b.reset();
    burst_with(&mut a, 40, 0xa5);
    a[0].reset();
    let mut c = a;
    for _ in 0..2 {
        let held: Vec<Chunk> = (0..40).map(|_| c[0].alloc_chunk().unwrap()).collect();
        assert!(held.iter().all(|h| c[0].bytes(h).iter().all(|x| *x == 0)));
        drop(held);
        c[0].reset();
    }
}

#[test]
fn a_session_that_takes_its_own_segment_back_keeps_what_it_wrote() {
    if SEGMENT_CHUNKS == 1 {
        return;
    }
    let spare = Segments::new();
    let mut a = [shared(&spare)];
    burst_with(&mut a, 40, 0xa5);
    // The session takes its own segment back: nothing is cleared or committed again, so the first chunk of the segment
    // still holds what the session wrote there.
    let held: Vec<Chunk> = (0..PAST_OWN).map(|_| a[0].alloc_chunk().unwrap()).collect();
    assert_eq!(spare.kept(), 0);
    let seg = held.iter().find(|c| c.index() >= OWN_CHUNKS).unwrap();
    assert!(a[0].bytes(seg).iter().all(|x| *x == 0xa5));
}

#[test]
fn a_refused_segment_falls_back_to_chunks_of_their_own_and_is_counted() {
    let spare = Segments::new();
    let mut pool = BufferPool::new_grown_in(64, REFUSED);
    pool.share_segments(&spare);
    // The pool's first segment cannot be reserved: the refusal is counted once, and the session's chunks are each an
    // allocation of their own, whole and apart.
    let held: Vec<Chunk> = (0..40).map(|_| pool.alloc_chunk().unwrap()).collect();
    assert_eq!((spare.refused(), pool.held_chunks()), (1, 40));
    for (i, c) in held.iter().enumerate() {
        pool.bytes_mut(c).fill(u8::try_from(i).unwrap());
    }
    for (i, c) in held.iter().enumerate() {
        let v = u8::try_from(i).unwrap();
        assert!(pool.bytes(c).len() == CHUNK_SIZE && pool.bytes(c).iter().all(|x| *x == v));
    }
    // Quiet, it frees them to the allocator: nothing goes spare. The next session tries a segment again.
    for c in held {
        pool.free_chunk(c);
    }
    pool.trim();
    assert_eq!((pool.held_chunks(), spare.kept()), (0, 0));
    pool.reset();
    let again: Vec<Chunk> = (0..PAST_OWN).map(|_| pool.alloc_chunk().unwrap()).collect();
    assert_eq!((spare.refused(), again.len()), (2, PAST_OWN));
}

#[test]
fn nothing_leaves_the_spares_before_the_timer_and_a_burst_takes_back_what_it_freed() {
    let spare = Segments::new();
    let mut pools: Vec<BufferPool<'static>> = (0..8).map(|_| shared(&spare)).collect();
    // A burst: 8 sessions busy at once, then quiet.
    burst(&mut pools, PAST_OWN);
    let n = if SEGMENT_CHUNKS == 1 { 0 } else { 8 };
    assert_eq!(spare.kept(), n);
    if n == 0 {
        return;
    }
    // Before the deadline an expiry frees nothing; 8 new sessions take the 8 segments back.
    let due = spare.deadline(1_000).unwrap();
    assert_eq!(due, 1_000 + SEGMENT_DECAY);
    spare.expire(due - 1);
    assert_eq!(spare.kept(), 8);
    let held: Vec<Vec<Chunk>> = pools
        .iter_mut()
        .map(|p| (0..PAST_OWN).map(|_| p.alloc_chunk().unwrap()).collect())
        .collect();
    assert_eq!(spare.kept(), 0);
    // With nothing spare there is no deadline, and asking again changes nothing.
    assert_eq!(spare.deadline(2_000), None);
    for (p, c) in pools.iter_mut().zip(held) {
        for c in c {
            p.free_chunk(c);
        }
        p.trim();
    }
    assert_eq!(spare.kept(), 8);
    // The deadline, once asked, stays where it was however often and however late it is asked: the node keeps it.
    let due = spare.deadline(3_000).unwrap();
    assert_eq!((spare.deadline(3_001), spare.deadline(due)), (Some(due), Some(due)));
}

#[test]
fn the_timer_frees_only_the_segments_no_session_took_for_a_whole_period() {
    if SEGMENT_CHUNKS == 1 {
        return;
    }
    let spare = Segments::new();
    let mut pools: Vec<BufferPool<'static>> = (0..4).map(|_| shared(&spare)).collect();
    // Four sessions busy at once, then quiet.
    burst(&mut pools, PAST_OWN);
    assert_eq!(spare.kept(), 4);
    // The first expiry after the segments were freed keeps them: they were not spare for a whole period.
    let t1 = spare.deadline(0).unwrap();
    spare.expire(t1);
    assert_eq!(spare.kept(), 4);
    // In the next period one session at a time takes a segment and frees it again: one segment was needed, three
    // were not, and the expiry frees those three.
    let t2 = spare.deadline(t1).unwrap();
    assert_eq!(t2, t1 + SEGMENT_DECAY);
    burst(pools.get_mut(..1).unwrap(), PAST_OWN);
    burst(pools.get_mut(1..2).unwrap(), PAST_OWN);
    spare.expire(t2);
    assert_eq!(spare.kept(), 1);
    // A quiet period after that frees the last one, and the cache asks for no timer.
    let t3 = spare.deadline(t2).unwrap();
    spare.expire(t3);
    assert_eq!((spare.kept(), spare.deadline(t3)), (0, None));
}

#[test]
fn a_grown_pool_and_a_flat_one_behave_alike() {
    for seg in SEGS.into_iter().chain([REFUSED]) {
        // The same script of takes, writes, returns, trims and resets gives the same handles, the same counts, the
        // same refusals and the same bytes, whether the grown pool shares its segments with another pool or not.
        let spare = Segments::new();
        let mut other = BufferPool::new_grown_in(21, seg);
        let (mut grown, mut flat) = (BufferPool::new_grown_in(21, seg), BufferPool::new_boxed(21));
        if seg > 1 {
            grown.share_segments(&spare);
            other.share_segments(&spare);
        }
        let (mut held_grown, mut held_flat) = (Vec::new(), Vec::new());
        let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
        for step in 0..4000_u32 {
            seed = seed
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            let r = seed >> 33;
            if r.is_multiple_of(97) {
                // The session ends: both pools start a new one with every chunk dead.
                held_grown.clear();
                held_flat.clear();
                grown.reset();
                flat.reset();
                // Another session takes and frees a segment in between.
                burst_with(core::slice::from_mut(&mut other), PAST_OWN + 2, 0xee);
            } else if r.is_multiple_of(17) {
                grown.trim();
                assert!(grown.held_chunks() >= grown.used_chunks());
            } else if !r.is_multiple_of(3) || held_grown.is_empty() {
                let (a, b) = (grown.alloc_chunk(), flat.alloc_chunk());
                assert_eq!(a.is_ok(), b.is_ok());
                if let (Ok(a), Ok(b)) = (a, b) {
                    assert_eq!(a, b);
                    let tag = step.to_le_bytes();
                    grown.bytes_mut(&a)[..4].copy_from_slice(&tag);
                    flat.bytes_mut(&b)[..4].copy_from_slice(&tag);
                    held_grown.push(a);
                    held_flat.push(b);
                }
            } else {
                let i = usize::try_from(seed >> 40).unwrap() % held_grown.len();
                let (a, b) = (held_grown.swap_remove(i), held_flat.swap_remove(i));
                assert_eq!(grown.bytes(&a)[..4], flat.bytes(&b)[..4], "seg {seg}");
                grown.free_chunk(a);
                flat.free_chunk(b);
            }
            assert_eq!(
                (grown.used_chunks(), grown.available_chunks(), grown.budget_bytes()),
                (flat.used_chunks(), flat.available_chunks(), flat.budget_bytes())
            );
        }
    }
}
