//! The node-wide loss estimate and the tail-repair decision.
//!
//! The estimate is an exponentially weighted average in units of 1/65536 with gain 1/32, stepped once per packet: an
//! acknowledged packet does `v -= v >> 5`, a lost one does `v += (65536 - v) >> 5`. It is kept in one atomic so every
//! connection of an endpoint shares it by reference without a lock. Only packets that need an acknowledgement count,
//! and repair packets and path MTU probes are left out (the caller passes only the packets that count).
//!
//! A target without 32-bit compare-and-swap (the Cortex-M0 class) keeps the value in a plain cell instead, so there
//! the estimate is not `Sync` and an endpoint and its connections stay in one context, which is how the core is driven.
//!
//! Invariant: the value is always in `0..=65536`. Both steps have a fixed point (below 32 for the decay, above 65504
//! for the growth), so a batch of any size costs at most a few hundred steps.

use super::SECOND;

#[cfg(target_has_atomic = "32")]
use core::sync::atomic::{AtomicU32, Ordering};

/// The scale of the estimate: 65536 means every packet was lost.
pub const SCALE: u32 = 65_536;
/// Tail repair needs an estimate of at least this (328/65536, about 0.5 %).
pub const REPAIR_THRESHOLD: u32 = 328;
/// A connection must be at least this old (2 s) before it repairs its tail.
pub const REPAIR_MIN_AGE: u64 = 2 * SECOND;
/// The averaging gain is 1/2^`GAIN_SHIFT` (1/32).
const GAIN_SHIFT: u32 = 5;

/// The estimate after a batch: `acked` acknowledged packets, then `lost` lost ones, each as its own step.
fn step(old: u32, lost: u32, acked: u32) -> u32 {
    let mut v = old;
    for _ in 0..acked {
        let next = v - (v >> GAIN_SHIFT);
        if next == v {
            break;
        }
        v = next;
    }
    for _ in 0..lost {
        let next = v + ((SCALE - v) >> GAIN_SHIFT);
        if next == v {
            break;
        }
        v = next;
    }
    v
}

/// The value cell: an atomic updated by compare-and-swap where the target has one.
#[cfg(target_has_atomic = "32")]
#[derive(Debug, Default)]
struct Word(AtomicU32);

#[cfg(target_has_atomic = "32")]
impl Word {
    const fn new() -> Self {
        Self(AtomicU32::new(0))
    }

    fn get(&self) -> u32 {
        self.0.load(Ordering::Relaxed)
    }

    fn set(&self, v: u32) {
        self.0.store(v, Ordering::Relaxed);
    }

    fn update(&self, lost: u32, acked: u32) {
        // The closure always returns `Some`, so the update cannot fail; ignoring the result is safe.
        let _ = self
            .0
            .try_update(Ordering::Relaxed, Ordering::Relaxed, |old| Some(step(old, lost, acked)));
    }
}

/// The value cell of a target without compare-and-swap: read, step, write, in one context. Built under test on every
/// target so the host can compare it with the atomic one.
#[cfg(any(test, not(target_has_atomic = "32")))]
#[derive(Debug, Default)]
struct CellWord(core::cell::Cell<u32>);

#[cfg(any(test, not(target_has_atomic = "32")))]
impl CellWord {
    const fn new() -> Self {
        Self(core::cell::Cell::new(0))
    }

    fn get(&self) -> u32 {
        self.0.get()
    }

    fn set(&self, v: u32) {
        self.0.set(v);
    }

    fn update(&self, lost: u32, acked: u32) {
        self.0.set(step(self.0.get(), lost, acked));
    }
}

#[cfg(not(target_has_atomic = "32"))]
type Word = CellWord;

/// The shared loss average of an endpoint.
#[derive(Debug, Default)]
pub struct LossEstimate {
    value: Word,
}

impl LossEstimate {
    /// An estimate of zero loss.
    pub const fn new() -> Self {
        Self { value: Word::new() }
    }

    /// Forget every packet seen: the estimate of a new endpoint, for memory that is handed on to the next one.
    pub fn reset(&self) {
        self.value.set(0);
    }

    /// The current estimate in units of 1/65536.
    pub fn get(&self) -> u32 {
        self.value.get()
    }

    /// Fold in a batch: `acked` acknowledged packets, then `lost` lost ones, each as its own step.
    pub fn record(&self, lost: u32, acked: u32) {
        if lost == 0 && acked == 0 {
            return;
        }
        self.value.update(lost, acked);
    }

    /// Whether to repair the tail: the connection is at least 2 s old, its send queue just drained, the path is a
    /// direct one and the estimate is at least 328/65536.
    pub fn should_send_repair(&self, conn_age: u64, queue_drained: bool, on_direct_path: bool) -> bool {
        queue_drained && on_direct_path && conn_age >= REPAIR_MIN_AGE && self.get() >= REPAIR_THRESHOLD
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used, reason = "tests assert")]
mod tests {
    use super::*;

    /// The step written out plainly: the same two loops, one packet at a time.
    fn model(mut v: u32, lost: u32, acked: u32) -> u32 {
        for _ in 0..acked {
            v -= v >> 5;
        }
        for _ in 0..lost {
            v += (65_536 - v) >> 5;
        }
        v
    }

    /// A value in `0..n` from a xorshift stream.
    fn below(s: &mut u64, n: u32) -> u32 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        u32::try_from(*s % u64::from(n)).unwrap()
    }

    #[test]
    fn the_cell_word_and_the_atomic_word_step_alike_and_match_the_model() {
        let mut seed = 0x9E37_79B9_7F4A_7C15_u64;
        let starts = [0, 31, 32, 65_504, 65_505, 65_536];
        for n in 0..10_000_usize {
            let start = starts
                .get(n % (starts.len() + 2))
                .copied()
                .unwrap_or_else(|| below(&mut seed, 65_537));
            let (a, c) = (Word::new(), CellWord::new());
            a.set(start);
            c.set(start);
            // A few batches from each start, so the values wander.
            let mut want = start;
            for _ in 0..4 {
                let lost = below(&mut seed, 71);
                let acked = below(&mut seed, 71);
                a.update(lost, acked);
                c.update(lost, acked);
                want = model(want, lost, acked);
                assert_eq!(
                    c.get(),
                    a.get(),
                    "the two words differ after ({lost}, {acked}) from {start}"
                );
                assert_eq!(
                    c.get(),
                    want,
                    "the cell word differs from the model after ({lost}, {acked}) from {start}"
                );
            }
        }
    }
}
