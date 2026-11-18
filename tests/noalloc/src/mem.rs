//! The static storage: the buffer pool chunks of every session slot of both endpoints.
//!
//! Invariants: the slabs are handed out once, as one exclusive borrow; the program runs on one thread and never
//! calls [`take`] from an interrupt.
#![allow(unsafe_code, reason = "one exclusive borrow of a static, taken once")]

use core::sync::atomic::{AtomicBool, Ordering};

use vinc_transport::stream::pool::{CHUNK_SIZE, RawChunk};

/// Session slots of one endpoint.
pub(crate) const SLOTS: usize = 2;
/// Pool chunks of one session slot (16 KiB each).
pub(crate) const CHUNKS: usize = 32;
/// The slabs of both endpoints.
pub(crate) type Slabs = [[RawChunk; CHUNKS]; 2 * SLOTS];

static mut SLABS: Slabs = [[[0; CHUNK_SIZE]; CHUNKS]; 2 * SLOTS];
static TAKEN: AtomicBool = AtomicBool::new(false);

/// The slabs, the first time; `None` after.
pub(crate) fn take() -> Option<&'static mut Slabs> {
    // One `swap` where the target has compare-and-swap on a byte, so the host test is sound on any thread. Where it
    // has none, load then store: the program runs in one context and takes its storage once.
    #[cfg(target_has_atomic = "8")]
    let taken = TAKEN.swap(true, Ordering::Relaxed);
    #[cfg(not(target_has_atomic = "8"))]
    let taken = {
        let t = TAKEN.load(Ordering::Relaxed);
        TAKEN.store(true, Ordering::Relaxed);
        t
    };
    if taken {
        return None;
    }
    // SAFETY: the flag above lets this borrow exist once, so nothing else reaches the static.
    unsafe { (&raw mut SLABS).as_mut() }
}
