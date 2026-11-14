//! Memory across runs: the same world run again and again in one process holds the same live heap after every run,
//! because a restarted node reuses the connection table of its previous incarnation and a finished run gives its
//! tables back. The scenario is S13; what is measured is the allocator's own live bytes (allocated minus freed),
//! which other processes cannot move, and never the resident size, which the kernel moves whenever the host is
//! under memory pressure. The numbers print with `--nocapture`.
#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::indexing_slicing,
    clippy::cast_precision_loss
)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

use vinc_sim::Driver;
use vinc_sim::suite::run::{LayerSet, run};
use vinc_sim::suite::world::{build, variants};

static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

/// A global allocator that forwards to the system allocator and keeps the process-wide live bytes and their peak. The
/// shared counting allocator of the test support counts per thread and never frees, so it cannot give a live figure.
struct Live;

fn grow(by: usize) {
    let now = LIVE.fetch_add(by, Relaxed) + by;
    PEAK.fetch_max(now, Relaxed);
}

// SAFETY: every method forwards its arguments unchanged to `System`, which upholds the `GlobalAlloc` contract; the
// counters are atomics and never allocate.
#[allow(unsafe_code)]
unsafe impl GlobalAlloc for Live {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(l) };
        if !p.is_null() {
            grow(l.size());
        }
        p
    }
    unsafe fn alloc_zeroed(&self, l: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(l) };
        if !p.is_null() {
            grow(l.size());
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size(), Relaxed);
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, new: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, l, new) };
        if !q.is_null() {
            LIVE.fetch_sub(l.size(), Relaxed);
            grow(new);
        }
        q
    }
}

#[global_allocator]
static ALLOCATOR: Live = Live;

/// The resident set of this process in bytes (Linux), printed for information only.
fn resident() -> u64 {
    let statm = std::fs::read_to_string("/proc/self/statm").unwrap();
    statm.split_whitespace().nth(1).unwrap().parse::<u64>().unwrap() * 4096
}

/// How many times the world is run.
const RUNS: usize = 12;
/// How much one run may add to the live bytes over the run before it. Measured: the live bytes of this world differ
/// from one run to the next by a toggle of about 180 KB (the buffer pools and the recycled-table maps of the run
/// thread, each bounded) and a drift of about 0.5 KB per run; a run that keeps its connection tables adds about 3 GB.
const STEP: usize = 512 << 10;
/// How much the live bytes after the last run may exceed those after the first in all: well above the toggle, and
/// below what a leak of even 30 KB per run adds over eleven runs.
const TOTAL: usize = 256 << 10;

#[test]
fn a_rerun_world_does_not_grow_the_process() {
    let v = variants().into_iter().find(|v| v.id == "S13").unwrap();
    let world = build(&v).unwrap();
    let mut live = Vec::new();
    for _ in 0..RUNS {
        assert!(run(&world, Driver::Vinc, LayerSet::NODE).unwrap().ran);
        live.push(LIVE.load(Relaxed));
        println!(
            "live {} peak {} resident {}",
            live[live.len() - 1],
            PEAK.load(Relaxed),
            resident()
        );
    }
    // A leak adds to the live bytes at every run, so every run ends above the one before it by the same step.
    for (n, w) in live.windows(2).enumerate() {
        let step = w[1].saturating_sub(w[0]);
        assert!(step <= STEP, "run {} holds {step} more bytes than run {}", n + 2, n + 1);
    }
    let total = live[RUNS - 1].saturating_sub(live[0]);
    assert!(total <= TOTAL, "the live bytes grew by {total} over {RUNS} runs");
}
