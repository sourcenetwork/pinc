//! Shared helpers for the PINC tests.
//!
//! The tests themselves are the `[[test]]` targets of this package (`tests/*.rs`); this library holds what several of
//! them use.

mod connect_client;
mod connect_host;
mod connect_relay_node;
mod connect_world;
mod core_net;
mod forge;
mod layer_apps;
mod link;
mod mbt;
mod node_sim;
mod route;
mod swtpm;
pub use connect_client::*;
pub use connect_host::*;
pub use connect_relay_node::*;
pub use connect_world::*;
pub use core_net::*;
pub use forge::*;
mod pair;
pub use layer_apps::*;
pub use link::*;
pub use mbt::*;
pub use node_sim::*;
pub use pair::*;
pub use route::*;
#[cfg(feature = "hwenc")]
pub use swtpm::Swtpm;

/// The number in the environment variable `PINC_TRACE_SEED`, mixed; zero when it is unset or not a number.
fn trace_salt() -> u64 {
    std::env::var("PINC_TRACE_SEED")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .map_or(0, |n| SplitMix64::new(n).next_u64())
}

/// Whether the trace tests run under a shifted seed (`PINC_TRACE_SEED` is set). A trace test's "the runs reach every
/// branch" assertions describe its fixed seeds only, so they are skipped then; the recorded trace is still written and
/// still checked against the models, which is the point of the soak.
pub fn soaking() -> bool {
    trace_salt() != 0
}

/// A small deterministic pseudo-random generator (`SplitMix64`) for reproducible test inputs.
///
/// Tests use it instead of a global random source, so a failing case reproduces from its seed.
#[derive(Debug, Clone)]
pub struct SplitMix64(u64);

impl SplitMix64 {
    /// A generator starting from `seed`.
    pub fn new(seed: u64) -> Self {
        Self(seed)
    }

    /// A generator for a trace test (see [`soaking`]): `seed`, unless the environment variable `PINC_TRACE_SEED` is set to a number, in
    /// which case every seed of every trace test is moved by it (the soak script `scripts/trace-soak.sh` does this to
    /// record runs the fixed seeds never produce). Unset, it is exactly `new(seed)`, so the gate's runs do not change.
    pub fn traced(seed: u64) -> Self {
        Self::new(seed ^ trace_salt())
    }

    /// The next 64-bit value.
    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// Fill `buf` with pseudo-random bytes.
    pub fn fill(&mut self, buf: &mut [u8]) {
        for chunk in buf.chunks_mut(8) {
            let v = self.next_u64().to_le_bytes();
            let n = chunk.len();
            chunk.copy_from_slice(v.get(..n).unwrap_or(&[]));
        }
    }
}

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;

thread_local! {
    // Const-initialised and drop-free, so touching them from inside the allocator never allocates.
    static ALLOCS: Cell<u64> = const { Cell::new(0) };
    static REALLOCS: Cell<u64> = const { Cell::new(0) };
    static BYTES: Cell<u64> = const { Cell::new(0) };
}

fn bump(counter: &'static std::thread::LocalKey<Cell<u64>>, by: u64) {
    counter.with(|c| c.set(c.get() + by));
}

/// A global allocator that delegates to the system allocator and counts, per thread, the allocations,
/// reallocations and bytes requested. Install it with [`install_counting_allocator!`].
#[derive(Debug)]
pub struct CountingAlloc;

// SAFETY: every method forwards its arguments unchanged to `System`, which upholds the `GlobalAlloc` contract; the
// counters are thread-local `Cell`s that never allocate.
#[allow(unsafe_code)]
unsafe impl GlobalAlloc for CountingAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        bump(&ALLOCS, 1);
        bump(&BYTES, layout.size() as u64);
        unsafe { System.alloc(layout) }
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        bump(&ALLOCS, 1);
        bump(&BYTES, layout.size() as u64);
        unsafe { System.alloc_zeroed(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        bump(&REALLOCS, 1);
        bump(&BYTES, new_size as u64);
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

/// Install [`CountingAlloc`] as the global allocator of a test target; [`measure`] needs it.
#[macro_export]
macro_rules! install_counting_allocator {
    () => {
        #[global_allocator]
        static COUNTING_ALLOCATOR: $crate::CountingAlloc = $crate::CountingAlloc;
    };
}

/// What the allocator counted on the current thread.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct AllocStats {
    /// Calls to `alloc` and `alloc_zeroed`.
    pub allocs: u64,
    /// Calls to `realloc`.
    pub reallocs: u64,
    /// Bytes requested by all of them.
    pub bytes: u64,
}

impl AllocStats {
    /// Allocations plus reallocations: zero means the code never touched the heap.
    pub fn count(&self) -> u64 {
        self.allocs + self.reallocs
    }

    /// What the allocator has counted on the current thread so far.
    pub fn now() -> Self {
        Self {
            allocs: ALLOCS.with(Cell::get),
            reallocs: REALLOCS.with(Cell::get),
            bytes: BYTES.with(Cell::get),
        }
    }
}

/// Run `f` and return what this thread allocated meanwhile.
///
/// # Panics
///
/// Panics if the test target did not install the counting allocator, since every count would read zero.
#[allow(clippy::panic)]
pub fn measure(f: impl FnOnce()) -> AllocStats {
    let probe = AllocStats::now();
    drop(std::hint::black_box(Box::new(0u8)));
    assert!(
        AllocStats::now() != probe,
        "the counting allocator is not installed: add `pinc_tests::install_counting_allocator!();` to the test target"
    );
    let before = AllocStats::now();
    f();
    let after = AllocStats::now();
    AllocStats {
        allocs: after.allocs - before.allocs,
        reallocs: after.reallocs - before.reallocs,
        bytes: after.bytes - before.bytes,
    }
}

/// The secrets of the broadcast id tables of the test nodes, full width as the key store draws them.
pub static MAP_SECRETS: [u64; 7] = [
    0x9e37_79b9_7f4a_7c15,
    0xbf58_476d_1ce4_e5b9,
    0x94d0_49bb_1331_11eb,
    0x2545_f491_4f6c_dd1d,
    0xd6e8_feb8_6659_fd93,
    0xff51_afd7_ed55_8ccd,
    0xc4ce_b9fe_1a85_ec53,
];

/// The id key of a test node with `seed`, over [`MAP_SECRETS`].
#[allow(
    clippy::unwrap_used,
    clippy::missing_panics_doc,
    reason = "the secrets are fixed and nonzero"
)]
pub fn id_key(seed: u64) -> pinc_broadcast::IdKey {
    pinc_broadcast::IdKey::new(seed, &MAP_SECRETS).unwrap()
}
