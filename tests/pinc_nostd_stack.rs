//! The stack a host without an executor needs: the example host (`examples/platform.rs`) builds two endpoints,
//! connects, echoes 64 bytes and closes on a thread whose stack is set, and the smallest stack it runs on is found by
//! halving until a run fails. A stack that is too small kills the process, so each size runs in a child process: this
//! binary run again for its `child` test, with the size in the environment.
//!
//! The figures are those of this 64-bit build host, not of a microcontroller; what a 32-bit target needs is not
//! measured yet. The optimised build and the `unoptimised` profile (every crate at opt-level 0) differ a great deal,
//! so each has its own ceiling.
#![allow(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::indexing_slicing,
    dead_code,
    missing_docs,
    unreachable_pub
)]

use std::process::Command;

#[path = "../crates/pinc/examples/platform.rs"]
mod platform;

/// The environment variable that carries the stack size, in KiB, to the child.
const KIB: &str = "PINC_STACK_KIB";
/// The largest stack tried, in KiB.
const START: usize = 8192;
/// The most stack the run may need, in KiB, as a power of two: it runs on 1024 KiB and fails on 512 KiB.
const STACK_MAX: usize = 1024;
/// The same in an `unoptimised` build: it runs on 1024 KiB and fails on 512 KiB there too.
const STACK_UNOPTIMISED_MAX: usize = 1024;

/// The child: with a size in the environment, run the example on a thread of that stack; without one, nothing.
#[test]
fn child() {
    let Ok(kib) = std::env::var(KIB) else { return };
    let kib: usize = kib.parse().unwrap();
    let echoed = std::thread::Builder::new()
        .stack_size(kib << 10)
        .spawn(|| platform::run(&[0x5a; 64]).unwrap())
        .unwrap()
        .join()
        .unwrap();
    assert_eq!(echoed, [0x5a; 64]);
}

/// Whether the run completes on a stack of `kib` KiB: the child ran its test and it passed.
fn runs_on(kib: usize) -> bool {
    let out = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", "child", "--nocapture", "--test-threads", "1"])
        .env(KIB, kib.to_string())
        .output()
        .unwrap();
    out.status.success() && String::from_utf8_lossy(&out.stdout).contains("1 passed")
}

#[test]
fn the_smallest_stack_a_host_without_an_executor_runs_on_is_measured() {
    let unoptimised = std::env::current_exe()
        .unwrap()
        .components()
        .any(|c| c.as_os_str() == "unoptimised");
    let max = if unoptimised { STACK_UNOPTIMISED_MAX } else { STACK_MAX };
    assert!(runs_on(START), "the run does not complete on {START} KiB");
    let mut kib = START;
    while kib > 8 && runs_on(kib / 2) {
        kib /= 2;
    }
    let build = if unoptimised { "unoptimised" } else { "optimised" };
    println!(
        "{build} build on the 64-bit build host: runs on {kib} KiB, fails on {} KiB",
        kib / 2
    );
    assert!(kib <= max, "the run needs {kib} KiB, above {max}");
}
