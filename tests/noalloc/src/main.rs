//! A program with no allocator: two endpoints on caller storage that shake hands and move one stream between them.
//!
//! It exists to be linked. For a bare-metal target (`just no-std`) it is `no_std` and `no_main` with no global
//! allocator, so a crate on the path from the endpoint down that reaches the heap fails the link. On the host it runs
//! the same exchange and exits with a failure when it does not complete, and its test does the same. Packets pass
//! between the two endpoints by hand, the sans-IO way; no socket and no clock is read.
//!
//! Invariants: nothing here or below allocates; every table lives in the static slabs of `mem` or in the frame of
//! `drive::drive`; the exchange runs once per process.
#![cfg_attr(any(target_os = "none", target_arch = "wasm32"), no_std, no_main)]

mod drive;
mod mem;

#[cfg(any(target_os = "none", target_arch = "wasm32"))]
mod bare;

#[cfg(not(any(target_os = "none", target_arch = "wasm32")))]
fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(stage) => {
            eprintln!("the exchange stopped at {stage:?}");
            std::process::ExitCode::FAILURE
        }
    }
}

/// The exchange on a thread with room for it: the endpoints live in the frame, as on a target whose stack is sized
/// for them.
#[cfg(not(any(target_os = "none", target_arch = "wasm32")))]
fn run() -> Result<(), drive::Stage> {
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(drive::drive)
        .map_or(Err(drive::Stage::Setup), |t| {
            t.join().unwrap_or(Err(drive::Stage::Setup))
        })
}

#[cfg(test)]
mod tests {
    #[test]
    fn two_endpoints_on_static_storage_move_a_stream() {
        assert_eq!(super::run(), Ok(()));
        // The storage is handed out once: a second exchange in this process finds it taken.
        assert_eq!(super::run(), Err(super::drive::Stage::Storage));
    }
}
