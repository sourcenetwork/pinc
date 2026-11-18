//! What a bare-metal target needs from the program: a panic handler and an entry symbol.
#![allow(
    unsafe_code,
    reason = "the entry symbol must be unmangled; nothing else here is unsafe"
)]

use crate::drive::drive;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}

/// The entry symbol: runs the exchange once. It is the root the linker keeps the whole endpoint reachable from.
#[unsafe(no_mangle)]
pub(crate) extern "C" fn _start() -> ! {
    // A bare program has nowhere to report; the host build and its test read the result.
    let _ = drive();
    loop {}
}
