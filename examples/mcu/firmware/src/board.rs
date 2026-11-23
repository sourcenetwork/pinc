//! The board: its clock, the serial line to the debug probe's virtual COM port, and the stack's high-water mark.
//!
//! NUCLEO-H7S3L8: USART3 on PD8 (TX) and PD9 (RX) reaches the ST-LINK's virtual COM port. The clocks are the boot
//! stage's to set (`pinc_mcu_link::clock`); this program only counts on them.

use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU32, AtomicUsize, Ordering};

use stm32_metapac::{self as pac, interrupt};

use pinc_mcu_link::clock::PERIPHERAL_HZ;
pub(crate) use pinc_mcu_link::clock::{BAUD, CORE_HZ};

/// The clock: core cycles counted since [`init`], and the cycle counter's value when they were last counted. The
/// counter has 32 bits and wraps every 67 s; the main loop reads the clock far more often than that.
struct Clock(UnsafeCell<(u64, u32)>);
// SAFETY: only `now` touches it, with interrupts off.
unsafe impl Sync for Clock {}
static CLOCK: Clock = Clock(UnsafeCell::new((0, 0)));

/// Bytes received and not yet read. The interrupt handler writes at `HEAD`; the main loop reads at `TAIL`.
const RX_LEN: usize = 16384;
struct Ring(UnsafeCell<[u8; RX_LEN]>);
// SAFETY: one writer (the USART3 handler) and one reader (the main loop) that never touch the same place: the writer
// stops one place short of `TAIL` and the reader stops at `HEAD`.
unsafe impl Sync for Ring {}
static RX: Ring = Ring(UnsafeCell::new([0; RX_LEN]));
static HEAD: AtomicUsize = AtomicUsize::new(0);
static TAIL: AtomicUsize = AtomicUsize::new(0);
/// Bytes lost: the receiver overran, or the ring was full.
pub(crate) static RX_LOST: AtomicU32 = AtomicU32::new(0);

#[interrupt]
fn USART3() {
    if pac::USART3.isr().read().ore() {
        pac::USART3.icr().write(|w| w.set_ore(true));
        RX_LOST.fetch_add(1, Ordering::Relaxed);
    }
    // Everything the receiver's FIFO holds, so a handler that started late still finds its bytes.
    while pac::USART3.isr().read().rxne() {
        #[allow(clippy::cast_possible_truncation, reason = "the data register holds eight bits")]
        let byte = pac::USART3.rdr().read().dr() as u8;
        let head = HEAD.load(Ordering::Relaxed);
        let next = (head + 1) % RX_LEN;
        if next == TAIL.load(Ordering::Acquire) {
            RX_LOST.fetch_add(1, Ordering::Relaxed);
        } else {
            // SAFETY: `head` is below `RX_LEN`, and the reader does not read this place until `HEAD` moves past it.
            unsafe { RX.0.get().cast::<u8>().add(head).write_volatile(byte) };
            HEAD.store(next, Ordering::Release);
        }
    }
}

/// Close the address space no memory of this program answers, before the data cache is on.
///
/// With the data cache on, the core fills cache lines ahead of loads it has not decided to make, at whatever address
/// the bytes ahead of it spell. On this chip such a read of the graphics unit's range (`0x2500_0000` to
/// `0x25FF_FFFF`) stops the chip, the debug port with it; ST names it for an erratum (community thread 159810) and
/// says to keep every unused range closed.
///
/// Six regions, a later one over an earlier: the 64 MiB below the main RAM are closed and the 64 KiB of the DTCM RAM
/// at their start opened again; the 64 MiB from the main RAM up are closed and its first 512 KiB opened again; the
/// space of memories outside the chip (`0x6000_0000` to `0xDFFF_FFFF`) is closed and the 32 MiB of the
/// flash the image runs from opened again. Everything else keeps the default map.
fn close_unused_memory(mpu: &mut cortex_m::peripheral::MPU) {
    /// No access, never executed.
    const CLOSED: u32 = 1 << 28;
    /// Full access, cached.
    const OPEN: u32 = (0b011 << 24) | (1 << 17) | (1 << 16);
    /// The size field of a region of `2^bits` bytes, and the region on.
    const fn size(bits: u32) -> u32 {
        ((bits - 1) << 1) | 1
    }
    let regions = [
        // Below the stack, so that a stack that outgrows its room is a fault the handler reports: left to the default
        // map, a write there is one more access that nothing answers.
        (0x2000_0000, CLOSED | size(26)),
        (0x2000_0000, OPEN | CLOSED | size(16)),
        (0x2400_0000, CLOSED | size(26)),
        (0x2400_0000, OPEN | CLOSED | size(19)),
        // The whole space in eight parts of 512 MiB, of which the fourth to the seventh take part.
        (0x0000_0000, CLOSED | (0x87 << 8) | size(32)),
        (0x7000_0000, OPEN | size(25)),
    ];
    // SAFETY: every address this program uses keeps the access it had; the RAM stays not executable, as nothing runs
    // from it.
    unsafe {
        mpu.ctrl.write(0);
        for (n, (base, attributes)) in (0u32..).zip(regions) {
            mpu.rnr.write(n);
            mpu.rbar.write(base);
            mpu.rasr.write(attributes);
        }
        // On, with the default map wherever no region is.
        mpu.ctrl.write(0b101);
    }
    cortex_m::asm::dsb();
    cortex_m::asm::isb();
}

/// Turn the caches on, and start the cycle counter and the serial line.
pub(crate) fn init(mut core: cortex_m::Peripherals) {
    close_unused_memory(&mut core.MPU);
    // The image runs in place from a serial flash: without the instruction cache every fetch waits for the flash.
    core.SCB.enable_icache();
    core.SCB.enable_dcache(&mut core.CPUID);

    // The serial line is disabled while it is set up; the boot stage left it on.
    pac::USART3.cr1().write(|_| {});
    pac::RCC.ahb4enr().modify(|w| w.set_gpioden(true));
    pac::RCC.apb1enr1().modify(|w| w.set_usart3en(true));
    let _ = pac::RCC.apb1enr1().read();

    // PD8 and PD9 to alternate function 7 (USART3).
    for pin in [8, 9] {
        pac::GPIOD
            .moder()
            .modify(|w| w.set_moder(pin, pac::gpio::vals::Moder::ALTERNATE));
        pac::GPIOD.afr(1).modify(|w| w.set_afr(pin - 8, 7));
    }
    pac::USART3.brr().write(|w| w.set_brr((PERIPHERAL_HZ / BAUD) as u16));
    pac::USART3.cr1().write(|w| {
        w.set_te(true);
        w.set_re(true);
        w.set_rxneie(true);
        w.set_fifoen(true);
        w.set_ue(true);
    });
    // SAFETY: the handler above is the only user of what it touches besides `read`, which is written for it.
    unsafe { cortex_m::peripheral::NVIC::unmask(pac::Interrupt::USART3) };

    core.DCB.enable_trace();
    // A probe that was ever told to stop the core at a fault leaves that order in the core until its power goes; with
    // it the core halts at a fault and the handler never says what happened.
    // SAFETY: clears one bit of the debug control register, which only decides whether a fault halts the core.
    unsafe { core.DCB.demcr.modify(|r| r & !(1 << 10)) };
    // SAFETY: the unlock only lets the cycle counter be switched on.
    unsafe { core.DWT.lar.write(0xC5AC_CE55) };
    core.DWT.enable_cycle_counter();
}

/// Nanoseconds since [`init`], plus one second: the endpoint's clock, to a core cycle.
pub(crate) fn now() -> u64 {
    let cycles = cortex_m::interrupt::free(|_| {
        // SAFETY: interrupts are off and no handler reads the clock, so this is the only access.
        let clock = unsafe { &mut *CLOCK.0.get() };
        let count = cortex_m::peripheral::DWT::cycle_count();
        clock.0 += u64::from(count.wrapping_sub(clock.1));
        clock.1 = count;
        clock.0
    });
    1_000_000_000 + cycles * 1000 / u64::from(CORE_HZ / 1_000_000)
}

/// Thirty-two bytes from the chip's random generator (its analog noise source, conditioned as the chip leaves reset),
/// or `None` when the generator reports a fault or gives nothing.
pub(crate) fn random_seed() -> Option<[u8; 32]> {
    // The generator runs from the 48 MHz internal oscillator, its clock source after reset.
    pac::RCC.cr().modify(|w| w.set_hsi48on(true));
    while !pac::RCC.cr().read().hsi48rdy() {}
    pac::RCC.ahb3enr().modify(|w| w.set_rngen(true));
    let _ = pac::RCC.ahb3enr().read();
    pac::RNG.cr().modify(|w| w.set_rngen(true));
    let mut seed = [0u8; 32];
    for word in seed.as_chunks_mut::<4>().0 {
        let mut tries = 0u32;
        loop {
            let sr = pac::RNG.sr().read();
            if sr.seis() || sr.ceis() || sr.secs() || sr.cecs() {
                return None;
            }
            if sr.drdy() {
                break;
            }
            tries += 1;
            if tries > 10_000_000 {
                return None;
            }
        }
        *word = pac::RNG.dr().read().to_le_bytes();
    }
    // A generator that is stuck gives the same word again and again.
    let words = seed.as_chunks::<4>().0;
    (words.iter().any(|w| *w != [0; 4]) && words.windows(2).any(|w| w[0] != w[1])).then_some(seed)
}

/// The next byte the line delivered.
pub(crate) fn read() -> Option<u8> {
    let tail = TAIL.load(Ordering::Relaxed);
    if tail == HEAD.load(Ordering::Acquire) {
        return None;
    }
    // SAFETY: `tail` is below `RX_LEN`, and the handler wrote this place before it moved `HEAD` past it.
    let byte = unsafe { RX.0.get().cast::<u8>().add(tail).read_volatile() };
    TAIL.store((tail + 1) % RX_LEN, Ordering::Release);
    Some(byte)
}

/// Send bytes, waiting for the transmitter.
pub(crate) fn write(bytes: &[u8]) {
    for &b in bytes {
        while !pac::USART3.isr().read().txe() {}
        pac::USART3.tdr().write(|w| w.set_dr(u16::from(b)));
    }
}

/// What the unused stack is filled with.
const PAINT: u32 = 0x5AFE_C0DE;

unsafe extern "C" {
    static mut _stack_end: u32;
    static _stack_start: u32;
    static __image_start: u32;
    static __erodata: u32;
    static __sdata: u32;
    static __edata: u32;
    static __sbss: u32;
    static __ebss: u32;
}

/// Fill the stack below the caller's frame, so [`stack_peak`] can tell how deep it went. Call once, early.
#[inline(never)]
pub(crate) fn paint_stack() {
    let here = cortex_m::register::msp::read() as usize - 256;
    let mut p = &raw mut _stack_end;
    // SAFETY: the words from the stack's lower end to 256 bytes below the stack pointer hold no live frame.
    unsafe {
        while (p as usize) < here {
            p.write_volatile(PAINT);
            p = p.add(1);
        }
    }
}

/// The most bytes of stack in use at once since [`paint_stack`].
pub(crate) fn stack_peak() -> usize {
    let top = &raw const _stack_start as usize;
    let mut p = &raw const _stack_end;
    // SAFETY: the scan stays inside the stack's region and reads plain words.
    unsafe {
        while (p as usize) < top && p.read_volatile() == PAINT {
            p = p.add(1);
        }
    }
    top - p as usize
}

/// The room the stack has.
pub(crate) fn stack_size() -> usize {
    &raw const _stack_start as usize - &raw const _stack_end as usize
}

/// The image's bytes: code and constants, and the initial values of the statics that have any.
pub(crate) fn image_len() -> usize {
    (&raw const __erodata as usize - &raw const __image_start as usize)
        + (&raw const __edata as usize - &raw const __sdata as usize)
}

/// The statics' bytes: those with initial values, and those that start as zeroes.
pub(crate) fn statics_len() -> usize {
    (&raw const __edata as usize - &raw const __sdata as usize)
        + (&raw const __ebss as usize - &raw const __sbss as usize)
}
