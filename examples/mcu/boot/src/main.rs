//! The boot stage of the NUCLEO-H7S3L8.
//!
//! The STM32H7S3L8 has 64 KiB of flash of its own; a program of any size lives in the board's external flash, a
//! Macronix MX25UW25645G (32 MiB) on the XSPI2 interface (port N), and runs in place from there. This stage does what
//! must be done before that: it powers and clocks the interface, puts the flash in a known state, maps it for reading
//! at `0x7000_0000` and starts the image whose vector table is at that address.
//!
//! The flash is mapped in its octal mode (eight data lines, one transfer per clock, the `0xEC13` read) at 53 or
//! 64 MHz, so code is fetched at 53 or 64 MB/s. It is erased and programmed in its power-up mode, on one data line.
//!
//! The core's clock is this stage's to set, because the flash interface runs from it and the image runs from the
//! flash: as the chip leaves reset (64 MHz), or 320 MHz from the PLL with the `fast-clock` feature
//! (`pinc_mcu_link::clock`).
//!
//! It is also the loader. For half a second after it starts it listens on the serial line for a request to load
//! (`pinc_mcu_link::load`); when one comes it erases, programs and checks the flash as the laptop asks, one request
//! and one answer at a time, until it is told to go.
#![no_std]
#![no_main]

use core::fmt::Write as _;

use cortex_m_rt::entry;
use pinc_mcu_link::clock::{BAUD, BUS_HZ, CORE_HZ, PERIPHERAL_HZ};
use pinc_mcu_link::frame::{Deframer, encode, encoded_max};
use pinc_mcu_link::{kind, load};
use stm32_metapac::{self as pac, gpio, xspi};

/// Where the external flash is mapped.
const IMAGE: u32 = 0x7000_0000;
/// The fastest the flash is clocked. The board's lines carry it without the pads' high-speed mode, which is an option
/// byte this stage leaves alone.
const FLASH_HZ: u32 = 64_000_000;

/// A line of text for the laptop, in the image's framing.
struct Line {
    buf: [u8; 120],
    len: usize,
}

impl Line {
    fn send(&self) {
        let mut enc = [0u8; encoded_max(120)];
        if let Some(n) = encode(&self.buf[..self.len], &mut enc) {
            for &b in &enc[..n] {
                while !pac::USART3.isr().read().txe() {}
                pac::USART3.tdr().write(|w| w.set_dr(u16::from(b)));
            }
            while !pac::USART3.isr().read().tc() {}
        }
    }
}

impl core::fmt::Write for Line {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let n = s.len().min(self.buf.len() - self.len);
        self.buf[self.len..self.len + n].copy_from_slice(&s.as_bytes()[..n]);
        self.len += n;
        Ok(())
    }
}

macro_rules! report {
    ($($arg:tt)*) => {{
        let mut line = Line { buf: [0; 120], len: 1 };
        line.buf[0] = kind::REPORT;
        let _ = write!(line, $($arg)*);
        line.send();
    }};
}

fn serial() {
    pac::RCC.ahb4enr().modify(|w| w.set_gpioden(true));
    pac::RCC.apb1enr1().modify(|w| w.set_usart3en(true));
    let _ = pac::RCC.apb1enr1().read();
    for pin in [8, 9] {
        pac::GPIOD
            .moder()
            .modify(|w| w.set_moder(pin, gpio::vals::Moder::ALTERNATE));
        pac::GPIOD.afr(1).modify(|w| w.set_afr(pin - 8, 7));
    }
    #[allow(clippy::cast_possible_truncation, reason = "the divisor is at most 80")]
    pac::USART3.brr().write(|w| w.set_brr((PERIPHERAL_HZ / BAUD) as u16));
    pac::USART3.cr1().write(|w| {
        w.set_te(true);
        w.set_re(true);
        w.set_ue(true);
    });
}

/// The next byte of the line, if one waits.
fn read() -> Option<u8> {
    let isr = pac::USART3.isr().read();
    if isr.ore() {
        pac::USART3.icr().write(|w| w.set_ore(true));
    }
    #[allow(clippy::cast_possible_truncation, reason = "the data register holds eight bits")]
    isr.rxne().then(|| pac::USART3.rdr().read().dr() as u8)
}

/// Send an answer to the laptop.
fn answer(body: &[u8]) {
    let mut raw = [0u8; 8];
    let mut enc = [0u8; encoded_max(8)];
    raw[0] = kind::CONTROL;
    let n = body.len().min(7);
    raw[1..=n].copy_from_slice(&body[..n]);
    if let Some(len) = encode(&raw[..=n], &mut enc) {
        for &b in &enc[..len] {
            while !pac::USART3.isr().read().txe() {}
            pac::USART3.tdr().write(|w| w.set_dr(u16::from(b)));
        }
    }
}

fn idle() {
    while pac::XSPI2.sr().read().busy() {}
}

/// Wait for the interface, drop the flags of what it did before, and set how the next transfer runs: 0 writes,
/// 1 reads, 3 maps the flash.
fn begin(mode: u8) {
    idle();
    // An abort empties the FIFO: a byte left over from the last transfer would be read as the first of the next.
    pac::XSPI2.cr().modify(|w| w.set_abort(true));
    while pac::XSPI2.cr().read().abort() {}
    idle();
    pac::XSPI2.fcr().write(|w| {
        w.set_ctef(true);
        w.set_ctcf(true);
        w.set_csmf(true);
        w.set_ctof(true);
    });
    pac::XSPI2
        .cr()
        .modify(|w| w.set_fmode(xspi::vals::Fmode::from_bits(mode)));
    // No dummy cycles, unless the transfer sets its own: the mapped read leaves eight behind.
    pac::XSPI2.tcr().write(|_| {});
}

/// Send a command that has no address and no data, on one line (`lines` 1, one instruction byte) or on eight
/// (`lines` 4 in the register's coding, two instruction bytes).
fn command(lines: u8, instruction: u32) {
    begin(0);
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(lines));
        w.set_isize(xspi::vals::CcrIsize::from_bits(u8::from(lines == 4)));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(instruction));
    idle();
}

/// Read the flash's three identification bytes on one line.
fn identify() -> u32 {
    begin(1);
    pac::XSPI2.dlr().write(|w| w.set_dl(2));
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(1));
        w.set_dmode(xspi::vals::CcrDmode::from_bits(1));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(0x9F));
    while !pac::XSPI2.sr().read().tcf() {}
    pac::XSPI2.dr().read().data() & 0x00FF_FFFF
}

/// Leave the mapped mode and put the flash back in its power-up mode, so commands can be sent on one line.
fn unmap() {
    pac::XSPI2.cr().modify(|w| w.set_abort(true));
    while pac::XSPI2.cr().read().abort() {}
    idle();
    power_up_mode();
}

/// Whatever mode the flash is in, it is in its power-up mode after a reset given both ways.
fn power_up_mode() {
    command(4, 0x6699);
    command(4, 0x9966);
    command(1, 0x66);
    command(1, 0x99);
    cortex_m::asm::delay(CORE_HZ / 10);
}

/// Switch the flash from its power-up mode to eight lines, one transfer per clock: bit 0 of its second configuration
/// register, which is volatile.
fn octal_mode() {
    command(1, 0x06);
    begin(0);
    pac::XSPI2.dlr().write(|w| w.set_dl(0));
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(1));
        w.set_admode(xspi::vals::CcrAdmode::from_bits(1));
        w.set_adsize(xspi::vals::CcrAdsize::from_bits(3));
        w.set_dmode(xspi::vals::CcrDmode::from_bits(1));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(0x72));
    pac::XSPI2.ar().write(|w| w.set_address(0));
    // SAFETY: a byte-wide write to the data register puts exactly one byte in the FIFO, which `begin` emptied.
    unsafe { (0x5200_A050 as *mut u8).write_volatile(0x01) };
    while !pac::XSPI2.sr().read().tcf() {}
    idle();
}

/// The flash's status byte: bit 0 is set while it writes or erases. It is read as four bytes, which the flash repeats,
/// so the data register is only ever accessed as a word.
fn status() -> u8 {
    begin(1);
    pac::XSPI2.dlr().write(|w| w.set_dl(3));
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(1));
        w.set_dmode(xspi::vals::CcrDmode::from_bits(1));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(0x05));
    while !pac::XSPI2.sr().read().tcf() {}
    pac::XSPI2.dr().read().data().to_le_bytes()[3]
}

fn settle() {
    while status() & 1 != 0 {}
}

/// Erase the 4 KiB sector that holds `addr`.
fn erase_sector(addr: u32) {
    command(1, 0x06);
    begin(0);
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(1));
        w.set_admode(xspi::vals::CcrAdmode::from_bits(1));
        w.set_adsize(xspi::vals::CcrAdsize::from_bits(3));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(0x21));
    pac::XSPI2.ar().write(|w| w.set_address(addr));
    idle();
    settle();
}

/// Program `data`, which lies inside one 256-byte page and is a whole number of words, at `addr`.
fn program_page(addr: u32, data: &[u8]) {
    let Some(last) = data.len().checked_sub(1) else { return };
    command(1, 0x06);
    begin(0);
    #[allow(clippy::cast_possible_truncation, reason = "a page has 256 bytes")]
    pac::XSPI2.dlr().write(|w| w.set_dl(last as u32));
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(1));
        w.set_admode(xspi::vals::CcrAdmode::from_bits(1));
        w.set_adsize(xspi::vals::CcrAdsize::from_bits(3));
        w.set_dmode(xspi::vals::CcrDmode::from_bits(1));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(0x12));
    pac::XSPI2.ar().write(|w| w.set_address(addr));
    for word in data.as_chunks::<4>().0 {
        while pac::XSPI2.sr().read().flevel() > 28 {}
        pac::XSPI2.dr().write(|w| w.set_data(u32::from_le_bytes(*word)));
    }
    while !pac::XSPI2.sr().read().tcf() {}
    settle();
}

/// Map the flash for reading at [`IMAGE`], from its power-up mode.
fn map() {
    octal_mode();
    begin(3);
    // The flash answers the octal read after 20 clocks, as it leaves the factory.
    pac::XSPI2.tcr().write(|w| w.set_dcyc(20));
    pac::XSPI2.ccr().write(|w| {
        w.set_imode(xspi::vals::CcrImode::from_bits(4));
        w.set_isize(xspi::vals::CcrIsize::from_bits(1));
        w.set_admode(xspi::vals::CcrAdmode::from_bits(4));
        w.set_adsize(xspi::vals::CcrAdsize::from_bits(3));
        w.set_dmode(xspi::vals::CcrDmode::from_bits(4));
    });
    pac::XSPI2.ir().write(|w| w.set_instruction(0xEC13));
}

/// The CRC-32 (IEEE) of `len` mapped bytes from `offset`.
fn crc(offset: u32, len: u32) -> u32 {
    let mut crc = !0u32;
    for i in 0..len {
        // SAFETY: the flash is mapped and the laptop asks only for bytes inside it.
        let b = unsafe { ((IMAGE + offset + i) as *const u8).read_volatile() };
        crc ^= u32::from(b);
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xEDB8_8320 & 0u32.wrapping_sub(crc & 1));
        }
    }
    !crc
}

fn word(bytes: &[u8], at: usize) -> Option<u32> {
    Some(u32::from_le_bytes(bytes.get(at..at + 4)?.try_into().ok()?))
}

/// Serve the laptop's requests until it says go. The flash is mapped again on return.
fn serve(line: &mut Deframer<{ encoded_max(load::BODY) }>) {
    answer(&[load::ENTER, 0]);
    let mut mapped = true;
    loop {
        let Some(byte) = read() else { continue };
        let Some(frame) = line.push(byte) else { continue };
        let Some((&kind::CONTROL, request)) = frame.split_first() else {
            continue;
        };
        let Some((&op, rest)) = request.split_first() else {
            continue;
        };
        if matches!(op, load::ERASE | load::WRITE) && mapped {
            unmap();
            mapped = false;
        }
        if matches!(op, load::CHECK | load::GO) && !mapped {
            map();
            mapped = true;
        }
        match (op, word(rest, 0)) {
            (load::ENTER, _) => answer(&[load::ENTER, 0]),
            (load::ERASE, Some(addr)) => {
                erase_sector(addr);
                answer(&[load::ERASE, 0]);
            }
            (load::WRITE, Some(addr)) if rest.len() % 4 == 0 => {
                let mut at = addr;
                let mut data = rest.get(4..).unwrap_or(&[]);
                while !data.is_empty() {
                    let room = 256 - (at % 256) as usize;
                    let (page, more) = data.split_at(room.min(data.len()));
                    program_page(at, page);
                    #[allow(clippy::cast_possible_truncation, reason = "a page has 256 bytes")]
                    {
                        at += page.len() as u32;
                    }
                    data = more;
                }
                answer(&[load::WRITE, 0]);
            }
            (load::CHECK, Some(addr)) => {
                let c = crc(addr, word(rest, 4).unwrap_or(0)).to_le_bytes();
                answer(&[load::CHECK, c[0], c[1], c[2], c[3]]);
            }
            (load::GO, _) => {
                answer(&[load::GO, 0]);
                while !pac::USART3.isr().read().tc() {}
                return;
            }
            _ => answer(&[op, 1]),
        }
    }
}

/// Power, clock and map the external flash.
fn map_flash() -> u32 {
    pac::RCC.ahb4enr().modify(|w| w.set_gpionen(true));
    pac::RCC.ahb5enr().modify(|w| w.set_xspi2en(true));
    let _ = pac::RCC.ahb5enr().read();
    pac::PWR.csr2().modify(|w| w.set_en_xspim2(true));

    // Port N carries XSPI2 and nothing else: DQS, NCS, IO0 to IO3, CLK on pins 0 to 6 and IO4 to IO7 on 8 to 11.
    for pin in [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11] {
        pac::GPION
            .ospeedr()
            .modify(|w| w.set_ospeedr(pin, gpio::vals::Ospeedr::from_bits(3)));
        pac::GPION.afr(pin / 8).modify(|w| w.set_afr(pin % 8, 9));
        pac::GPION
            .moder()
            .modify(|w| w.set_moder(pin, gpio::vals::Moder::ALTERNATE));
    }

    pac::XSPI2.cr().write(|_| {});
    idle();
    pac::XSPI2.dcr1().write(|w| {
        w.set_mtyp(xspi::vals::Mtyp::from_bits(1)); // Macronix
        w.set_devsize(24); // 2^25 bytes
        w.set_csht(xspi::vals::Csht::from_bits(1));
    });
    #[allow(clippy::cast_possible_truncation, reason = "the divisor is at most 3")]
    pac::XSPI2
        .dcr2()
        .write(|w| w.set_prescaler((BUS_HZ.div_ceil(FLASH_HZ) - 1) as u8));
    pac::XSPI2.cr().modify(|w| w.set_en(true));

    power_up_mode();
    let id = identify();
    map();
    id
}

/// Run the core from the first PLL at 320 MHz: the internal oscillator (64 MHz) divided by 16, multiplied by 160 and
/// divided by 2, with the buses at half the core's clock and the peripherals at half the buses'.
#[cfg(feature = "fast-clock")]
fn fast_clock() {
    use pac::rcc::regs;
    // The source is the internal oscillator (0) and the PLL's input is 4 MHz (the divisor, at bit 4).
    pac::RCC.pllckselr().write_value(regs::Pllckselr(16 << 4));
    // The input is in the 2 to 4 MHz range (1, at bit 3), the oscillator is the wide one, and the P output is on (bit 5).
    pac::RCC.pllcfgr().write_value(regs::Pllcfgr((1 << 3) | (1 << 5)));
    // Multiply by 160 and divide by 2 for P; each field holds its value less one. Q and R are not used.
    pac::RCC
        .plldivr(0)
        .write_value(regs::Plldivr((160 - 1) + (1 << 9) + (1 << 16) + (1 << 24)));
    pac::RCC.cr().modify(|w| w.set_pllon(0, true));
    while !pac::RCC.cr().read().pllrdy(0) {}
    // The dividers first, so that no bus is ever above its clock: the buses at half (8), the peripherals at half
    // of that (4 in each of the four fields).
    pac::RCC.bmcfgr().write_value(regs::Bmcfgr(8));
    pac::RCC.apbcfgr().write_value(regs::Apbcfgr(0x4444));
    pac::RCC.cfgr().modify(|w| w.set_sw(pac::rcc::vals::Sw::PLL1_P));
    while pac::RCC.cfgr().read().sws() != pac::rcc::vals::Sw::PLL1_P {}
}

#[entry]
fn main() -> ! {
    #[cfg(feature = "fast-clock")]
    fast_clock();
    serial();
    let id = map_flash();
    // The pin's first edge reads as a byte on the laptop: close that frame before the first real one.
    answer(&[]);
    report!("boot flash_id={id:06x} listening");

    // Half a second for the laptop to ask for the loader.
    let mut line = Deframer::<{ encoded_max(load::BODY) }>::new();
    for _ in 0..500_000u32 {
        if let Some(byte) = read()
            && let Some(frame) = line.push(byte)
            && frame.first() == Some(&kind::CONTROL)
            && frame.get(1) == Some(&load::ENTER)
        {
            serve(&mut line);
            break;
        }
        cortex_m::asm::delay(CORE_HZ / 1_000_000);
    }
    // SAFETY: the flash is mapped; these are the first two words of the image's vector table.
    let (stack, reset) = unsafe {
        (
            (IMAGE as *const u32).read_volatile(),
            (IMAGE as *const u32).add(1).read_volatile(),
        )
    };
    report!("boot stack={stack:#010x} reset={reset:#010x}");
    // An erased flash, or anything that is not an image for this chip, is not started.
    if !(0x2000_0000..=0x3000_8000).contains(&stack) || !(IMAGE..IMAGE + (32 << 20)).contains(&reset) {
        report!("boot no_image");
        loop {
            cortex_m::asm::nop();
        }
    }
    // SAFETY: the vector table at `IMAGE` was checked above; nothing of this stage is used after the jump.
    unsafe {
        (*cortex_m::peripheral::SCB::PTR).vtor.write(IMAGE);
        cortex_m::asm::bootload(IMAGE as *const u32)
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {
        cortex_m::asm::nop();
    }
}
