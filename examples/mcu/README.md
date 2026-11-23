# PINC on a microcontroller

The `no_std` core (`pinc-core`, the SANS-IO endpoint, with no allocator) runs on a board: an STM32H7S3L8 (Cortex-M7)
on a NUCLEO-H7S3L8. It completes the hybrid post-quantum handshake with a laptop, resumes it from a ticket, and
carries streams both ways, as the acceptor and as the dialer. This directory holds the programs that do it and what
they measured ([#540](https://github.com/sourcenetwork/pinc/issues/540)).

The link is the board's serial line (the ST-LINK's virtual COM port, 1 Mbaud), with each datagram byte-stuffed into a
frame. It is not a network: there is no loss, no reordering and one peer.

## What was measured

Session of 23 November 2026, commit `b3e6d630`, ten sessions of each kind; the files are in
[`results/2026-11-23/`](results/2026-11-23). Times are medians; over the ten sessions the smallest and the largest are
within 3% of them at 64 MHz and within 6% at 320 MHz. The board's clock is its internal oscillator (64 MHz), or a PLL fed by it
(320 MHz); the chip allows 600 MHz, which needs its voltage scale raised and was not tried. "Board CPU" is the time the
board spent inside the endpoint, counted with the core's cycle counter around every call; the rest of a handshake's
time is its bytes on the line (2,900 bytes at 1 Mbaud take 29 ms).

The image built for speed (`opt-level = 3`):

| | 64 MHz | 320 MHz |
|---|---|---|
| Full handshake, the board accepts: board CPU | 125 ms | 37 ms |
| the same, as the laptop sees it, dial to session | 119 ms | 50 ms |
| the same, dial to the first 32 bytes back | 160 ms | 69 ms |
| Resumed handshake, the board accepts: board CPU | 42 ms | 12 ms |
| the same, as the laptop sees it, dial to the first 32 bytes back | 54 ms | 21 ms |
| Full handshake, the board dials: board CPU | 134 ms | 42 ms |
| the same, by the board's clock, dial to session | 152 ms | 62 ms |
| Resumed handshake, the board dials: board CPU | 47 ms | 16 ms |
| the same, by the board's clock, dial to the peer's answer | 50 ms | 19 ms |
| Round trip of 32 bytes on a stream (200, timed by the laptop) | 4.6 ms | 4.1 ms |
| the same, timed by the board | 4.6 ms | 4.1 ms |
| 256 KiB there and back on a stream | 52 KiB/s | 57 KiB/s |
| Image in the flash | 713 KiB | 715 KiB |
| Statics | 200 KiB | 200 KiB |
| Stack, deepest | 151 KiB | 151 KiB |

The round trip and the transfer are the line's, not the board's: the line carries 100 kB/s. No byte of the line was
lost in any run.

Built for size, the image is half as large and slower, and its stack is deeper:

| | `opt-level` 3 | `s` | `z` |
|---|---|---|---|
| Image in the flash | 713 KiB | 375 KiB | 358 KiB |
| Full handshake, the board accepts: board CPU at 64 MHz | 125 ms | 153 ms | 226 ms |
| the same at 320 MHz | 37 ms | 39 ms | 57 ms |
| Full handshake, the board dials: board CPU at 64 MHz | 134 ms | 163 ms | 240 ms |
| the same at 320 MHz | 42 ms | 45 ms | 64 ms |
| Resumed, the board accepts: board CPU at 64 MHz | 42 ms | 56 ms | 70 ms |
| the same at 320 MHz | 12 ms | 14 ms | 18 ms |
| Stack, deepest | 151 KiB | 229 KiB | 249 KiB |

Since the chip's fault below was mended the session has run three more times on this library: twice with every image
to its end, and once with every image but one (64 MHz at `opt-level = 3` closed with the path dead in both its runs,
at the start of the session; rebuilt alone straight after, it ran three times of three, and the board gave no fault).
Why that image closed is not known.

The same session on the library without the connection built in its slot is in
[`results/2026-11-23-without-conn-in-place/`](results/2026-11-23-without-conn-in-place); it was run before these
programs were in this repository, and its files name commits that are not in it. At `opt-level = 3` both roles run and
the stack reaches 351 KiB of its 368. Built for size the board accepts (298 and 300 KiB) and its dial overruns the
stack at both clocks: the board reports the fault, a write 70 KiB below the stack's lower end at `s` and 15 KiB below
at `z` (the two `-dial-fault.log` files).

## The chip stops on a read it only guessed at

Before the ranges below were closed some images stopped the board partway through a session: no fault report, no panic, and the debug
port no longer answered. A tick every millisecond that noted where the program was showed the tick dying with the
program, somewhere different in ordinary code each time. Whether an image did it depended on its bytes, not its
source: built in another directory (the paths are in the image) the same source stopped in every run or in none.

The cause is the chip's, and ST names it for an erratum
([community thread](https://community.st.com/stm32-mcus-embedded-software-32/stm32h7rs-h7s3l8-core-freeze-xspi-dcache-in-bootloader-159810),
22 December 2025): with the data cache on, the core fills cache lines ahead of loads it has not decided to make, and a
fill that lands in the graphics unit's range (`0x2500_0000` to `0x25FF_FFFF`) stops the chip. `firmware/src/board.rs`
closes the ranges no memory answers with the memory protection unit before it turns the cache on.

| The image built for size, at 64 MHz | runs that ended |
|---|---|
| before the change | none of 8 |
| with the data cache off | 6 of 6, a handshake taking 2.4 times as long |
| with the ranges closed | 6 of 6, and then the sessions above |

Two sessions before the change ended for three images of six and for six of six, from the same source in two
directories. What was tried and did not help: the flash clocked at half the speed, sampled later, released when idle,
and the external memories' range closed alone. The boot stage read the mapped image 3 million bytes in order and
2.4 million words out of order and every read agreed, so the flash was never at fault.

Two more things kept the board from saying what was wrong, and are mended with it. A probe that was ever told to stop
the core at a fault leaves that order in the core until its power goes, so the core halted at a fault and the image's
handler never ran; the image clears the order, and `board.sh` no longer gives it. And the range below the stack is
closed like the rest, so a stack that outgrows its room is a fault and not one more read that nothing answers.

Of the runs that did not end before these changes, the dials of the images built for size on the library without
the connection built in its slot were the stack, as the session above shows. The others (a run at `opt-level = 3`
closed as unanswered, and runs that closed with the path dead) may have been the chip stopping.

## What it takes

**Flash.** 713 KiB at `opt-level = 3`, 358 KiB at `z`, with every algorithm the library accepts from a peer linked in
(ML-DSA and P-256 verification besides Ed25519, both ciphers). The chip has 64 KiB of flash of its own; the image runs
in place from the board's external flash.

**RAM.** 351 KiB of the chip's 620 KiB at `opt-level = 3`, for one session:

| | bytes |
|---|---|
| The endpoint (a table of one session, tables sized for a device) | 57,616 |
| The session's slot (the connection, its handshake machine, its tables) | 69,040 |
| The session's memory: a pool of three 16 KiB chunks and the stream table | 61,936 |
| The node's keys, the receive ring of the serial line, the rest | 16,416 |
| Stack, deepest | 154,848 |

Three things about the library decide these numbers:

1. **The endpoint's fixed tables.** As the library ships, the tables that do not grow with the session table are
   sized for a node with hundreds of peers, and an endpoint for one session was 326,592 bytes on this target on
   16 November (not measured again). An application's build sets each size (`pinc-core`, `sizes`); `board.sh` gives the
   board's builds the sizes of a handful of peers, and the endpoint is 57,616 bytes. The laptop's end keeps the tables
   of a host, so every session here is between the two.
2. **The stack.** What is left of it after the connection is built in its slot was read from the frame sizes of the
   image of 16 November and not again: the frame that frees a slot takes the connection by value (80 KiB), the one that
   builds the dialing side's handshake machine holds two copies of it (52 KiB), and the frame that verifies an ML-DSA
   signature (a peer with such an identity; not exercised here) is 142 KiB. Built for size the stack is 78 to 98 KiB
   deeper, and the cause is not found; part of it is this firmware's own main loop.
3. **The key pair.** Without an allocator `pinc_crypto::Keypair` holds room for an ML-DSA key whatever the algorithm
   (65,928 bytes, [#706](https://github.com/sourcenetwork/pinc/issues/706)). The board keeps its Ed25519 key as itself
   and answers the endpoint's signature requests with it.

## What was not measured

- A network: the line loses nothing and has one peer. Ethernet is on the board and not used.
- More than one session, more than one stream at a time (the pool of three chunks holds one stream's buffers both
  ways), a peer with an ML-DSA or P-256 identity, a key roll, a path change.
- The chip at 600 MHz, and the flash interface above 64 MHz.
- A board that starts with no probe. The probe loads the boot stage into RAM after every reset, and the board stops
  when the probe lets go of it; the chip's own flash is as it was found.
- The facade (`pinc`). It builds without `std` now, with an allocator; the host here is still the few hundred lines
  of `link/`, with none.
- The board's time is by the chip's internal oscillator, not a crystal; its time of a handshake and the laptop's
  agree within a millisecond in 51.

## The programs

| Path | What |
|---|---|
| `link/` | the endpoint a small device holds: table sizes, memory lent from statics, the host duties, an echo, the serial framing; `no_std`, no heap, no `unsafe`; both ends build on it |
| `boot/` | the board's boot stage, which the probe loads into RAM: sets the clock, maps the external flash (octal mode) at `0x7000_0000` and starts the image; it is also the loader, which erases, programs and checks the flash as the laptop asks over the serial line |
| `firmware/` | the image: accepts and echoes, or dials when asked and times its own round trips; reports the cost of every handshake and session, its statics and its stack's high-water mark |
| `peer/` | the laptop's end: loads an image, runs the sessions, writes the measured lines |
| `board.sh` | builds, loads and measures; `session` runs every optimisation level at both clocks |
| `results/` | the result files, one directory a session |

The memory map of the image is in `firmware/memory.x`: the stack has the lower 368 KiB of the AXI SRAM, so one that
outgrows its room faults instead of writing over the statics above it; the session's memory is in the DTCM RAM and
the endpoint in the ITCM RAM.

## Running it

It needs the board on USB, the pinned Rust toolchain (the `thumbv7em-none-eabihf` target is in
`rust-toolchain.toml`), [probe-rs](https://probe.rs) and access to the ST-LINK and its serial port (a udev rule for
USB vendor `0483`).

```sh
just mcu                                           # no board: lints, the images linked, both ends of the line in one process
just board build 3 fast                            # the boot stage and the image: opt-level 3, 320 MHz (leave `fast` out for 64 MHz)
just board flash                                   # load the image into the external flash and start it
just board run out.txt 10                          # ten sessions of each kind; the lines measured go to out.txt
just board session examples/mcu/results/2026-11-23 # every optimisation level at both clocks
```

`PROBE_RS` names the probe-rs command when it is not on the `PATH` (with Nix:
`PROBE_RS="nix shell nixpkgs#probe-rs-tools -c probe-rs"`), and `PORT` the serial line when it is not `/dev/ttyACM0`.

A result file holds the lines of the run in order (`board ...` is what the board reported, `laptop ...` what the
laptop measured), a `summary` of each kind of handshake, and the `conditions` it ran under.
