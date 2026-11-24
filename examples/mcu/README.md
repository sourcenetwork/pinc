# PINC on a microcontroller

The `no_std` core (`pinc-core`, the SANS-IO endpoint, with no allocator) on an STM32H7S3L8 (Cortex-M7, NUCLEO-H7S3L8).
The board completes the hybrid post-quantum handshake with a laptop, resumes it from a ticket, and carries streams both
ways, as the acceptor and as the dialer. This directory holds the programs that do it and what they measured
([#540](https://github.com/sourcenetwork/pinc/issues/540)). It is a workspace of its own.

| Path | What |
|---|---|
| `link/` | the endpoint a small device holds: memory lent from statics, the host duties, an echo, the serial framing; `no_std`, no heap, no `unsafe`; both ends build on it |
| `boot/` | the board's boot stage, loaded into RAM by the probe: sets the clock, maps the external flash at `0x7000_0000`, starts the image; also the loader that programs the flash over the serial line |
| `firmware/` | the image: accepts and echoes, or dials when asked; reports the cost of every handshake and session, its statics and its stack's high-water mark |
| `peer/` | the laptop's end: loads an image, runs the sessions, writes the measured lines |
| `board.sh` | builds, loads and measures |
| `results/` | the result files, one directory a session |

## Running it

It needs the board on USB, the pinned Rust toolchain (the `thumbv7em-none-eabihf` target is in
`rust-toolchain.toml`), [probe-rs](https://probe.rs) and access to the ST-LINK and its serial port (a udev rule for
USB vendor `0483`).

```sh
just mcu                                           # no board: lints, the images linked, both ends of the line in one process
just board build 3 fast                            # opt-level 3 (or s, z) at 320 MHz (`full`: 600 MHz, neither: 64 MHz)
just board flash                                   # load the image into the external flash and start it
just board run out.txt 10                          # ten sessions of each kind; the lines measured go to out.txt
just board session examples/mcu/results/<date>     # every optimisation level at every clock, one file each
```

`PROBE_RS` names the probe-rs command when it is not on the `PATH` (with Nix:
`PROBE_RS="nix shell nixpkgs#probe-rs-tools -c probe-rs"`), and `PORT` the serial line when it is not `/dev/ttyACM0`.

A result file holds the lines of the run in order (`board ...` is what the board reported, `laptop ...` what the
laptop measured), a `summary` of each kind of handshake, and the `conditions` it ran under.

## Measurement protocol

- Board: NUCLEO-H7S3L8, STM32H7S3L8, 620 KiB of RAM, 64 KiB of flash of its own (not written) and 32 MiB outside it,
  which the image runs from in place. Data and instruction caches on.
- Link: the board's serial line (the ST-LINK's virtual COM port) at 1 Mbaud, each datagram byte-stuffed into a frame.
  It is not a network: nothing is lost or reordered, and there is one peer.
- Clock: the internal oscillator at 64 MHz, or a PLL fed by it at 320 MHz, or at 600 MHz (the chip's limit) with the
  voltage scale raised. The buses run at half the PLL's clock and the flash interface at 53 to 64 MHz.
- Build: rustc 1.100.0, `opt-level` 3, `s` and `z`. The board's endpoint has the table sizes `board.sh` sets
  (`PINC_EVENT_BASE=128`, `PINC_LEDGER_ENTRIES=32`, `PINC_SUBS_SEEN=32`, `PINC_PEER_RTTS=16`, `PINC_PREKEY_PEERS=16`,
  `PINC_REJOIN_ADDRS=16`, `PINC_MAX_DATAGRAM=1500`); the laptop's has the library's defaults.
- Identities: Ed25519 on both ends. Every algorithm the library accepts from a peer is linked into the image.
- Workload, for each image: ten full and ten resumed handshakes with the laptop dialing, the same with the board
  dialing, 20 round trips of 32 bytes on a stream after each, and 200 round trips and 256 KiB there and back in the
  first session.
- "Board CPU" is the time the board spent inside the endpoint, counted with the core's cycle counter around every
  call. The rest of a handshake's time is its bytes on the line: 2,900 bytes at 1 Mbaud take 29 ms.

## Results

Session of 24 November 2026, commit `6fdc7aa6`, in [`results/2026-11-24/`](results/2026-11-24). All nine images ran
every session to its end, and no byte of the line was lost. Times are medians of ten. The smallest and the largest are
within 1% of the median at 64 MHz and within 4% at 320 and 600 MHz, except the board CPU of a full dial there, which
is within 13%.

Built for speed (`opt-level = 3`):

| | 64 MHz | 320 MHz | 600 MHz |
|---|---:|---:|---:|
| Full handshake, the board accepts: board CPU | 124 ms | 37 ms | 24 ms |
| the same, as the laptop sees it, dial to session | 119 ms | 50 ms | 41 ms |
| the same, dial to the first 32 bytes back | 159 ms | 68 ms | 55 ms |
| Resumed handshake, the board accepts: board CPU | 42 ms | 11 ms | 7 ms |
| the same, as the laptop sees it, dial to the first 32 bytes back | 53 ms | 20 ms | 15 ms |
| Full handshake, the board dials: board CPU | 134 ms | 45 ms | 29 ms |
| the same, by the board's clock, dial to session | 151 ms | 61 ms | 48 ms |
| Resumed handshake, the board dials: board CPU | 46 ms | 15 ms | 10 ms |
| the same, by the board's clock, dial to the peer's answer | 50 ms | 19 ms | 14 ms |
| Round trip of 32 bytes on a stream, timed by the laptop | 4.7 ms | 4.2 ms | 3.7 ms |
| the same, timed by the board | 4.7 ms | 4.2 ms | 3.7 ms |
| 256 KiB there and back on a stream | 52 KiB/s | 58 KiB/s | 59 KiB/s |

The round trip and the transfer are the line's, not the board's: the line carries 100 kB/s.

By optimisation level:

| | `3` | `s` | `z` |
|---|---:|---:|---:|
| Image in the flash | 716 KiB | 376 KiB | 358 KiB |
| Statics | 200 KiB | 200 KiB | 200 KiB |
| Stack, deepest | 151 KiB | 229 KiB | 238 KiB |
| Full handshake, the board accepts: board CPU at 64 MHz | 124 ms | 153 ms | 228 ms |
| the same at 320 MHz | 37 ms | 39 ms | 59 ms |
| the same at 600 MHz | 24 ms | 24 ms | 37 ms |
| Full handshake, the board dials: board CPU at 64 MHz | 134 ms | 162 ms | 242 ms |
| the same at 320 MHz | 45 ms | 45 ms | 66 ms |
| the same at 600 MHz | 29 ms | 28 ms | 43 ms |
| Resumed handshake, the board accepts: board CPU at 64 MHz | 42 ms | 55 ms | 70 ms |
| the same at 320 MHz | 11 ms | 13 ms | 18 ms |
| the same at 600 MHz | 7 ms | 8 ms | 11 ms |

## Memory

One session takes 351 KiB of the chip's 620 KiB at `opt-level = 3`:

| | bytes |
|---|---:|
| The endpoint (a table of one session, tables sized for a device) | 57,616 |
| The session's slot (the connection, its handshake machine, its tables) | 69,040 |
| The session's memory: a pool of three 16 KiB chunks and the stream table | 61,936 |
| The node's keys, the receive ring of the serial line, the rest | 16,416 |
| Stack, deepest | 154,848 |

- **Table sizes.** With the library's default sizes the endpoint is 326,592 bytes on this target, more than half of
  the chip's RAM, so the board's builds set the sizes above (`pinc-core`, `sizes`).
- **Stack.** The image's stack is the lower 368 KiB of the AXI SRAM (`firmware/memory.x`), below the statics: a stack
  that outgrows its room leaves the RAM and the board reports the fault, where one above the statics would write over
  them. The deepest path is a dial.
- **Key pair.** Without an allocator `pinc_crypto::Keypair` holds room for an ML-DSA key whatever the algorithm
  (65,928 bytes, [#706](https://github.com/sourcenetwork/pinc/issues/706)). The board keeps its Ed25519 key as itself
  and answers the endpoint's signature requests with it.

## The chip's fault with the data cache on

With the data cache on, the core fills cache lines ahead of loads it has not decided to make, and a fill that lands in
an address range nothing answers stops the chip: no fault, no panic, and the debug port stops answering. Whether an
image meets it depends on its bytes, not its source. ST names the range `0x2500_0000` to `0x25FF_FFFF` for an erratum
([community thread](https://community.st.com/stm32-mcus-embedded-software-32/stm32h7rs-h7s3l8-core-freeze-xspi-dcache-in-bootloader-159810)).

`firmware/src/board.rs` closes every range no memory answers with the memory protection unit before it turns the
cache on. An image that stopped in eight runs of eight without the closed ranges ran six of six with them.

A probe that was once told to stop the core at a fault leaves that order in the core until its power goes, and the
image's fault handler then never runs. The image clears the order when it starts, and `board.sh` does not give it.

## Limits

- No network: the line loses nothing and has one peer. Ethernet is on the board and not used.
- One session and one stream at a time (the pool of three chunks holds one stream's buffers both ways), Ed25519
  identities only, no key roll, no path change.
- One board, one session of measurements for these figures.
- From 320 to 600 MHz the board CPU of a handshake falls by a factor of 1.5 to 1.6 for 1.9 times the clock; the cause
  is not known.
- Built for size the stack is 78 to 87 KiB deeper than at `opt-level = 3`; the cause is not known.
- In one session of 23 November the 64 MHz image at `opt-level = 3` closed with the path dead in both its runs, with
  no fault reported; it ran in every other session. The cause is not known.
- The board does not start alone: the probe loads the boot stage into RAM after every reset, and the board stops when
  the probe lets go of it.
- The board's time is by the chip's internal oscillator, not a crystal; its time of a handshake and the laptop's agree
  within a millisecond in 51.
- The facade (`pinc`) is not used: the host here is `link/`, with no allocator.

## Result directories

- [`results/2026-11-24/`](results/2026-11-24): the session above, nine files.
- [`results/2026-11-23/`](results/2026-11-23): the 64 and 320 MHz images, commit `b3e6d630`. Its times are within 3 ms
  of the session above; its stack at `z` is 249 KiB.
- [`results/2026-11-23-without-conn-in-place/`](results/2026-11-23-without-conn-in-place): the same images on the
  library without the connection built in its slot (#763); its files name commits that are not in this repository.
  At `opt-level = 3` the stack reaches 351 KiB of its 368. Built for size the board accepts (298 and 300 KiB) and its
  dial overruns the stack; the two `-dial-fault.log` files hold the board's fault reports.
