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
| `data.py` | writes a session's result files as JSON data sets beside them, in the shape of the PINC paper's `data/` |
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
examples/mcu/data.py examples/mcu/results/<date>   # the session as JSON: mcu-opt-3.json, mcu-opt-s.json, mcu-opt-z.json
```

A last argument `chip` to `build` (after the clock; `slow` names 64 MHz) or to `session` (after the rounds) runs
AES-128-GCM and SHA-256 on the chip's units, as below.

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

## The chip's cryptographic units

The STM32H7S3 has a cryptographic processor (AES), a hash processor (SHA-1 and SHA-2), a public-key accelerator and a
random generator. Built with the `chip-crypto` feature, the image gives the endpoint a `Provider`
(`firmware/src/crypto.rs`) that runs AES-128-GCM, the AES header mask and SHA-256 on the first two and everything
else in the library's software. The board then offers AES-128-GCM, and a peer with hardware AES chooses it; without
the feature the board offers ChaCha20-Poly1305 only. The seed of the node's keys comes from the random generator in
both builds.

Every image times each primitive when it starts, in software and on the chip, and checks the chip's AES-128-GCM
(seven lengths, and a wrong tag refused with the ciphertext left as it was), its header mask and its SHA-256 (eight
lengths) against the software; all agree in every file. At `opt-level = 3`, the least of four runs:

| | 64 MHz | 320 MHz | 600 MHz |
|---|---:|---:|---:|
| AES-128-GCM, 1,200 bytes sealed: software | 2,466 µs | 503 µs | 271 µs |
| the same on the chip | 255 µs | 66 µs | 37 µs |
| ChaCha20-Poly1305, 1,200 bytes sealed: software | 679 µs | 144 µs | 87 µs |
| AES header mask: software | 52 µs | 13 µs | 7.9 µs |
| the same on the chip | 5.7 µs | 6.2 µs | 5.1 µs |
| SHA-256 of 1,024 bytes: software | 432 µs | 90 µs | 47 µs |
| the same on the chip | 233 µs | 46 µs | 25 µs |
| X25519, one operation: software | 17.1 ms | 3.5 ms | 1.8 ms |
| ML-KEM-768 key generation: software | 24.5 ms | 5.0 ms | 2.7 ms |
| ML-KEM-768 encapsulation: software | 23.6 ms | 4.9 ms | 2.7 ms |
| ML-KEM-768 decapsulation: software | 30.9 ms | 6.3 ms | 3.4 ms |

Two sessions of 24 November at commit `cd4b3de6`, one with each build, are in
[`results/2026-11-24-crypto-software/`](results/2026-11-24-crypto-software) and
[`results/2026-11-24-crypto-chip/`](results/2026-11-24-crypto-chip). All eighteen images ran every session to its end.
With the feature every packet of every session was sealed and opened on the chip (10,148 in a file; the 25 the other
build counts are the check at its start).

| | 64 MHz | 320 MHz | 600 MHz |
|---|---:|---:|---:|
| Full handshake, the board accepts: board CPU, software | 125 ms | 37 ms | 25 ms |
| the same with the chip's units | 125 ms | 38 ms | 25 ms |
| Round trip of 32 bytes, timed by the laptop: software | 4.5 ms | 3.9 ms | 3.5 ms |
| the same with the chip's units | 4.2 ms | 3.8 ms | 3.5 ms |
| Board CPU of the first session (200 round trips, 256 KiB there and back): software | 2,479 ms | 1,770 ms | 1,598 ms |
| the same with the chip's units | 2,047 ms | 1,904 ms | 1,685 ms |
| the same built with `opt-level = z`: software | 4,714 ms | 2,498 ms | 1,922 ms |
| the same with the chip's units | 2,795 ms | 1,907 ms | 1,613 ms |
| 256 KiB there and back at `opt-level = z`: software | 38 KiB/s | 53 KiB/s | 56 KiB/s |
| the same with the chip's units | 50 KiB/s | 57 KiB/s | 59 KiB/s |

- The handshake does not change: its cost is the public-key work, which the chip's units used here do not do.
- The chip seals a packet 2.2 to 2.7 times faster than the software's ChaCha20-Poly1305. A session shows it where the
  processor is the limit: at 64 MHz, and in the image built for size. At 320 and 600 MHz and `opt-level = 3` the
  difference is inside what one session varies by; the board CPU of a session is one sample, and most of it is the
  main loop asking the endpoint for work.
- In both of these builds the stack reaches 112 KiB at `opt-level = 3`, where the session above reached 151 KiB, and
  the image is 634 to 645 KiB against 714 to 716 KiB; built for size the stack is 235 and 248 KiB, against 229 and
  238 KiB. The cause is not known.

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
- The chip's public-key accelerator is not used. It has no Curve25519 or ML-KEM operation of its own, and the chip
  crate has no registers for it. The chip's protected AES unit (SAES) is not used either.
- The chip's units are driven by polling, one operation at a time, and the AES key is loaded for every packet.
- The facade (`pinc`) is not used: the host here is `link/`, with no allocator.

## Result directories

Each directory of 24 November also holds its JSON data sets (`data.py`).

- [`results/2026-11-24/`](results/2026-11-24): the session above, nine files.
- [`results/2026-11-24-crypto-software/`](results/2026-11-24-crypto-software) and
  [`results/2026-11-24-crypto-chip/`](results/2026-11-24-crypto-chip): the two sessions of the chip's units, nine files
  each.
- [`results/2026-11-23/`](results/2026-11-23): the 64 and 320 MHz images, commit `b3e6d630`. Its times are within 3 ms
  of the session above; its stack at `z` is 249 KiB.
- [`results/2026-11-23-without-conn-in-place/`](results/2026-11-23-without-conn-in-place): the same images on the
  library without the connection built in its slot (#763); its files name commits that are not in this repository.
  At `opt-level = 3` the stack reaches 351 KiB of its 368. Built for size the board accepts (298 and 300 KiB) and its
  dial overruns the stack; the two `-dial-fault.log` files hold the board's fault reports.
