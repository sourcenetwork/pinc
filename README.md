<p align="center">
  <img src="art/pinc-banner.png" alt="PINC: next-gen peer-to-peer networking stack" width="100%">
</p>

**PINC** (read "pins") stands for **P**rovable **I**dentity-**N**ative **C**onnectivity:

- *Provable*: its state machines are specified in TLA+, model checked and proved in Lean 4, crate by crate (see
  [Proofs](#proofs)), and a node checks what it receives itself: every session is mutually authenticated, and a value
  is checked against its root before the application sees a byte of it.
- *Identity-native*: a node is reached by its id, which is derived from its key, not by an address.
- *Connectivity*: one stack that connects nodes directly, through relays, and across links that are not there all
  the time.

**PINCER**, the transport PINC runs on, stands for **PINC** **E**ncrypted **R**eliable transport.

PINC is a peer-to-peer networking stack for Rust, written SANS-IO. It has its own encrypted, reliable transport
(PINCER) with a hybrid post-quantum handshake (X25519 plus ML-KEM-768). The hybrid claim is the full handshake's: a
resumed session runs no ML-KEM, so its keys are as secret as its ticket's key (which a full handshake set up), and the
key roll is an X25519 ratchet, so with X25519 broken it does not recover a session whose keys were stolen. On top of
that core it builds membership, verified value transfer with no size limit, broadcast, set reconciliation and
delay-tolerant delivery. It runs from a microcontroller to a data centre and in the browser, and you write your own
protocols on top of it.

PINC is a library, not a framework:
- **No runtime dependency.** The protocol crates are state machines: you give them bytes, time and commands, and they
  give back packets to send, timers and events. PINC depends on no async runtime.
- **The host owns the runtime.** You pass the facade your I/O as three async closures (receive a datagram, send a
  datagram, sleep until an instant) and call async methods. It starts no thread, no task and no socket loop: the futures
  you await drive the endpoint, on your executor and your core. tokio, smol and nuclei all work.
- **One endpoint per core.** An endpoint's handles stay on the thread that built it, so nothing is shared between
  threads and nothing is locked: the host spawns their futures with its executor's local spawn and runs one endpoint
  per core.
- **Hot path:** zero-copy parsing and no heap allocation in steady state are design rules.

> **Status: pre-release.** The protocol crates are built and tested, and their proofs land crate by crate. Open work
> is tracked in the [issues](https://github.com/sourcenetwork/pinc/issues).

## Usage

An echo over loopback. The host's whole contribution is the three closures; here they sit on a
[nuclei](https://crates.io/crates/nuclei) UDP socket. Hosts with no executor drive the SANS-IO crates (`pinc-core`)
directly.

```rust
use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::time::Instant;

use nuclei::Handle;
use nuclei::time::sleep_until_precise;
use pinc::{Endpoint, Hosted, Pinc};

const ALPN: &[u8] = b"echo/1";

async fn bind() -> pinc::Result<Endpoint<impl Hosted>> {
    let any = SocketAddr::from(([127, 0, 0, 1], 0));
    let sock = Arc::new(Handle::<UdpSocket>::bind(any).await.expect("bind"));
    let (rx, tx) = (Arc::clone(&sock), Arc::clone(&sock));
    Pinc::builder().alpn(ALPN).local_addr(sock.local_addr().expect("address")).build(
        async move |buf: &mut [u8]| rx.recv_from(buf).await,         // receive a datagram
        async move |pkt: &[u8], to: SocketAddr| tx.send_to(pkt, to).await, // send a datagram
        async |at: Instant| sleep_until_precise(at).await,           // sleep until a deadline
    )
}

#[nuclei::main]
async fn main() -> pinc::Result<()> {
    let (server, client) = (bind().await?, bind().await?);
    let addr = server.addr(); // node id and socket address

    let accept = nuclei::spawn_local(async move {
        let conn = server.accept().await.expect("endpoint stopped").into_connection();
        let (mut tx, mut rx) = conn.accept_bi().await?;
        tx.write_all(&rx.read_to_end(1 << 20).await?).await?;
        tx.finish().await?;
        conn.closed().await; // dropping a connection closes it: wait for the client to finish reading
        pinc::Result::Ok(())
    });

    let conn = client.connect(addr, ALPN).await?;
    let (mut tx, mut rx) = conn.open_bi().await?;
    tx.write_all(b"hello, pinc").await?;
    tx.finish().await?;
    assert_eq!(rx.read_to_end(1 << 20).await?, b"hello, pinc");
    conn.close(0).await;
    accept.await
}
```

An endpoint with no future being polled makes no progress, which is the SANS-IO contract. Every call drives the endpoint
while it waits; a host with nothing else pending on it (a server between accepts, connections that only need their
keepalives) awaits `Endpoint::run()`.

## Without `std`

The `std` feature is on by default. A microcontroller or wasm host takes `pinc` with `default-features = false`, which
is `no_std` plus an allocator, and brings a `Platform` (its clock, its randomness and its I/O error type) to
`Pinc::builder_on` in place of `Pinc::builder`. Each endpoint then holds its own buffers, reserved when it is built.
The gate builds `pinc` and `pinc-keystore` for `thumbv7em-none-eabihf` and `wasm32-unknown-unknown`: it proves the
build. The memory one session needs on a microcontroller is not measured yet. Measured on the 64-bit build host, not
on a microcontroller: an endpoint with one session slot and 8 pool chunks holds about 0.8 MB with no session, one
connected session adds about 2.8 MB (room reserved for its tables, written as it is used), and build, connect, echo
and close run on 1 MiB of stack and fail on 512 KiB. `Limits::wasm()` is the preset for a 32-bit address space.

## Layout

| Path | What |
|---|---|
| `crates/` | the library, one crate per component |
| `proofs/` | TLA+ specifications (TLC) and Lean 4 proofs, both validated against traces of the real code |
| `tests/` | every test (integration, property, scenario, trace), run with [cargo-nextest](https://nexte.st) |
| `benches/` | micro benchmarks (per packet, allocations, copies) and the loopback comparison with iroh and rust-libp2p; a workspace of its own |
| `distributed/` | the distributed test harness: one binary that builds an emulated network of containers, runs PINC, iroh and rust-libp2p nodes on it with faults, measures them and serves a dashboard; a workspace of its own |
| `docs/` | [PROOFS.md](docs/PROOFS.md): what is proven, how it is checked, the assumptions |
| `scripts/` | the gate and the proof runner |

## Crates

| Crate | What it does | `no_std` | Status |
|---|---|---|---|
| `pinc` | the facade: builder, connections, streams, datagrams, topics, lookup by id, the hub and relay roles, over the host's three closures | yes, with an allocator and a `Platform` (the `std` feature is on by default) | built |
| `pinc-wire` | varints and a strict canonical DAG-CBOR codec, parsed in place | yes | built; varints proven, the codec tested ([#606](https://github.com/sourcenetwork/pinc/issues/606)) |
| `pinc-dag` | content-addressed blocks and CIDs, value roots, range proofs | yes, heap-free | built; roots and range proofs proven, CIDs, blocks and CAR tested ([#606](https://github.com/sourcenetwork/pinc/issues/606)) |
| `pinc-crypto` | RustCrypto primitives behind one `Provider`: AEADs, X25519, ML-KEM-768, four identity algorithms, BLAKE3 | yes | built |
| `pinc-keystore` | long-term keys behind a `KeyStore` trait; a software store and a pure-Rust TPM 2.0 store (`hwenc`) | yes, with an allocator (the TPM store needs `std`) | built |
| `pinc-security` | hybrid post-quantum handshake, resumption with 0-RTT, key schedule, packet protection, key roll | yes | built, proven |
| `pinc-transport` | PINCER: streams, datagrams, flow and congestion control, loss recovery, pacing, path MTU, migration | yes | built |
| `pinc-core` | the SANS-IO endpoint: host interface, protocol dispatch, commands, events, queries | yes | built |
| `pinc-node` | the endpoint, the connectivity client and every layer composed over real sessions | yes | built |
| `pinc-connect` | carriers, relays, signed records and lookup, hole punching, the hub tunnel, the mailbox | yes | built; relay side proven |
| `pinc-portmap` | a UDP port mapping from the home gateway (PCP, NAT-PMP, UPnP-IGD), off unless turned on | yes, heap-free | built |
| `pinc-table` | fixed tables over one block of bytes made once: sorted slab, array, ring, slot pool; no allocation after setup | yes, heap-free | built |
| `pinc-membership` | hub roster and member view: leases, probes, incarnations, leave, revocation | yes | built |
| `pinc-values` | verified streaming of values of any size from up to four providers, with resume | yes | built, proven |
| `pinc-broadcast` | topic broadcast through hubs with origin authentication, replay floors and a bounded log | yes | built, proven |
| `pinc-reconcile` | range-based set reconciliation whose cost scales with the difference | yes | built |
| `pinc-dtn` | bundles sealed to a recipient, erasure coding, custody, copy-limited forwarding | yes | built, proven |
| `pinc-sim` | deterministic network simulator and scenario suite | no | built |

**proven**: every property has a TLA+ model, a Lean theorem and trace validation; the others are being closed
([docs/PROOFS.md](docs/PROOFS.md), [#105](https://github.com/sourcenetwork/pinc/issues/105)).

## Build and test

The [justfile](justfile) holds every task; CI runs the same recipes.

```sh
just setup        # install everything: system packages, the Rust toolchain, cargo-nextest, Lean, the TLA+ tools
just              # list the recipes
just gate         # everything a change must pass: checks, tests, doctests, proofs
just checks       # dependency rules, format, lints, docs, no_std builds, pure Rust
just test         # every test with cargo-nextest (the hwenc TPM tests need swtpm); just test-default skips hwenc
just proofs       # Lean proofs, TLC model checking, trace validation and model-based tests
just tla-tools    # install the pinned TLA+ tools the proofs use
just bench        # micro benchmarks
just compare      # PINC against iroh and rust-libp2p on loopback (run it on an otherwise idle machine; needs sudo and tc)
just distributed run distributed/scenarios/wan.toml   # a scenario on an emulated network (Docker and sudo)
just distributed run distributed/scenarios/wan.toml --hosts fleet.toml   # the same on real machines over SSH (see distributed/infra)
just distributed serve                                # the dashboard, on http://127.0.0.1:7878
just distributed clean                                # remove whatever a run left
just distributed summarize distributed/results/<run>  # rebuild a run's summary from its raw rows, running nothing
just e2e          # the harness end to end: a two-node scenario, every stack (Docker and sudo)
```

The distributed harness gives every node its own container and network stack on one machine, shapes each link with
`tc netem`, and runs PINC, iroh and rust-libp2p through the same tests: transport (setup, resumed setup, round trips,
bulk, many connections) and the layers above (publish and subscribe, fetching a value, reconciling two sets,
delay-tolerant delivery). Scenarios are TOML files in `distributed/scenarios/`; a run writes its raw rows, its
conditions and a summary to `distributed/results/`, measures only on a quiet machine and says so when it could not.
With `--hosts` the same run places the nodes on real machines over SSH; that has run on one machine only
([#530](https://github.com/sourcenetwork/pinc/issues/530)).

`just compare` and `just distributed` compile every library for the machine that runs them (`-C target-cpu=native`)
and say so in their results. Every dependency is declared once, in its workspace's root `Cargo.toml`. The benchmarks
and the harness are workspaces of their own, so the other libraries and their runtimes never enter PINC's graph; the
gate checks that no crate under `crates/` depends on an async runtime and that nothing in the library's build
compiles C.

## Proofs

PINC's state machines and pure functions are specified in TLA+ and model checked with TLC, proved in Lean 4 without
bounds, and both are validated against traces recorded from the real Rust code. The other way round, the real code of
the endpoint's table of held first-flight fragments is driven along every edge of TLC's bounded state graph of its
model (model-based tests). Only the dependencies are taken on trust: the cryptographic primitives and Rust `core` and
`std` semantics. The crates marked proven above are covered in full; the others land crate by crate.
[docs/PROOFS.md](docs/PROOFS.md) has the property table, how each property is checked, the assumptions and what is
still being closed.

## Performance

Measured on one build host (AMD EPYC 7R13, 16 cores), PINC, iroh and rust-libp2p in one quiet window, medians of the
session of 15 November 2026 at commit `9dd66f05`. The best value of a row is in bold; a row PINC does not lead is
tracked in [#579](https://github.com/sourcenetwork/pinc/issues/579), which lists every such row, not only these.

| | PINC | iroh | rust-libp2p |
|---|---|---|---|
| Bulk on loopback, one stream (MiB/s) | **710** | 507 | 471 |
| CPU per byte moved, both ends (ns) | **2.66** | 4.83 | 5.03 |
| 64-byte round trip on loopback (us) | **69.2** | 93.5 | 75.5 |
| Connection setup on loopback (us) | **859** | 1,049 | 1,817 |
| 8 MiB over a 50 ms path with 1% loss (MiB/s) | **6.45** | 0.31 | 0.34 |
| Requests a second, 64 in flight on a 20 ms path | **2,801** | 2,287 | 48.2 |
| 1 MiB fetched over a WAN (ms) | **393** | 472 | 512 |
| 64 MiB fetched from three providers (ms) | 1,259 | 2,984 | **1,232** |
| A burst longer than a hub's log: messages lost | **0%** | 35.4% | 51.6% |
| First byte when 1,000 connections start at once (ms) | 814 | **316** | 1,039 |
| Memory per connection, client and server (KiB) | 177 and 113 | 178 and 120 | **107 and 88** |

The 1% loss row is an 8 MiB transfer; a 64 MiB fetch on the same path runs at 1.16 MiB/s against 0.31 and 0.32
([#564](https://github.com/sourcenetwork/pinc/issues/564)). `just compare` and the harness print every row, the ones
PINC loses included.
