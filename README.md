# VINC

VINC is a peer-to-peer networking stack for Rust, written SANS-IO. It has its own encrypted, reliable transport
(VINCER) with a hybrid post-quantum handshake (X25519 plus ML-KEM-768). On top of that core it builds membership,
verified value transfer with no size limit, broadcast, set reconciliation and delay-tolerant delivery. It runs from a
microcontroller to a data centre and in the browser, and you write your own protocols on top of it.

VINC is a library, not a framework:
- **No runtime dependency.** The protocol crates are state machines: you give them bytes, time and commands, and they
  give back packets to send, timers and events. VINC depends on no async runtime.
- **Async without a runtime.** The async API is runtime-agnostic (plain `std` futures) and works under any executor,
  or under none.
- **Concurrency** is lock-free, through the [kovan](https://crates.io/crates/kovan) crates.
- **Hot path:** zero-copy parsing and no heap allocation in steady state are design rules.

> **Status: under construction.** The crates are built one at a time. The Status column below says which exist;
> nothing in this README claims more than that.

## Layout

| Path | What |
|---|---|
| `crates/` | the library, one crate per component (table below) |
| `proofs/tla/` | TLA+ specifications, model checked with TLC, plus trace validation of the implementation |
| `proofs/lean/` | Lean 4 models and proofs of the same state machines, checked against the same traces |
| `tests/` | every test (integration, property, scenario, trace), run with [cargo-nextest](https://nexte.st) |
| `benches/` | micro benchmarks (per packet, allocations, copies) and comparisons with iroh and rust-libp2p |
| `distributed/` | multi-node tests of VINC, iroh and rust-libp2p on shaped networks |
| `scripts/gate.sh` | the checks every change must pass |

## Crates

| Crate | Component | What it does | `no_std` | Status |
|---|---|---|---|---|
| `vinc-wire` | encodings | varints and a strict canonical DAG-CBOR codec, parsed in place from borrowed bytes | yes | in progress |
| `vinc-dag` | lite DAG | DefraDB blocks and CIDs, value roots and range proofs, verified-range sets, reconciliation summaries; no networking code, usable on its own | yes, heap-free mode | in progress |
| `vinc-crypto` | primitives | the vetted primitives behind one static interface: X25519, ML-KEM-768, Ed25519, ChaCha20-Poly1305, BLAKE3 | yes | planned |
| `vinc-security` | security | hybrid handshake, key schedule, record protection, replay window, address validation, anti-amplification | yes | planned |
| `vinc-transport` | VINCER | streams, datagrams, flow control, loss recovery, congestion control, pacing, path MTU, connection ids, migration | yes | planned |
| `vinc-core` | endpoint | the SANS-IO endpoint: host interface, protocol registration and dispatch, commands, events and queries | yes | planned |
| `vinc-connect` | connectivity | reachability, relays, carriers (TCP, WebSocket), rendezvous, keepalive, mailbox | yes | planned |
| `vinc-membership` | membership | membership views, epochs, failure detection, member records, revocation | yes | planned |
| `vinc-values` | values | verified streaming of values of any size from one or many providers, with resume | yes | planned |
| `vinc-broadcast` | broadcast | topic broadcast with origin authentication | yes | planned |
| `vinc-reconcile` | reconciliation | set reconciliation whose cost scales with the difference | yes | planned |
| `vinc-dtn` | delay tolerance | delay-tolerant bundles with custody | yes | planned |
| `vinc-driver` | driver | std sockets and OS readiness polling around the SANS-IO endpoint | no (std) | planned |
| `vinc` | facade | one entry point, with the runtime-agnostic async API and the blocking API | std feature | planned |
| `vinc-sim` | testing | deterministic network simulator for scenario and trace tests | no | planned |

## Build and test

```sh
cargo build --workspace
cargo nextest run --workspace --all-features   # every test
scripts/gate.sh                                # format, lints, docs, no_std builds, tests
```

`benches/` and `distributed/` are separate Cargo workspaces. They depend on iroh and rust-libp2p, and with them on an
async runtime; no VINC crate does.

## Proofs

`proofs/tla/` and `proofs/lean/` model the same state machines as the crates: the handshake, the record layer, streams,
membership, reconciliation and authorization. They are kept identical to the code by validating the same traces:
- The Rust implementation emits a versioned trace.
- TLC validates that trace against the TLA+ specification.
- The Lean step relation replays it.
