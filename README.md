<p align="center">
  <img src="art/vinc-banner.png" alt="VINC: next-gen peer-to-peer networking stack" width="100%">
</p>

VINC is a peer-to-peer networking stack for Rust, written SANS-IO. It has its own encrypted, reliable transport
(VINCER) with a hybrid post-quantum handshake (X25519 plus ML-KEM-768). On top of that core it builds membership,
verified value transfer with no size limit, broadcast, set reconciliation and delay-tolerant delivery. It runs from a
microcontroller to a data centre and in the browser, and you write your own protocols on top of it.

VINC is a library, not a framework:
- **No runtime dependency.** The protocol crates are state machines: you give them bytes, time and commands, and they
  give back packets to send, timers and events. VINC depends on no async runtime.
- **The host owns the runtime.** You pass the facade your I/O as three async closures (receive a datagram, send a
  datagram, sleep until an instant) and call async methods. It starts no thread, no task and no socket loop: the futures
  you await drive the endpoint, on your executor and your core. tokio, smol and nuclei all work.
- **One endpoint per core.** An endpoint's handles stay on the thread that built it, so nothing is shared between
  threads and nothing is locked: the host spawns their futures with its executor's local spawn and runs one endpoint
  per core.
- **Hot path:** zero-copy parsing and no heap allocation in steady state are design rules.

> **Status: pre-release.** The protocol crates are built and tested, and their proofs land crate by crate. The facade
> serves direct connections today; relays, broadcast and lookup exist in the crates below it and are not yet reachable
> through it. The Status column says where each crate stands and [Open items](#open-items) lists what is not done.

## Usage

An echo over loopback. The host's whole contribution is the three closures; here they sit on a
[nuclei](https://crates.io/crates/nuclei) UDP socket. Hosts with no executor drive the SANS-IO crates (`vinc-core`)
directly.

```rust
use std::net::{SocketAddr, UdpSocket};
use std::sync::Arc;
use std::time::Instant;

use nuclei::Handle;
use nuclei::time::sleep_until_precise;
use vinc::{Endpoint, Hosted, Vinc};

const ALPN: &[u8] = b"echo/1";

async fn bind() -> vinc::Result<Endpoint<impl Hosted>> {
    let any = SocketAddr::from(([127, 0, 0, 1], 0));
    let sock = Arc::new(Handle::<UdpSocket>::bind(any).await.expect("bind"));
    let (rx, tx) = (Arc::clone(&sock), Arc::clone(&sock));
    Vinc::builder().alpn(ALPN).local_addr(sock.local_addr().expect("address")).build(
        async move |buf: &mut [u8]| rx.recv_from(buf).await,         // receive a datagram
        async move |pkt: &[u8], to: SocketAddr| tx.send_to(pkt, to).await, // send a datagram
        async |at: Instant| sleep_until_precise(at).await,           // sleep until a deadline
    )
}

#[nuclei::main]
async fn main() -> vinc::Result<()> {
    let (server, client) = (bind().await?, bind().await?);
    let addr = server.addr(); // node id and socket address

    let accept = nuclei::spawn_local(async move {
        let conn = server.accept().await.expect("endpoint stopped").into_connection();
        let (mut tx, mut rx) = conn.accept_bi().await?;
        tx.write_all(&rx.read_to_end(1 << 20).await?).await?;
        tx.finish().await?;
        conn.closed().await; // dropping a connection closes it: wait for the client to finish reading
        vinc::Result::Ok(())
    });

    let conn = client.connect(addr, ALPN).await?;
    let (mut tx, mut rx) = conn.open_bi().await?;
    tx.write_all(b"hello, vinc").await?;
    tx.finish().await?;
    assert_eq!(rx.read_to_end(1 << 20).await?, b"hello, vinc");
    conn.close(0).await;
    accept.await
}
```

An endpoint with no future being polled makes no progress, which is the SANS-IO contract. Every call drives the endpoint
while it waits; a host with nothing else pending on it (a server between accepts, connections that only need their
keepalives) awaits `Endpoint::run()`.

## Layout

| Path | What |
|---|---|
| `crates/` | the library, one crate per component |
| `proofs/` | TLA+ specifications (TLC) and Lean 4 proofs, both validated against traces of the real code |
| `tests/` | every test (integration, property, scenario, trace), run with [cargo-nextest](https://nexte.st) |
| `benches/` | micro benchmarks (per packet, allocations, copies) and the loopback comparison with iroh and rust-libp2p; a workspace of its own |
| `distributed/` | the distributed test harness: one binary that builds an emulated network of containers, runs VINC, iroh and rust-libp2p nodes on it with faults, measures them and serves a dashboard; a workspace of its own |
| `docs/` | [PROOFS.md](docs/PROOFS.md): what is proven, how it is checked, the assumptions |
| `scripts/` | the gate and the proof runner |

## Crates

| Crate | What it does | `no_std` | Status |
|---|---|---|---|
| `vinc` | the facade: a builder, connections, streams with urgencies, datagrams, an access hook and revocation, all async, over the host's receive, send and sleep closures | std | built for direct connections; proofs being closed |
| `vinc-wire` | varints and a strict canonical DAG-CBOR codec, parsed in place | yes | built, proven |
| `vinc-dag` | content-addressed blocks and CIDs, value roots, range proofs, verified-range sets; usable on its own | yes, heap-free | built, proven |
| `vinc-crypto` | RustCrypto primitives behind one static `Provider`: AEADs, X25519, ML-KEM-768, Ed25519, P-256 and ML-DSA-65 identities, BLAKE3 KDF and transcript hash | yes | built; proofs being closed |
| `vinc-keystore` | long-term keys behind a `KeyStore` trait; a software store, and a pure-Rust TPM 2.0 store with `hwenc` | no | built; proofs being closed |
| `vinc-security` | hybrid post-quantum handshake, ticket resumption with 0-RTT, key schedule, packet protection, key roll, amplification budget | yes | built, proven |
| `vinc-transport` | VINCER: streams, datagrams, flow and congestion control, loss recovery, pacing, path MTU, migration | yes | built; proofs being closed |
| `vinc-core` | the SANS-IO endpoint: host interface, protocol dispatch, commands, events and queries | yes | built; proofs being closed |
| `vinc-node` | one composition of the endpoint, the connectivity client and every layer over real sessions; membership, broadcast, values, reconcile and delay-tolerant delivery are in | yes | built; write-through proofs, stream urgencies, FLOOR_PUSH, the hub's relay duties and restart of held bundles are in; the scenario runner and the facade move onto it next |
| `vinc-connect` | TCP and WebSocket carriers, relays, signed records and lookup, hole punching, the hub tunnel, the mailbox | yes | built; relay side proven |
| `vinc-membership` | hub roster and member view: leases, independent-path probes, restart-safe incarnations, leave, revocation | yes | built; proofs being closed |
| `vinc-values` | verified streaming of values of any size from up to four providers, with resume and zero-copy serving | yes | built, proven; corrections being made |
| `vinc-broadcast` | topic broadcast through hubs with origin authentication, replay floors and a bounded log | yes | built; proofs being closed |
| `vinc-reconcile` | range-based set reconciliation whose cost scales with the difference, exact by a final check | yes | built; proofs being closed |
| `vinc-dtn` | bundles sealed to a recipient, erasure coding, custody and copy-limited forwarding | yes | built, proven |
| `vinc-sim` | deterministic network simulator and scenario suite: links, sites, NAT, partitions, clocks, adversaries | no | built |

**proven**: every property has a TLA+ model, a Lean theorem and trace validation ([docs/PROOFS.md](docs/PROOFS.md)).

## Build and test

The [justfile](justfile) holds every task; CI runs the same recipes.

```sh
just setup        # install everything: system packages, the Rust toolchain, cargo-nextest, Lean, the TLA+ tools
just              # list the recipes
just gate         # everything a change must pass: checks, tests, doctests, proofs
just checks       # dependency rules, format, lints, docs, no_std builds, pure Rust
just test         # every test with cargo-nextest (the hwenc TPM tests need swtpm); just test-default skips hwenc
just proofs       # Lean proofs, TLC model checking and trace validation
just tla-tools    # install the pinned TLA+ tools the proofs use
just bench        # micro benchmarks
just compare      # VINC against iroh and rust-libp2p on loopback (run it on an otherwise idle machine; needs sudo and tc)
just distributed run distributed/scenarios/wan.toml   # a scenario on an emulated network (Docker and sudo)
just distributed run distributed/scenarios/wan.toml --hosts fleet.toml   # the same on real machines over SSH (see distributed/infra)
just distributed serve                                # the dashboard, on http://127.0.0.1:7878
just distributed clean                                # remove whatever a run left
just e2e          # the harness end to end: a two-node scenario, every stack (Docker and sudo)
```

The distributed harness gives every node its own container and network stack, wired by veth pairs, bridges and a
router per site, with an MTU of 1500, `tc netem` shaping each direction of each link, and address translation where a
scenario puts a node behind a home router. Scenarios are TOML files in `distributed/scenarios/`; each run writes its
raw rows, its conditions (machine, CPU sets, versions) and a summary table to `distributed/results/`. A run measures
only on a quiet machine and says so when it could not. The dashboard composes scenarios, shows a run live and compares
results. The harness runs the transport tests (connection setup, resumed setup, request latency, one and 16 stream
throughput, many connections) and the layers above them on nodes that stay up for a whole repetition: publish and
subscribe fan-out (delivery latency, losses, duplicates, bytes on the wire per delivered message), syncing a value from
one or several providers, and reconciling two sets, each for VINC (the node on a real-socket host in
`distributed/src/node/vinc`), iroh (gossip and blobs) and rust-libp2p (gossipsub and a request-response protocol),
configured as each documents and said so in the results; where a stack has no equivalent the table says "not
available". One machine emulates the whole network, and every table says so.

The same run can place the nodes on real machines over SSH (`--hosts fleet.toml`, the file `distributed/infra` writes or
one written by hand): each node is a program in its own systemd scope with its own CPUs and memory, the network is the
machines' own, and `tc netem` on their egress adds the scenario's shapes between sites. It has run on one machine (the
build host as a fleet of one, where there is no network between nodes to shape) and its shaping commands were checked
on a virtual link pair; it has not run on several machines.

`just compare` and `just distributed` compile every stack for the machine that runs them (`-C target-cpu=native`) and
say so in their results. A host gets the same from VINC by building its own binary that way: on an x86-64 CPU with
VAES and no AVX-512 the AES code VINC uses takes its 256-bit path only when it is compiled for that CPU.

Every dependency is declared once, in its workspace's root `Cargo.toml`, and every crate has the one version. The
benchmarks are a workspace of their own, so iroh, rust-libp2p, their runtime and their C code never enter the
library's graph. The gate also checks that no crate under `crates/` depends on an async runtime and that nothing in
the library's build compiles C.

## Proofs

VINC's state machines and pure functions are specified in TLA+ and model checked with TLC, proved in Lean 4 without
bounds, and both are validated against traces recorded from the real Rust code. Only the dependencies are taken on
trust: the cryptographic primitives and Rust `core` and `std` semantics. The crates marked proven above are covered in
full; the others land crate by crate. [docs/PROOFS.md](docs/PROOFS.md) has the property table, how each property is
checked, the assumptions and what is still being closed.

## Open items

- **The facade** reaches peers directly and through relays, and has topic broadcast through a hub, lookup of a peer
  by its id through signed records, export and restore of its state, revocation, stream urgency, and two stream calls
  that pass a buffer instead of copying it (`RecvStream::read_with`, `SendStream::send_owned`). Not yet: the relay
  role (`vinc::relay`) run by the endpoint's own driver, so that one endpoint is hub and relay with nothing beside it;
  an owned buffer written in the middle of a stream; a build without `std` (the crates below the facade have one).
- **Performance.** On loopback on the build host (12 November 2026, commit `38301fc`, all three in one quiet window)
  VINC leads iroh and rust-libp2p on bulk throughput (699 against 518 and 462 MiB/s on one stream), on CPU per byte
  (2.71 against 4.75 and 5.14 ns), on the 64-byte round trip (68 against 93 and 78 microseconds) and on connection
  setup. It is behind on the memory of an idle endpoint (6.3 MiB against 3.3 and 0.6), on a client's memory per
  connection (277 KiB against 185 and 107) and on the time to the first byte when 1000 connections start at once
  (834 ms against iroh's 323). The emulated-network scenarios were last measured before these changes. `just compare`
  and the harness print every row, the ones VINC loses included.
- **The harness** has run on no machine but the build host's containers; the Terraform for separate machines is in
  `distributed/infra/` and has not been applied.
- **The proofs** listed under [Being closed](docs/PROOFS.md#being-closed).
- `vinc-values`: five corrections found by its proofs are being made.
- **The scenario suite** passes every gate on every seed it runs; the two scenarios that need the values and reconcile
  layers in one composition wait for them.
