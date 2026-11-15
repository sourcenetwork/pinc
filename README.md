<p align="center">
  <img src="art/vinc-banner.png" alt="VINC: next-gen peer-to-peer networking stack" width="100%">
</p>

**VINC** stands for **V**erified **I**dentity-**N**ative **C**onnectivity:

- *Verified*: every session is mutually authenticated, and a value is checked against its root before the
  application sees a byte of it.
- *Identity-native*: a node is reached by its id, which is derived from its key, not by an address.
- *Connectivity*: one stack that connects nodes directly, through relays, and across links that are not there all
  the time.

**VINCER**, the transport VINC runs on, stands for **VINC** **E**ncrypted **R**eliable transport.

VINC is a peer-to-peer networking stack for Rust, written SANS-IO. It has its own encrypted, reliable transport
(VINCER) with a hybrid post-quantum handshake (X25519 plus ML-KEM-768). The hybrid claim is the full handshake's: a
resumed session runs no ML-KEM, so its keys are as secret as its ticket's key (which a full handshake set up), and the
key roll is an X25519 ratchet, so with X25519 broken it does not recover a session whose keys were stolen. On top of
that core it builds membership, verified value transfer with no size limit, broadcast, set reconciliation and
delay-tolerant delivery. It runs from a microcontroller to a data centre and in the browser, and you write your own
protocols on top of it.

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
> reaches peers directly and through relays, broadcasts on topics through a hub, looks a peer up by its id, and can
> itself be the hub and relay of other nodes. The two measured cases in which broadcast lost messages lose none now.
> The Status column says where each crate stands and [Open items](#open-items) lists what is not done, with the issue
> that tracks each.

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
| `vinc` | the facade: a builder, connections, streams with urgencies, datagrams, an access hook and revocation, all async, over the host's receive, send and sleep closures | std | built: direct and relayed connections, topic broadcast, lookup by id, state export and restore, the hub and relay roles; proofs being closed |
| `vinc-wire` | varints and a strict canonical DAG-CBOR codec, parsed in place | yes | built, proven |
| `vinc-dag` | content-addressed blocks and CIDs, value roots, range proofs, verified-range sets; usable on its own | yes, heap-free | built, proven |
| `vinc-crypto` | RustCrypto primitives behind one static `Provider`: AEADs, X25519, ML-KEM-768, Ed25519, P-256 and ML-DSA-65 identities, BLAKE3 KDF and transcript hash | yes | built; proofs being closed |
| `vinc-keystore` | long-term keys behind a `KeyStore` trait; a software store, and a pure-Rust TPM 2.0 store with `hwenc` | no | built; proofs being closed |
| `vinc-security` | hybrid post-quantum handshake, ticket resumption with 0-RTT, key schedule, packet protection, key roll, amplification budget | yes | built, proven |
| `vinc-transport` | VINCER: streams, datagrams, flow and congestion control, loss recovery, pacing, path MTU, migration | yes | built; proofs being closed |
| `vinc-core` | the SANS-IO endpoint: host interface, protocol dispatch, commands, events and queries | yes | built; proofs being closed |
| `vinc-node` | one composition of the endpoint, the connectivity client and every layer over real sessions; membership, broadcast, values, reconcile and delay-tolerant delivery are in | yes | built; the scenario suite and the facade run on it; proofs being closed |
| `vinc-connect` | TCP and WebSocket carriers, relays, signed records and lookup, hole punching, the hub tunnel, the mailbox | yes | built; relay side proven, with its record store and lookup, the protected carrier's records and its WebSocket framing |
| `vinc-portmap` | port mapping: asks the home gateway for a UDP mapping with PCP, then NAT-PMP, then UPnP-IGD, renews it, notices a gateway that restarted and releases it on shutdown; the node publishes the mapped address, and is port-mapped, once a relay saw the node at its IP; off unless the builder turns it on | yes, heap-free | built; lease model and codec proofs |
| `vinc-membership` | hub roster and member view: leases, independent-path probes, restart-safe incarnations, leave, revocation | yes | built; proofs being closed |
| `vinc-values` | verified streaming of values of any size from up to four providers, with resume and zero-copy serving | yes | built, proven |
| `vinc-broadcast` | topic broadcast through hubs with origin authentication, replay floors and a bounded log | yes | built, proven (the liveness theorems cover runs without restarts) |
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
just proofs       # Lean proofs, TLC model checking, trace validation and model-based tests
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
bounds, and both are validated against traces recorded from the real Rust code. The other way round, the real code of
the endpoint's table of held first-flight fragments is driven along every edge of TLC's bounded state graph of its
model (model-based tests). Only the dependencies are taken on trust: the cryptographic primitives and Rust `core` and
`std` semantics. The crates marked proven above are covered in full; the others land crate by crate.
[docs/PROOFS.md](docs/PROOFS.md) has the property table, how each property is checked, the assumptions and what is
still being closed.

## Open items

As of 15 November 2026, at the commit that carries this text. Every item names the issue that tracks it.

- **Message loss in broadcast.** The cases that lost messages lose none now, in three repetitions each in the
  harness. A burst of 2,000 messages of 4 KiB through a hub to ten subscribers lost 1.35% to 21% and loses 0, as
  iroh and rust-libp2p do ([#109](https://github.com/sourcenetwork/vinc/pull/109)). A site cut off for 15 seconds
  lost 1.4% to 6.6% and loses 0, where rust-libp2p loses 15.8%
  ([#111](https://github.com/sourcenetwork/vinc/pull/111)). A burst of 6,000 messages, longer than a hub's log of a
  topic, loses 0 of 60,000 deliveries where iroh and rust-libp2p lose about half
  ([#115](https://github.com/sourcenetwork/vinc/pull/115)): a publisher is told when its hub has room and a
  subscriber that fell behind is brought up from the log. The price is the median delivery time of such a burst,
  7.0 s. A subscriber the hub cannot give every message (it was away while the log moved on, or it fell too far
  behind) is told so by the hub, and the application hears it as `Event::Missed`
  ([#505](https://github.com/sourcenetwork/vinc/issues/505),
  [#507](https://github.com/sourcenetwork/vinc/issues/507)).
- **The facade** reaches peers directly and through relays, and has topic broadcast through a hub, lookup of a peer
  by its id through signed records, export and restore of its state, revocation, stream urgency, and two stream calls
  that pass a buffer instead of copying it (`RecvStream::read_with`, `SendStream::send_owned`). One endpoint can be
  hub and relay for other nodes (`Builder::relay_role`), run by its own `run` with nothing beside it. A session
  carries 100 streams each way, and a stream the peer opened gives its place back when its answer has left
  ([#128](https://github.com/sourcenetwork/vinc/pull/128)). Not yet: a build without `std`, which the crates below
  the facade have; the plan is in [#99](https://github.com/sourcenetwork/vinc/issues/99) and its first phases are
  written but not merged: one of them raised a server's memory per connection, which is being looked into. An owned
  buffer written in the middle of a stream.
- **Performance on loopback.** On the build host (15 November 2026, commit `9dd66f05`, all three stacks in one quiet
  window) VINC leads iroh and rust-libp2p on bulk throughput (710 against 507 and 471 MiB/s on one stream, 678
  against 489 and 460 on sixteen), on CPU per byte (2.66 against 4.83 and 5.03 ns), on the 64-byte round trip (69
  against 94 and 76 microseconds) and on connection setup (859 microseconds against 1,049 and 1,817). A client's
  memory per connection is level with iroh's and behind rust-libp2p's, 177 KiB against 178 and 107 (it was 250), and
  a server's lies between them, 113 against 120 and 88. The memory of an idle endpoint was last measured on
  13 November on a c7i.4xlarge, 5.8 MiB against 3.3 and 0.6 (it was 6.3)
  ([#158](https://github.com/sourcenetwork/vinc/issues/158)). It is behind on the time to the first byte when 1000
  connections start at once (814 ms against iroh's 316,
  [#157](https://github.com/sourcenetwork/vinc/issues/157)).
- **Performance on the emulated network** (containers on the build host, the same session, three repetitions,
  medians). Under 1% loss on a 50 ms path a transfer runs at 6.65 MiB/s against 0.33 and 0.34. Requests on a stream
  each over a 20 ms path, 512-byte bodies: with 64 in flight 2,801 a second against 2,287 for iroh and 48 for
  rust-libp2p, the slowest hundredth at 25.9 ms against 40.4; with 4 KiB bodies 2,729 against 2,005, and 2,733
  against 1,702 when 256 are asked for, where the slowest hundredth is 104 ms against iroh's 228. Fetching a value
  over a WAN: 1 KiB in 104 ms against 114 and 155, 1 MiB in 393 ms against 472 and 512, 64 MiB in 6.06 s against 6.24
  and 6.47, 256 MiB level with iroh (23.35 s against 23.32), and 64 MiB from three providers at once in 1.26 s,
  level with rust-libp2p's 1.23 s, against 2.98 s for iroh.
  Behind:
  - one stream on a clean 150 ms path moves 10.8 MiB/s, where it moved 12.1 on 12 November (iroh 5.68; the
    change that did it is being looked for, [#156](https://github.com/sourcenetwork/vinc/issues/156)), and sixteen streams there move 9.64 MiB/s against iroh's
    11.2 ([#159](https://github.com/sourcenetwork/vinc/issues/159));
  - one stream on a LAN, 84.4 against 90.9 MiB/s ([#159](https://github.com/sourcenetwork/vinc/issues/159)), and a burst of 500 connections there, 0.93 s
    against 0.56 s ([#157](https://github.com/sourcenetwork/vinc/issues/157));
  - the slowest hundredth of requests with 16 in flight (23.9 ms against 21.2, [#94](https://github.com/sourcenetwork/vinc/issues/94));
  - the median delivery of a topic message on a LAN (748 microseconds against 438, two hops by design,
    [#102](https://github.com/sourcenetwork/vinc/issues/102)) and of a burst of 2,000 updates through a hub (3.46 s against iroh's 1.27 s, level with
    rust-libp2p, [#161](https://github.com/sourcenetwork/vinc/issues/161));
  - CPU on a large value fetched from one provider, per received packet in the node: with the library's share of
    [#523](https://github.com/sourcenetwork/vinc/issues/523) alone, 1.47 s over all nodes for 64 MiB against 1.34 and
    1.45, and 5.62 s for 256 MiB against 5.48 and 5.79 (15 November, c7i.4xlarge,
    [#163](https://github.com/sourcenetwork/vinc/issues/163)); the harness's own node program, which added to the row
    a cost iroh's never had, no longer does;
  - three setup rows: the median on a LAN, the resumed median on a slow lossy path and the tail at 1% loss
    ([#160](https://github.com/sourcenetwork/vinc/issues/160)).

  Against the session of 13 November (commit `6355d7d`) 327 of 383 values are inside that session's spread. A
  second session the same day on `79cfc653`, after the changes that landed in between, has 353 of 383 values
  inside the first one's spread (a repeat of one build gave 214 of 223). The rows that are still above 13 November, and what is known of each, are in
  [#485](https://github.com/sourcenetwork/vinc/issues/485).

  `just compare` and the harness print every row, the ones VINC loses included.
- **Transport and connectivity rules not in yet.** Two changes that bring the library closer to the reference model
  are written, tested and held back: a hub's floor that covers a message sent after a member's restart
  ([#340](https://github.com/sourcenetwork/vinc/issues/340)), and an amplification ledger that asks for evidence
  before it validates an address ([#251](https://github.com/sourcenetwork/vinc/issues/251)). Each loses one or two
  deliveries in a few low-bandwidth and mobile seeds, and they stay out until that is explained. The three held
  back with them (the rules for a dial's first flight, the punch round that probes unvalidated direct paths again,
  the hub tunnel with the longer life of an unauthenticated session on a thin node) landed in
  [#517](https://github.com/sourcenetwork/vinc/pull/517).
- **The scenario suite** passes every gate on the seeds it runs by default, the mobile scenario included
  ([#134](https://github.com/sourcenetwork/vinc/pull/134)). The full run over 96 seeds depends on which packets the
  emulated links lose, so it is read over eight realizations of that loss (`VINC_SUITE_LOSS_SALT`): the library passes
  87 to 90 of the 96 seeds, 89 on average and 90 in the realization the suite runs by itself; the reference model the
  rules come from passes 88 in its own. Four seeds fail in every realization, and they are four the model fails too
  ([#212](https://github.com/sourcenetwork/vinc/issues/212)). The others are deliveries on low-bandwidth links that
  miss their deadline in some realizations and not in others
  ([#516](https://github.com/sourcenetwork/vinc/issues/516)); the low-bandwidth scenario's default seed is therefore
  one whose result does not depend on the draw, and the one that does stays in the full run. The two scenarios that
  need the values and reconcile layers in one composition wait for them.
- **The proofs** land with the code: a fix whose behaviour a model covers carries the model's update in the same pull
  request. What is still to prove or to check again is listed in
  [#105](https://github.com/sourcenetwork/vinc/issues/105), beside [Being closed](docs/PROOFS.md#being-closed).
- `vinc-values`: the five corrections found by its proofs are made and proven. One of them, the stall timer armed by the
  first request, was changed again on purpose (the stall rule now starts at the first verified granule), and the models
  follow it ([#190](https://github.com/sourcenetwork/vinc/pull/190)).
- **The harness** has run on no machine but the build host's containers; the Terraform for separate machines is in
  `distributed/infra/` and has not been applied. A scenario can ask for the VINC nodes' traces and packet logs
  (`[debug] trace = true`, [#126](https://github.com/sourcenetwork/vinc/pull/126)).
- **Planned.** Forward erasure correction as an option, off by default, that an application switches on through the
  builder ([#145](https://github.com/sourcenetwork/vinc/issues/145)).
- **Known gaps, each small.** On a topic with more subscribers than a hub lists (256 by default) a member the list
  leaves out is subscribed and is never told so ([#483](https://github.com/sourcenetwork/vinc/issues/483)). Port
  mapping skips a few cases the reviews named: an IPv6 gateway for NAT-PMP, a relative control URL in a UPnP
  description, a local address that changes ([#476](https://github.com/sourcenetwork/vinc/issues/476)). When two
  indices derive the same connection id, the highest index a connection has seen can run ahead of or stay behind the
  one its peer used, so an index the peer may still use can lose its id; found by a model, not seen in a run
  ([#463](https://github.com/sourcenetwork/vinc/issues/463)).
