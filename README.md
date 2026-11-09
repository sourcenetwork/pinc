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
- **Async without a runtime.** The async API is runtime-agnostic (plain `std` futures) and works under any executor,
  or under none.
- **Concurrency** is lock-free, through the [kovan](https://crates.io/crates/kovan) crates.
- **Hot path:** zero-copy parsing and no heap allocation in steady state are design rules.

> **Status: pre-release.** Most crates are built and tested, and their proofs land crate by crate. The Status column
> below says where each crate stands and [Open items](#open-items) lists what is not done.

## Use it

An echo through the `vinc` facade: one node accepts a stream on an ALPN and sends it back, another dials it by node id
and address. The async API needs no runtime; `block_on` here is the facade's own.

```rust
use vinc::{Vinc, block_on};

const ALPN: &[u8] = b"echo/1";

fn main() -> vinc::Result<()> {
    let lo = ([127, 0, 0, 1], 0).into();
    let server = Vinc::builder().alpn(ALPN).bind_addr(lo).bind_blocking()?;
    let client = Vinc::builder().bind_addr(lo).bind_blocking()?;
    let addr = server.addr(); // node id and socket address

    let echo = std::thread::spawn(move || {
        block_on(async {
            let conn = server.accept().await.expect("endpoint stopped").into_connection();
            let (mut tx, mut rx) = conn.accept_bi().await?;
            tx.write_all(&rx.read_to_end(1 << 20).await?).await?;
            tx.finish().await?;
            conn.closed().await; // dropping a connection closes it: wait for the client to finish reading
            Ok(())
        })
    });

    block_on(async {
        let conn = client.connect(addr, ALPN).await?;
        let (mut tx, mut rx) = conn.open_bi().await?;
        tx.write_all(b"hello, vinc").await?;
        tx.finish().await?;
        assert_eq!(rx.read_to_end(1 << 20).await?, b"hello, vinc");
        vinc::Result::Ok(())
    })?;
    echo.join().expect("echo thread")
}
```

The blocking mirror, `vinc::blocking`, is one call away (`.blocking()`) and has the same shape:

```rust
use vinc::Vinc;

fn main() -> vinc::Result<()> {
    let lo = ([127, 0, 0, 1], 0).into();
    let server = Vinc::builder().alpn(b"echo/1").bind_addr(lo).bind_blocking()?.blocking();
    let client = Vinc::builder().bind_addr(lo).bind_blocking()?.blocking();
    let addr = server.addr();

    let echo = std::thread::spawn(move || -> vinc::Result<()> {
        let (_node, _alpn, conn) = server.accept().expect("endpoint stopped");
        let (mut tx, mut rx) = conn.accept_bi()?;
        tx.write_all(&rx.read_to_end(1 << 20)?)?;
        tx.finish()?;
        conn.closed(); // dropping a connection closes it: wait for the client to finish reading
        Ok(())
    });

    let conn = client.connect(addr, b"echo/1")?;
    let (mut tx, mut rx) = conn.open_bi()?;
    tx.write_all(b"hello, vinc")?;
    tx.finish()?;
    assert_eq!(rx.read_to_end(1 << 20)?, b"hello, vinc");
    drop((conn, tx, rx)); // the last handle closes the connection
    echo.join().expect("echo thread")
}
```

## Layout

| Path | What |
|---|---|
| `crates/` | the library, one crate per component |
| `proofs/` | TLA+ specifications (TLC) and Lean 4 proofs, both validated against traces of the real code |
| `tests/` | every test (integration, property, scenario, trace), run with [cargo-nextest](https://nexte.st) |
| `benches/` | micro benchmarks: per packet, allocations, copies |
| `docs/` | [PROOFS.md](docs/PROOFS.md): what is proven, how it is checked, the assumptions |
| `scripts/` | the gate and the proof runner |

## Crates

| Crate | What it does | `no_std` | Status |
|---|---|---|---|
| `vinc` | the facade: a builder, connections, `futures-io` streams and datagrams, with a runtime-agnostic async API and a blocking API | std | built; proofs being closed |
| `vinc-wire` | varints and a strict canonical DAG-CBOR codec, parsed in place | yes | built, proven |
| `vinc-dag` | content-addressed blocks and CIDs, value roots, range proofs, verified-range sets; usable on its own | yes, heap-free | built, proven |
| `vinc-crypto` | RustCrypto primitives behind one static `Provider`: AEADs, X25519, ML-KEM-768, Ed25519, P-256 and ML-DSA-65 identities, BLAKE3 KDF and transcript hash | yes | built; proofs being closed |
| `vinc-keystore` | long-term keys behind a `KeyStore` trait; a software store, and a pure-Rust TPM 2.0 store with `hwenc` | no | built; proofs being closed |
| `vinc-security` | hybrid post-quantum handshake, ticket resumption with 0-RTT, key schedule, packet protection, key roll, amplification budget | yes | built, proven |
| `vinc-transport` | VINCER: streams, datagrams, flow and congestion control, loss recovery, pacing, path MTU, migration | yes | built; proofs being closed |
| `vinc-core` | the SANS-IO endpoint: host interface, protocol dispatch, commands, events and queries | yes | built; proofs being closed |
| `vinc-connect` | TCP and WebSocket carriers, relays, signed records and lookup, hole punching, the hub tunnel, the mailbox | yes | built; relay side proven |
| `vinc-membership` | hub roster and member view: leases, independent-path probes, restart-safe incarnations, leave, revocation | yes | built; proofs being closed |
| `vinc-values` | verified streaming of values of any size from up to four providers, with resume and zero-copy serving | yes | built, proven; corrections being made |
| `vinc-broadcast` | topic broadcast through hubs with origin authentication, replay floors and a bounded log | yes | built; proofs being closed |
| `vinc-reconcile` | range-based set reconciliation whose cost scales with the difference, exact by a final check | yes | built; proofs being closed |
| `vinc-dtn` | bundles sealed to a recipient, erasure coding, custody and copy-limited forwarding | yes | built, proven |
| `vinc-driver` | the reference driver: the endpoint on one thread over a std UDP socket | no | built; proofs being closed |
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
```

Every dependency is declared once, in the root `Cargo.toml`, and every crate has the one workspace version. The
gate also checks that no crate under `crates/` depends on an async runtime and that nothing in the build compiles C.

## Proofs

VINC's state machines and pure functions are specified in TLA+ and model checked with TLC, proved in Lean 4 without
bounds, and both are validated against traces recorded from the real Rust code. Only the dependencies are taken on
trust: the cryptographic primitives and Rust `core` and `std` semantics. The crates marked proven above are covered in
full; the others land crate by crate. [docs/PROOFS.md](docs/PROOFS.md) has the property table, how each property is
checked, the assumptions and what is still being closed.

## Open items

- The proofs listed under [Being closed](docs/PROOFS.md#being-closed).
- `vinc-values`: five corrections found by its proofs are being made.
- On loopback and other very fast paths a session is given up after about a second of silence, so a host stall that
  long drops it. An absolute silence floor is being added; the 1000-session test waits for it.
- The scenario suite passes every gate on every seed it runs; the two scenarios that need the values and reconcile
  layers in one composition wait for them.
- The comparisons with iroh and rust-libp2p, and the distributed tests, are not in the tree yet.
