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

Every dependency is declared once, in the root `Cargo.toml`, and every crate has the one workspace version; the gate
checks both. `benches/` is a workspace member whose comparison dependencies (iroh, rust-libp2p and their async
runtime) belong to the bench package only: the gate also checks that no crate under `crates/` depends on an async
runtime.

```sh
cargo bench -p vinc-benches                    # micro benchmarks
```

## Proofs

`proofs/tla/` and `proofs/lean/` hold specifications and proofs of the first crates' state machines and pure
functions, kept identical to the Rust code by validating recorded traces of the code against both. The rest of the
protocol is not specified here yet.

How it is checked, by `scripts/proofs.sh` (the `== proofs` step of `scripts/gate.sh`):
- **Lean** (`proofs/lean`, a Lake package on core Lean and Std, no Mathlib): `lake build` checks every proof. A script
  rejects `sorry`, `admit`, `axiom` and `native_decide` in the sources, and the build fails if any declaration of the
  package depends on an axiom beyond `propext`, `Classical.choice` and `Quot.sound` (`#audit_package`, plus a
  printed `#audit_axioms` line for every main theorem).
- **TLC** model checks every TLA+ config in `proofs/tla` over the bounds in the table.
- **Trace validation.** The Rust test `tests/trace_ranges.rs` runs seeded random sequences through the public API of
  `VerifiedRanges<N>`, `VerifiedRangesVec`, `varint` and `Layout`, compares every answer with a naive reference, and,
  when `VINC_TRACE_DIR` is set, writes them as ndjson. TLC then checks that the recorded insert sequence is a
  behaviour of `VerifiedRanges.tla` (`TraceVerifiedRanges.tla`: every step is an `Insert` step with the run's
  capacity, and the recorded `covered_len`, `contains` and `contains_range` equal the specification's), and
  `lake exe replay` replays the ranges, varint and layout traces against the Lean functions and fails on any
  difference.

Tools: Lean 4 and Lake, TLC on `PATH` as `tlc`, Java, and for the trace check a TLC of the same era as the
[CommunityModules](https://github.com/tlaplus/CommunityModules) jar (the gate prints the download command when a
jar is missing).

| Property | Rust item | TLA+ | Lean theorem | Assumptions | Trace validation |
|---|---|---|---|---|---|
| varint round trip: `decode(encode(v) ++ rest) = (v, len)` | `varint::encode`, `varint::decode` | none: a pure function | `Varint.decode_encode` | `v < 2^63` | Lean replay of random values and encodings, both at the edges and uniform in bit width |
| one accepted encoding per value: an accepted prefix is exactly `encode(v)` | `varint::decode` | none | `Varint.decode_canonical`, `Varint.unique_encoding` | bytes are below 256 | Lean replay of random byte strings, including too long, truncated and non-minimal |
| encoded length is `encoded_len(v)` and at most 9 | `varint::encoded_len` | none | `Varint.encode_length` | `v < 2^63` | Lean replay (bytes written) |
| every decoded value is below `2^63` and at most 9 bytes were used | `varint::decode` | none | `Varint.decode_bounds` | bytes are below 256 | Lean replay |
| `encode` fails exactly on overflow or a short buffer, and writes the canonical encoding otherwise | `varint::encode` | none | `Varint.encodeInto_ok_iff`, `Varint.encodeInto_decode` | none | Lean replay with random buffer sizes |
| `partition_point` returns the first index where the predicate fails | `slice::partition_point` as used by `plan` and `find` | `RangeOps.PP` (the specification of the result) | `PP.partitionPoint_eq` (the binary search loop of `core::slice::binary_search_by` in the pinned toolchain, step for step) | the slice is partitioned, which `Ranges.part_end_lt`, `part_start_le`, `part_end_le` prove for canonical sets | indirect, through the insert traces |
| insert keeps the set canonical: each start is below its end, neighbours are strictly separated, at most `N` intervals | `VerifiedRanges::insert`, `VerifiedRangesVec::insert` | `VerifiedRanges.tla`: invariant `Inv`; offsets 0..7 with `N = 3`, offsets 0..7 with `N = 1` | `Ranges.insertVec_sound`, `Ranges.insertState_inv`, `Ranges.reach_inv` | none | `TraceVerifiedRanges.tla` and Lean replay of every recorded state |
| on success, coverage after insert is the old coverage plus the range | `VerifiedRanges::insert`, `VerifiedRangesVec::insert` | `VerifiedRanges.tla`: `InsertCovers`, `InsertExact`; same bounds | `Ranges.insertVec_covers`, `Ranges.insertFixed_covers` | none | as above |
| a covered offset stays covered, also on a capacity failure | `VerifiedRanges::insert` | `VerifiedRanges.tla`: `MonotoneCoverage`; same bounds | `Ranges.insertState_mono`, `Ranges.reach_mono` | none | as above |
| insert fails iff the merged set needs more than `N` intervals, and then changes nothing | `VerifiedRanges::insert`, `CapacityError` | `VerifiedRanges.tla`: `FailIff` (counted independently as maximal runs of covered offsets), `FailureUnchanged`; same bounds | `Ranges.insertFixed_none_iff`, `Ranges.insertState_of_none` | none | the traces include capacity failures with `N` from 1 to 6 |
| `contains`, `contains_range`, `covered_len` agree with the coverage semantics | `VerifiedRanges::contains`, `contains_range`, `covered_len` (and the `Vec` set) | checked on the trace only: `TraceVerifiedRanges.tla` compares the recorded answers with `Covers`, `CoversRange`, `CoveredLen` | `Ranges.contains_iff`, `Ranges.containsRange_iff`, `Ranges.coveredLen_eq` | offsets are `u64`, so `covered_len` never saturates (proved) | TLC and Lean replay, with offsets at the top of the `u64` range in the Lean replay |
| `left_groups` is the largest power of two strictly below the node size | `left_groups` (crate private) | `RangeVerifier.tla`: `Left`, the specification | `Layout.leftGroups_pos`, `leftGroups_lt`, `le_two_leftGroups`, `leftGroups_max` | none | none: the function is private |
| the right child's pre-order index is `idx + left_groups`, the left child's `idx + 1`, a tree of `n` groups has `n - 1` parents, and `preorder_index` returns a parent's position | `preorder_index`, `RangeEncoder` (crate private) | none | `Layout.right_child_index`, `Layout.left_child_index`, `Layout.pre_length`, `Layout.preorderIndex_correct` | the node is a node of the tree (`Layout.Sub`) | none: the function is private |
| `group_range` is the minimal covering group interval and stays within the groups | `Layout::group_range`, `Layout::groups` | none | `Layout.groupRange_spec`, `Layout.lt_groups_iff` | none | Lean replay of random lengths, group sizes and byte ranges |
| every group the verifier releases is the genuine group at its offset, whatever the adversary feeds | `RangeVerifier::feed` | `RangeVerifier.tla`: `ReleasedGenuine`, `StackGenuine`; up to 7 groups, every range, a genuine or forged item at each step | `Tree.released_genuine` | collision resistance of the hash (`Tree.CollisionFree`: injective on parent pairs and on (offset, data)) and the genuine root | none yet |
| releases are strictly ascending, and at completion are exactly the groups that intersect the requested bytes | `RangeVerifier::feed`, `RangeVerifier::is_complete`, `Layout::group_range` | `RangeVerifier.tla`: `Ascending`, `InRange`, `Bookkeeping`, `CompleteReleasedAll`; same bounds | `Tree.released_ascending`, `Tree.complete_releases_range`, `Tree.verifier_correct` | none for the ordering; collision resistance and the genuine root for the genuine bytes | none yet |
| a rejected item releases nothing, a failed verifier stays failed, a group is released only after its hash matched | `RangeVerifier::feed` | `RangeVerifier.tla`: `FailureSticky`, `RejectReleasesNothing`; same bounds | `Tree.feed_failed`, `Tree.feed_reject_releases_nothing`, `Tree.feed_release_verified` | none | none yet |

What is not proven or not checked:
- The verifier is modelled at the level of completed stream items. The buffer, partial feeds and any zero-copy path
  are out of the model, and the verifier has no trace validation yet, so the Rust `RangeVerifier` is tied to its
  model by reading, not by a recorded trace.
- BLAKE3 itself is abstract. The genuine tree is defined from abstract leaf and parent hashes, and that these are
  what the code computes (and that BLAKE3 is collision resistant) is an assumption, not a result.
- That an honest stream is always accepted (no false rejection) is not proven; only that nothing forged is released.
- `RangeEncoder`, `OutboardBuilder`, `Layout::depth`, `outboard_size` and `group_size` are not modelled, and nor is the
  64-entry stack bound.
- `left_groups` and `preorder_index` are crate private, so no test can record them: their Lean models are tied to
  the code by reading only.
- Offsets and lengths are modelled as natural numbers. For `u64` values the comparisons agree; the one place where
  they could differ (the saturating sum in `covered_len`) is proved not to saturate.
- The TLC models are bounded as listed; the Lean theorems are not.
