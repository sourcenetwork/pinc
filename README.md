<p align="center">
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="art/vinc-logo-white.svg">
    <img height="120" alt="VINC" src="art/vinc-logo.svg">
  </picture>
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
| `vinc-crypto` | primitives | pure-Rust RustCrypto primitives behind one static `Provider` trait: ChaCha20-Poly1305 and AES-128-GCM, header protection, SHA-256, X25519, ML-KEM-768; Ed25519, P-256 and ML-DSA-65 identities with node ids; a BLAKE3 KDF, an injective transcript hash and a seeded DRBG; no allocation, no randomness inside | yes | in progress |
| `vinc-keystore` | key custody | where long-term keys live: a `KeyStore` trait (sign, ML-KEM decapsulate, random, seal and unseal at rest) with an in-memory software store; the optional `hwenc` feature adds a pure-Rust TPM 2.0 store (ECDSA P-256 identities and the sealing key, through `tpm2-protocol` over `/dev/tpmrm0`); no C library; std only | no | in progress |
| `vinc-security` | security | SANS-IO hybrid post-quantum handshake (X25519 plus ML-KEM-768, mutual authentication with Ed25519, P-256, ML-DSA-65 or hybrid identities), prekey short Initial, single-use ticket resumption with 0-RTT keys, host key requests for signing and decapsulation, key schedule, packet and header protection with key update, replay window, address-validation tokens, anti-amplification budget; no allocation, no randomness or clock inside | yes | in progress |
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
- **Trace validation.** The Rust tests `tests/trace_ranges.rs` and `tests/trace_verifier.rs` run seeded random
  sequences through the public API, compare every answer with a naive reference or with the genuine value, and, when
  `VINC_TRACE_DIR` is set, write them as ndjson. `trace_ranges` covers `VerifiedRanges<N>`, `VerifiedRangesVec`,
  `varint` and `Layout`: TLC checks that the recorded insert sequence is a behaviour of `VerifiedRanges.tla`
  (`TraceVerifiedRanges.tla`: every step is an `Insert` step with the run's capacity, and the recorded `covered_len`,
  `contains` and `contains_range` equal the specification's).
  `trace_verifier` runs the real `RangeVerifier` on genuine `encode_range` streams and on streams with a flipped bit,
  cut short or followed by extra bytes, fed in windows of every size (the whole stream, single bytes, item-sized,
  random), and records one event per `feed` call: the input length, what the verifier reported (consumed bytes,
  released offset, error, `next_len`, `is_complete`) and, when the call completed a stream item, the item and the hash
  call the verifier made for it, with the chaining value the code computed for it (the oracle; chaining values and group
  bytes are ids). `TraceRangeVerifier.tla` (reusing `StepWith`, `QueryKey` and `Left` of `RangeVerifier.tla`) and
  `lake exe replay` (running the proved `Tree.feed`) check that the oracle is a function (one value per hash call) and
  that every decision is the model's under that oracle: the hash call is the one the model makes for the item, the
  item is accepted or rejected, the group released and the parents pushed as the model does, the error kind is right, a
  failed verifier repeats its error, and the stream steps of the public `RangeEncoder` name the model's nodes (a
  parent's outboard offset is 64 times its pre-order position). The same files carry the buffer: the bytes consumed,
  `next_len` and the fast-path predicate (nothing buffered and the whole item in the input) equal the model's, and a
  released group borrows the input exactly on the fast path and the verifier's buffer otherwise (`ptr`), so the two
  paths are told apart in the trace and both take the same step on the completed item. `lake exe replay` also replays
  the ranges, varint, layout and size traces (`groups`, `depth`, `outboard_size`, `group_size` over lengths up to
  `u64::MAX` and every group log) against the Lean functions and fails on any difference.

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
| `left_groups` is the largest power of two strictly below the node size | `left_groups` (crate private) | `RangeVerifier.tla`: `Left`, the specification | `Layout.leftGroups_pos`, `leftGroups_lt`, `le_two_leftGroups`, `leftGroups_max` | none | indirect: the function is private, but the node walk of every verifier trace uses it, and the recorded encoder steps and `next_len` values must match |
| the right child's pre-order index is `idx + left_groups`, the left child's `idx + 1`, a tree of `n` groups has `n - 1` parents, and `preorder_index` returns a parent's position | `preorder_index`, `RangeEncoder` (crate private) | `TraceRangeVerifier.tla`: `Pos`, the position counted from the definition | `Layout.right_child_index`, `Layout.left_child_index`, `Layout.pre_length`, `Layout.preorderIndex_correct`, `Builder.pre_nodup` | the node is a node of the tree (`Layout.Sub`) | the outboard offset of every recorded encoder step equals 64 times the node's position: TLC (`Pos`) and Lean replay (`preorderIndex`) |
| `group_range` is the minimal covering group interval and stays within the groups | `Layout::group_range`, `Layout::groups` | `TraceRangeVerifier.tla` recomputes the range of each run | `Layout.groupRange_spec`, `Layout.lt_groups_iff` | none | Lean replay of random lengths, group sizes and byte ranges, and the runs of the verifier traces |
| `depth` is the height of the group tree, `outboard_size` is 64 bytes per parent, `group_size` is the bytes of the value in that group; none of them overflows `u64`, and a value of at most `2^64 - 1` bytes has at most `2^54` groups | `Layout::depth`, `Layout::outboard_size`, `Layout::group_size` | none | `Layout.depth_eq` (with `Layout.ht_eq`: the height of the recursive tree is `ceil(log2 groups)`), `Layout.outboardSize_eq`, `Layout.outboardSize_lt`, `Layout.groupSize_spec`, `Layout.groupSize_eq` (the saturating multiply is the plain one), `Layout.groups_le` | `leading_zeros` is specified by the top set bit (`Layout.IsLz`) | Lean replay of 1500 random layouts, with lengths up to `u64::MAX` and every group log |
| every group the verifier releases is the genuine group at its offset, whatever the adversary feeds | `RangeVerifier::feed` | `RangeVerifier.tla`: `ReleasedGenuine`, `StackGenuine`; up to 7 groups, every range, a genuine or forged item at each step | `Tree.released_genuine` | collision resistance of the hash (`Tree.CollisionFree`: injective on parent pairs and on (offset, data)) and the genuine root | the decision of each recorded item equals the model's under the recorded hash values (`TraceRangeVerifier.tla`, Lean replay; `Tree.feed_congr`: the step depends on the hash only through the one call it makes); collision resistance itself is not testable |
| releases are strictly ascending, and at completion are exactly the groups that intersect the requested bytes | `RangeVerifier::feed`, `RangeVerifier::is_complete`, `Layout::group_range` | `RangeVerifier.tla`: `Ascending`, `InRange`, `Bookkeeping`, `CompleteReleasedAll`; same bounds | `Tree.released_ascending`, `Tree.complete_releases_range`, `Tree.verifier_correct` | none for the ordering; collision resistance and the genuine root for the genuine bytes | `Ascending`, `InRange` and `Bookkeeping` are invariants of the trace model, checked on every recorded state |
| a rejected item releases nothing, a failed verifier stays failed, a group is released only after its hash matched | `RangeVerifier::feed` | `RangeVerifier.tla`: `FailureSticky`, `RejectReleasesNothing`; same bounds | `Tree.feed_failed`, `Tree.feed_reject_releases_nothing`, `Tree.feed_release_verified` | none | the tampered runs: the rejected item, the repeated error of every later call, and `TooMuchData` after completion |
| completeness: the stream `encode_range` produces for a genuine value and outboard is accepted, with no false rejection; the verifier completes and releases exactly the groups intersecting the range, with their genuine bytes; the encoder reads inside the value and the outboard, and each step has the size the verifier expects | `RangeEncoder`, `encode_range`, `RangeVerifier::feed` | none (the verifier model is shared with the row above) | `Encode.complete_accepts` (with `Encode.lockstep`, `Encode.encStep_size`) | none: it holds for any hash | the genuine runs: every step names the model's node, and the verifier accepts every item |
| the stack never overflows: the verifier stack and the encoder stack hold at most 55 nodes for any value of at most `2^64 - 1` bytes (any group log), so the 64-entry `STACK_CAP` is never reached and `TreeError::StackOverflow` is unreachable; the builder stack holds at most 54 entries after each group, plus one before a merge | `Stack<_, 64>` in `RangeVerifier`, `RangeEncoder`, `OutboardBuilder` | the trace model checks `Len(stack) <= 55` on every recorded state | `Bounds.verifier_stack_le`, `Bounds.verifier_stack_le_len`, `Bounds.encoder_stack_le`, `Builder.mainPhase_stack_le` | none | the stack bound on every recorded verifier state |
| the outboard builder writes the parents in pre-order: every parent of the tree is written once (`n - 1` writes), each at the slot `preorder_index` gives, with the pair of the genuine chaining values of its children, and the root it returns is the genuine root; one group has no parent and the group hash is the root | `OutboardBuilder::update`, `finish` (and `build_outboard`) | none | `Builder.builder_correct`, `Builder.builder_outboard` (against any genuine outboard), `Builder.builder_correct_one` | the abstract hash is what the BLAKE3 calls compute (as in `Tree`); the model starts when a group completes | none: only the finished outboard is observable, and the integration tests check it against the verifier and `blake3::hash` |

What is not proven or not checked:
- BLAKE3 itself is abstract. The genuine tree is defined from abstract leaf and parent hashes, and that these are
  what the code computes (and that BLAKE3 is collision resistant) is an assumption, not a result. The trace check
  does not weaken this: it takes the chaining values the code computed as an oracle, so it validates the verifier's
  decisions, not the hashes.
- The Lean model of the verifier works on completed stream items. The buffer, partial feeds and the zero-copy path are
  validated by trace (the buffer arithmetic and the fast-path test in TLC and the Lean replay, over the recorded
  runs), not proved for all inputs, and the model holds no bytes: group bytes and chaining values are ids chosen by
  the test, so that the buffer reassembles pieces into the right item is checked through the hashes and the released
  bytes (`rd`), not proved. The two paths take the same step on a completed item in the model, which is why the
  proofs do not mention the path.
- Completeness is proved at the level of the encoder and verifier models. `encode_range`'s conversions between `u64`
  and `usize` (on a target where `usize` is narrower than 64 bits) and the caller's output buffer size are not
  modelled; the stream sizes are, but `OutputTooSmall` follows from the caller's buffer being `encoded_len`, the
  sum of the same steps.
- `OutboardBuilder` is proved on the model that starts when a group completes. The per-piece bookkeeping of `update`
  (`in_group`, `consumed`, splitting input at group boundaries, `TooMuchData`, `Incomplete`, `OutboardSize`), the
  BLAKE3 hasher state (`update` over pieces, `set_input_offset`, `finalize_non_root`) and the empty value (the constant
  hash of the empty input, which the verifier also checks) are not modelled, and the builder has no trace validation.
- `left_groups` and `preorder_index` are crate private, so no test calls them: they are checked indirectly, through
  the node walk of the verifier model and the offsets of the public encoder steps in the traces.
- `Layout::depth` uses `u64::leading_zeros`, specified here by the position of the top set bit; the standard
  library's implementation is validated by the size traces, not proved.
- Offsets and lengths are modelled as natural numbers. For `u64` values the comparisons agree; the places where they
  could differ are proved not to: the saturating sum in `covered_len`, the saturating multiply in `group_size`
  (`Layout.groupSize_eq`), and the products in `outboard_size` and the encoder offsets (`Layout.outboardSize_lt`,
  `Encode.InBounds`).
- The TLC models are bounded as listed; the Lean theorems are not. The trace checks cover the recorded runs only.
