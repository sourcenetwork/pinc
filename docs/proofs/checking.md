# Proofs: how it is checked

By `scripts/proofs.sh` (the `== proofs` step of `scripts/gate.sh`):
- **Lean** (`proofs/lean`, a Lake package on core Lean and Std, no Mathlib): `lake build` checks every proof. A script
  rejects `sorry`, `admit`, `axiom` and `native_decide` in the sources, and the build fails if any declaration of the
  package depends on an axiom beyond `propext`, `Classical.choice` and `Quot.sound` (`#audit_package`, plus a
  printed `#audit_axioms` line for every main theorem).
- **TLC** model checks every TLA+ config in `proofs/tla` over the bounds of its profile (below). TLC integers are 32 bits wide,
  so the specifications of the machine-integer code (`Varint`, `Layout`, `Encoder`, `BuilderBytes`, `VerifierBytes`)
  write every `u64` and `usize` as a word of five 16-bit limbs (`U64.tla`). Each operation of the Rust code has an
  operator with the semantics of the code: a plain `+`, `-`, `*`, `<<`, `>>`, `/` or `%` that overflows, underflows,
  shifts by 64 or more or divides by zero, a `try_from` that does not fit where the code unwraps it, an `ilog2` of
  zero, a slot that is not found and a push onto a full stack all stop TLC with an error, so a model check that
  finishes has shown that none of them is reachable in the checked domain. `checked_*`, `saturating_*` and
  `try_from` return their option or saturate. The cases of these specifications are the states of a machine whose
  root has one successor per seed, so all workers generate and check cases at once; the byte-level specifications
  (`BuilderBytes`, `VerifierBytes`) are machines that feed pieces, so TLC explores every split.
- **The link between the two languages.** Each specification names, in its header, the Lean theorems it
  corresponds to, and the [property table](properties.md) gives the specification and the theorem side by side. The boundary sets are the
  same on both sides: for every `j` in `0..64` the values `2^j - 1`, `2^j` and `2^j + 1`, the byte classes, the
  addends of `encoded_len`, the group buffer sizes, the shapes of the paths in a tree of `2^54` groups and the
  completed-group counts of the builder. `proofs/lean/Pinc/Link.lean` evaluates the Lean models of the code on
  those sets and the kernel checks the result (`decide +kernel`; the values below 16500 and the strings of 3 and 4
  bytes of `Varint.tla` are cut to 130 and 2 bytes, and the path and slot theorems take 16 values of `j` out of 55,
  `bigJ` in `Link.lean`, to keep the kernel's time within the budget), and the Rust traces of `tests/trace_tla.rs` run
  the real code on them for TLC. The Lean statements are general (`Varint.decode_encode` holds for every `v`); the TLA+
  checks are bounded; the sets are the place where the two meet, so a value accepted by one and refused by the other
  shows up in the build.
- **Trace validation.** The Rust tests `tests/trace_ranges.rs`, `tests/trace_verifier.rs` and `tests/trace_builder.rs`
  run seeded random sequences through the public API, compare every answer with a naive reference or with the genuine
  value, and, when `PINC_TRACE_DIR` is set, write them as ndjson. `trace_ranges` covers `VerifiedRanges<N>`,
  `VerifiedRangesVec`, `varint` and `Layout`: TLC checks that the recorded insert sequence is a behaviour of
  `VerifiedRanges.tla` (`TraceVerifiedRanges.tla`: every step is an `Insert` step with the run's capacity, and the
  recorded `covered_len`, `contains` and `contains_range` equal the specification's).
  `trace_verifier` runs the real `RangeVerifier` on genuine `encode_range` streams and on streams with a flipped bit,
  cut short or followed by extra bytes, fed in windows of every size (the whole stream, single bytes, item-sized,
  random), and records one event per `feed` call: the input length and its offset in the stream, what the verifier
  reported (consumed bytes, released offset, error, `next_len`, `is_complete`) and, when the call completed a stream
  item, the item, the offset of its first byte and the hash call the verifier made for it, with the chaining value the
  code computed for it (the oracle; chaining values and group bytes are ids). `TraceRangeVerifier.tla` (reusing
  `StepWith`, `QueryKey` and `Left` of `RangeVerifier.tla`) and `lake exe replay` (running the proved `Tree.feed` and the
  byte-level `VerifyBytes.feedCode`) check that the oracle is a function (one value per hash call) and that every
  decision is the model's under that oracle: the hash call is the one the model makes for the item, the item is accepted
  or rejected, the group released and the parents pushed as the model does, the error kind is right, a failed verifier
  repeats its error, and the stream steps of the public `RangeEncoder` name the model's nodes (a parent's outboard
  offset is 64 times its pre-order position). The same files carry the buffer: the replay runs the byte-level model on
  the real offsets (the input of a call is the bytes `pos .. pos + ilen` of the stream, the unconsumed tail is fed
  again, the model's buffer holds the offsets already taken), so the bytes consumed, `next_len`, the fast-path
  predicate (nothing buffered and the whole item in the input), the offset of the released group and the exact bytes of
  the item it holds equal the model's, and a released group borrows the input exactly on the fast path and the
  verifier's buffer otherwise (`ptr`, the one fact the value model cannot state); TLC checks that the offsets advance
  by the bytes consumed and that a completed item starts at `pos - filled`.
  `trace_verifier` also records the complete step list of the public `RangeEncoder` for layouts from one group to
  `2^54` groups (a value of `u64::MAX` bytes: the encoder needs only the layout), around every power of two and with
  ranges at the start, the end and in the middle, and `encode_range` into output buffers of every size around the
  stream's length. `lake exe replay` checks each step list against `Encode.encRun`, so the outboard offset of every
  parent step and the split of every node visited are the proved functions' (`left_groups`, the pre-order position),
  and each `encode_range` result against `Machine.encodeRangeM`.
  `trace_builder` runs the real `OutboardBuilder` on random values, group sizes (1 to 8 KiB, and 1 KiB groups up to
  150 groups) and splits of the value into pieces (whole, a few bytes, group-sized, one byte off a group, random), with
  the error cases between the real calls (a buffer of the wrong size, a piece past the declared length, `finish` before
  the last byte, a piece of 0 bytes, data after the end). A run starts with the genuine tree of the value, computed
  from the definition of the BLAKE3 tree with the BLAKE3 library, never by the code under test; each call is an event
  with the slots of the buffer that changed, found by comparing the buffer before and after. `TraceBuilder.tla` and the
  replay (running `BuilderBytes.updateCode` and `finishCode` under the recorded tables) check that the result of every
  call is the model's, that the slots written are exactly the model's, each at the pre-order position of its node
  (`Layout.preorderIndex` in Lean, `Pos` counted from the definition in TLA+) with the pair of genuine chaining values,
  and that the root `finish` returns is the genuine root; the root of the empty value must equal the recorded hash of
  the empty input, which the test takes from `blake3::hash(b"")` and the verifier's `RootMismatch` check uses.
  `trace_tla` runs the real `varint`, `Layout`, `RangeEncoder`, `encoded_len` and `encode_range` on the boundary
  sets the TLA+ models enumerate and on seeded random inputs, and writes every `u64` as four 16-bit limbs (TLC cannot
  read a number above 2^31 from JSON, it wraps it silently), to `tla/` under `PINC_TRACE_DIR`: `TraceVarint.tla`,
  `TraceLayout.tla` and `TraceEncoder.tla` check each recorded call against `Varint.tla`, `Layout.tla` and
  `Encoder.tla` (the same operators the model check runs). The builder trace is checked by `TraceBuilder.tla`, which
  runs the recorded calls through `BuilderBytes.tla` (`UpdateCall`, `FinishCall`) with the recorded hash tables as the
  hash, and `TraceRangeVerifier.tla` takes the buffer decisions (`Plan`, `NextLen`) from `VerifierBytes.tla`. The
  events of the pure functions are independent, so TLC checks them as separate states on all workers.
  `lake exe replay` also replays the ranges, varint, layout and size traces (`groups`, `depth`, `outboard_size`,
  `group_size` over lengths up to `u64::MAX` and every group log) against the Lean functions and fails on any
  difference.
- **What a trace check proves.** A trace check passes (the recorded trace is accepted) only when TLC finds a behaviour
  of its spec that consumes every line of a trace that has at least one. TLC ending with no error is not enough by
  itself: a replay that cannot match a line also ends with no error when a step that consumes no line stays enabled
  (the hidden steps of `TraceStreams.tla`), when the config does not check deadlock, or when the file is empty. Every
  trace spec extends `TraceEnd.tla` and its config names `INVARIANT ReplayAtEnd` (a state where every line is consumed
  records that in a TLC register) and `POSTCONDITION ReplayEnded` (after the search: the trace has a line and the end
  was recorded). A spec that replays independent runs (`TraceBuilder`, `TraceRangeVerifier`, `TraceValuesVerify`)
  asks for the end of every run; a spec that checks every line as its own state asks for the state of the last line.
  The registers are per worker, so `scripts/proofs.sh` runs a trace check on one worker, and it stops before the trace
  step when a `proofs/tla/Trace*.cfg` lacks the two lines. A missing trace file fails the check.
- **Model-based tests**, the other direction: a trace check runs seeded random calls, which reach the rare
  interleavings a model checker enumerates only by chance, so here the model chooses the calls. So far for four
  components, the table of held first-flight fragments (the pattern for the others), the half-open cap, the
  received-packet ranges and the handshake fragment reassembly. `MbtOrphan.tla` runs the
  operators of `OrphanOps.tla` at the size of the real table (4 entries) with one action per call of the code, whose
  parameters are the call's arguments and its result (`CallHold(t, key, len, ok)`, `CallTake(t, key, out)`,
  `CallExpire(t)`; TLC splits the bounded `\E` of the next-state relation into one action per value, and only the
  result the operators compute has a successor). TLC writes the whole state graph of a config
  (`-dump dot,actionlabels,constrained`, with the 2026 jar, whose edge labels carry the action's parameters): one
  node per state (the entries and the four counters), one edge per call, and the states past the config's constraint
  as leaves, reached but not left. `scripts/mbt.py` checks that the graph holds every state and every successor TLC
  counted, computes paths from the empty table that take every edge at least once (breadth first to a state with an
  edge not taken yet, then along edges not taken yet until there is none) and writes them as ndjson, each call with
  its arguments, the model's result and the model's state after it. `tests/mbt_orphan.rs` drives a fresh
  `OrphanProbe` along every path and stops at the first call whose result, or whose table after it (every entry with
  its bytes, the order of arrival and the counters), is not the model's; it reads the cases from `PINC_MBT_DIR` and
  checks nothing when that is unset, so the plain test run is unchanged. The model's numbers are scaled: model time
  `t` is `origin + t * (ORPHAN_LIFE / LIFE)` with the origin 0, an odd time or the one that puts the last time on
  `u64::MAX`, a length of at most `MAX` stands for one of at most 1500 bytes (1500, 1499, 600 or 8 by the datagram's
  tag) and `MAX + 1` for one past it, and the second message differs from the first in the id, the message length or
  the port, by case. `MbtOrphan.cfg` (lifetime 1, calls at times 0 to 2, datagrams arriving at 0 and 2, six held in
  all, so that a full table evicts a second time from an entry that is not the first) has 5434 states inside the
  bound, 10132 leaves and 92378 edges, walked as 33864 cases of 297287 calls; `MbtOrphan_edge.cfg` (arrivals at 0, 1
  and 2, five held: a hold at the last moment a held datagram is fresh) has 4741 states, 17918 leaves and 99561
  edges, 37359 cases of 271446 calls. Every call matched. The cases bite: with the eviction in `OrphanOps.tla` changed
  to take the first entry instead of the oldest arrival, `MbtOrphan.cfg` fails at the sixth hold of a case
  (`MbtOrphan_edge.cfg`, which holds five, passes); with `>=` for `>` in `Stale`, or a refused hold that expires, both
  fail. The second component is the received-packet tracker's range set and the ACK ranges it reports:
  `MbtRanges.tla` takes the operators of `RxOps.tla` at a small `RANGES` (the type is const generic, so the test builds
  a `ReceivedPackets<2>` and a `ReceivedPackets<3>`) with `CallRecv(pn, new)`, `CallContains(pn, seen)`,
  `CallAckRanges(now, rgs)`, `CallAckSent(apn, now)` and `CallPeerAck(now, rgs)`, and `tests/mbt_ranges.rs` compares
  the result and the whole tracker (`trace_view`, `largest`, `range_count`) after every call. The packets are not
  ack-eliciting, so the acknowledgement policy (the component "acknowledgement thinning") stays at its start; the
  tables of our acknowledgements and of confirmations are bounded by the config (the code's 48 and 32 are too large to
  fill). `MbtRanges.cfg` (2 ranges, packet numbers 0 to 4, clocks 0 and 2 s, up to 2 acknowledgements recorded and 1
  confirmation) has 8176 states, 4156 of them leaves, 92460 edges, walked as 17178 cases of 223729 calls;
  `MbtRanges_wide.cfg` (3 ranges, packet numbers 0 to 7, no confirmation) 5382 states, 45762 edges, 7733 cases of
  84763 calls (about 25 s together). Every call matched; the graphs hold the merge of adjacent ranges, a full table
  whose oldest range is forgotten (the floor rises past it), a packet below a full table refused and raising the
  floor, and the report cut to the newest range after a confirmation. They bite: the floor rising to the start of the
  forgotten range, `<=` for `<` in the test for the second-newest range against the confirmed floor, and `contains`
  without the `+ 1` of the full-table rule each fail. Not reached: the limit of 32 ranges in a report
  (`MAX_ACK_RANGES` is a constant of the module, not a parameter, and a graph with 33 ranges is every set of 33
  non-adjacent numbers); it stays with `Rx.tla`'s `ReportShape` at its scaled limit, `TraceRx.tla` at 128 ranges and
  the code's tests. The handshake fragment reassembly is the next: `MbtReasm.tla` takes `ReasmOps.tla` at the code's sizes (8
  runs, the largest message of 6529 bytes) with one action, `CallAdd(total, off, len, out)`, over a fixed set of calls
  (a message of 17 bytes in fragments that fill the table and overflow it, overlap, leave gaps, run past the end, are
  empty or lie beyond it; messages of 3 and of the largest length that start the count over; the lengths 0 and one
  past the largest, refused), and `tests/mbt_reasm.rs` compares the returned length, the runs and the message length
  after every call, and checks the buffer against the bytes it sent. `MbtReasm.cfg` has 3468 states, 93636 edges,
  35134 cases of 267353 calls (about 2 s); every call matched. They bite: a table that is full at 7 runs, a
  completed message that keeps its length, and `>=` for `>` in the largest message each fail (merging only runs that
  overlap, not ones that touch, is caught earlier, by `Complete`'s shape check in TLC). TLC's other exports were not
  enough: `-dumpTrace` writes one behaviour per violated property and `-simulate`
  draws random behaviours, so neither covers the graph.
  The second component is the half-open cap: `MbtHalfOpen.tla` takes the admission and expiry operators of
  `HalfOpenOps.tla` at the code's real cap, 256 (a plain constant, not a parameter of a type, so no probe with a
  small cap), with `CallFlood(t, kind, len, dec)` (a forged first flight from a new source, `dec` the endpoint's record of its decision: made, refused, or dropped by the screening, so a short Initial's floor and a Hello's are told apart) and `CallTimer(t)`, and
  `tests/mbt_halfopen.rs` drives a real 300-slot endpoint, comparing the endpoint's own admission record, the count
  and the sessions held by creation time after every call. The state is the number of sessions made at each time (the
  slot is the free list's choice, which nothing the cap or the expiry reads depends on), so the graphs stay small:
  `MbtHalfOpen.cfg` (flights at 0 and 1, timers at 0 to 2, up to 3 made at time 1) has 1022 states inside the bound,
  35770 edges, 1270 cases of 198960 calls; `MbtHalfOpen_back.cfg` (flights at 0 to 2, timers at 0 to 3, one made per
  later time: a timer before a creation, a clock that stepped back) 1024 states, 53248 edges, 3055 cases of 445174
  calls (about 40 s together). Every call matched. They bite: a cap of 255 in the model, an expiry one step late,
  swapped floors and a screening drop recorded as a reject each fail. The calls that need a peer that answers (establishment, a resumption at the cap, a close,
  a stalled queue) stay with the trace check and `HalfOpen.tla`.
- **Trace soak.** The gate records the trace tests under their fixed seeds. `scripts/trace-soak.sh` (`just trace-soak`)
  sets `PINC_TRACE_SEED`, which moves the seed of every trace test that draws from `SplitMix64::traced`, records the
  traces into a temporary directory and replays each file in the Lean model, over and over, keeping the ndjson and the
  seed of the first mismatch (with `-k n` it also runs the TLC trace checks every `n` iterations); a trace test's
  assertions that its fixed seeds reach every branch are skipped under a moved seed. `scripts/trace-cov.sh` (`just
  trace-cov`) measures what the trace tests alone run of the library crates, and lists the uncovered lines (with
  `BRANCH=1`, branches) of the items named in the tables of [Properties](properties.md).

Profiles: `just proofs` runs the quick profile, the default: a model with a file under `proofs/tla/quick/` is checked
over the smaller bounds of that file (the same specification and properties; [the quick profile](quick.md) lists every
such file and what its bounds no longer reach), one worker per check and one check per processor. `just proofs-deep`
(`scripts/proofs.sh deep`) checks every model over the bounds [Properties](properties.md) states, with every processor
for each of three checks at a time; it takes hours of processor time and is not part of the gate.

Tools: Lean 4 and Lake, TLC on `PATH` as `tlc`, Java, and for the trace check and the model-based tests a TLC of the
same era as the [CommunityModules](https://github.com/tlaplus/CommunityModules) jar (the gate prints the download
command when a jar is missing), and Python 3 for `scripts/mbt.py`.

