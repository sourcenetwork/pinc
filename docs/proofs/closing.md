# Proofs: being closed

These items are still open; they are listed so nothing is hidden:
- `pinc-crypto` and `pinc-keystore`: the labels of `pinc-broadcast` are private constants, so they are not in the label registry or its trace; the zeroization statement covers the named buffers of the crate, not the copies a dependency makes of a scalar passed by value; the TPM store is traced against a software TPM only, and a refused flush after a failed `ReadPublic` in `generate` leaks the handle without an error; the TPM refuses an object auth value longer than the digest of its name algorithm (32 bytes), which the client reports as the TPM's code. The TPM client's resend of a command answered `TPM_RC_RETRY`, `TPM_RC_YIELDED` or `TPM_RC_TESTING` is checked
  at the trace level (the same bytes sent again, at most 8 sends; the store's programs are checked on the commands
  that took effect); the typed error after the last resend is covered by unit tests, not by the TPM model.
- The TLC models are bounded as listed (the Lean theorems are not); the trace checks cover the recorded runs only;
  the model-based tests cover the bounded state graphs of their configs only, in the eleven tests of `scripts/proofs/mbt.sh`.
- `pinc-core`: the model-based test of the endpoint (`MbtEndpoint`) covers the endpoint's use of its tables in its
  three configs, the one with a stalled event queue among them. The text below was written before that model and is
  being brought in line with it ([#748](https://github.com/sourcenetwork/pinc/issues/748)).
  The half-open cap and the life of an unauthenticated session are proved (see "half-open cap" above: at most 256
  counted sessions, a refused first flight changes no slot, no arrival frees a session, no first flight makes a
  fifth holder of an id, a session leaves the count only when it is established or freed, and is gone at the first timer call at or
  after its 30 s); the ticket check that exempts a resumption is an
  input there, and a timer of one session that closes its sub-sessions is not in that model. The table of first-flight
  fragments held until their start arrives is proved on its own (see "held first-flight fragments" above: at most 4
  datagrams of at most 1500 bytes per endpoint, each given out at most once, at most 1 s old, for the same message
  from the same address); that the endpoint gives what the table hands out only to the session the start of that
  message creates is tested, not proven. The connection-id table is proved on its own (see "the endpoint's
  connection-id table" above: at most `CAP` entries, every key found whatever the collisions, a removal takes one
  entry, duplicates only by `insert_dup`, eviction of exactly the oldest, refusal on a full table, `matches`
  returning the newest `M` holders); that the endpoint's use of it is right (one session per id except through
  `insert_dup`, one entry per copy of an id a session lists, `cid_delta` taking the copies it gained and lost as
  multisets, while a session never lists an id twice, `Cid.tla` `IdsOnce`; the four newest holders of an id tried,
  `remove_pair` removing exactly its own entry) is tested, not proven. The deadline heap is proved (see "deadline heap" above: the position
  index and the heap are inverse, the order holds with ties to the lower id, the root is the earliest, a call
  changes exactly the entry it names, at most `N` items, pops come out sorted); that the endpoint sets a session's
  deadline in it from the right events is not. The saved state is proved too (see "saved state" above): the bytes of
  `export_state` read back as the state written, one reading per byte string, a refused input changes none of the
  three tables, and the tables stay within their bounds; the facade's wrapper of it (`crates/pinc/src/engine/state.rs`:
  the address book and the version and length framing around the core's bytes) is not modelled and has no trace, only
  its unit tests and `tests/pinc_state.rs`, because its `parse` and `restore_state` are private to the crate and the
  crate has no `trace` view. The endpoint's event queue and the held ring of a session are proved on
  their own (see "event queue" and "held ring of a session" above: events leave in the order they entered, the
  rings never grow, every drop and every loss is counted, an event the application cannot recover is evicted from
  the queue only if it holds nothing recoverable, a held ring never gives one up, and a step within the headroom
  from a queue that is not stalled loses nothing); that every step of the endpoint pushes at most the headroom of
  unrecoverable events, and checks the stall first, is an input there. The rings of extension frames (`ext_in.rs`) and of `REACH_OUT` bodies (`reach.rs`) are proved on their own (see
  "extension frames held for the application" and "`REACH_OUT` bodies held for the application" above: both never
  grow, a body over the limit is never stored, `ext_in.rs` drops its oldest frame and keeps arrival order, `reach.rs`
  keeps one body per session, the latest, and gives up the body put longest ago); that the endpoint routes the right
  frames to each ring is the extension registry's rule and is taken as given here; both rings return what they lose,
  and that the endpoint adds it, with the `REACH_OUT` bodies it refuses itself, to `NodeStats::reach_dropped` and
  `ext_dropped` is read off `events.rs` and tested (`tests/core_ring_drops.rs`), not modelled. The keepalive schedule (`keepalive.rs`) is proved (see "keepalive schedule"
  above); the relay path addresses (`relay_net.rs`) and the use of the plan by the
  timers (`timers.rs`) are not.
  The node's round trip table, average, peak and handshake floor (`rtt.rs`) are proved on their own (see "node round
  trips" above); the callers that feed it and the transport's use of what it returns (the connect limit, the first
  resend) are tested, not proven.
- `pinc-node`: the node's table of failed dials is proved on its own (see "the node's table of failed dials"
  above: at most 4096 entries, a wait that doubles to 16 s for a hub and 60 s for any other node, a full table that
  refuses a new peer and never evicts, the backoff window, the 5 s reset, the prune, the shed of a dial the full
  session table has no room for, traced through a real node's duty passes). Not done: the rest of `dial_peer` and
  the host duties as a whole (a trace of the guard beyond the window, the reset and a prune that lets go of an entry
  needs more of a view of a `Node`). Since then
  the delay-tolerant layer's own backoff table (`lfailed`), the bound on a deadline that its timer calls do not move
  (`timers.rs`), the silence bound of `bound.rs` and the queue of application events of `io.rs` each have a model and
  a trace check: see `NodeDtnBackoff`, `NodeTimerBound`, `NodeSilence` and `NodeEventQueue` under
  [Properties](properties.md). The checks of the node that fail or were never run are listed in
  [#748](https://github.com/sourcenetwork/pinc/issues/748). The
  known limitation of the model is the low-severity behaviour of a full table: a newly failing or shed peer has no
  entry and is redialed at every duty pass.
- `pinc` address text (`addr.rs`): `FacadeAddr.tla` checks the round trip of the ticket for every value built
  through the API (`with_relay` refuses an empty URL, one without `://` and one with a comma; `node_from_str` takes
  lowercase hex only); a node address made as a struct literal with relays `with_relay` refuses is outside it (the
  witness `FacadeAddr_raw`).
- `pinc-reconcile`: the refinement of the byte-level handlers to the abstract part system is proved for the split,
  the leaf rule, every part arm on an honest part and the frame, keep and round bounds, not end to end: that
  `answer` with its rollback, `turn`, the frames and the handlers carry exactly the honest parts of the abstract
  system through a whole session is not proved in Lean (that link rests on TLC and the traces). The cost bounds are
  proved for one pass of the abstract part system (parts, bytes of the parts, messages); through the open
  refinement they are not yet theorems about the byte handlers, and the session formulas `RoundsBound` and
  `BytesBound` (with the exact pass, the cold stream and the framing) are checked by TLC only. That no stale state
  survives across attempts is proved for the model of the handlers and the driver (`runAttempts_fresh`). TLC replays
  a size-bounded subset of the reconcile trace; the Lean replay takes all of it.
- `pinc-broadcast`: the liveness theorems cover runs without restarts.
- Of the transport (`pinc-transport`) the key layer, the stream table's receive and credit path, loss recovery
  (the sent ring, the byte accounts, loss detection, the probe timer, ghosts, tail repair), the received packet ranges
  and ack thinning, connection ids, congestion control and pacing, the packet number truncation and expansion, the
  handshake fragment reassembly, the path MTU state machine, the long and short header codecs, the packets of a
  datagram, the associated data of `seal` and `open`, the body of a Handshake packet (the message length and the
  offset, two varints written by `write_handshake` and read by `Handshake::on_fragment`), `pad_to`, the sample
  `sample_at` takes for header protection, the frame codecs (every frame type), the frames the packet
  builder puts into a packet (their order, the dropped length of the last STREAM frame, the payload read back), the
  registry of extension frame types with the layer each extension frame reaches (the values layer's own type tests
  are traced only through the endpoint's ring: see the row) and
  the connection's timers and closing state are proved and traced. Since then the frames each kind of packet
  carries (`PacketKind`, `trace_packet_kind`) and path validation and migration (`PathMove`, `trace_path_move`,
  `trace_path_held`) each have a model and a trace check: see their rows under [Properties](properties.md). Not done
  yet: the two-endpoint scenario models. They act on the whole `Connection`: a trace of them needs a view of its paths
  and streams (the timers have theirs, `TimerView`, and `trace_timers` a scripted pair of connections).
  Of the timers, the trace never saw the MTU deadline as the minimum nor the acknowledgement deadline held back by
  the amplification gate (both are in the TLC and Lean checks), and it records connections from the established
  state, from a dial nobody answers or from a dialing side connected to a responder that still waits for its Finish:
  the handshake establishing the session (`Est`) is checked by TLC and Lean only, and a handshake packet heard while
  connected (a resumed server's kept reply) is not modelled. That the probe backoff does not grow while the peer
  sleeps or the link is down is loss recovery's rule, in its models; here recovery's deadline and its giving up are
  inputs. The carrier rule is traced from a session whose carrier time the
  test sets (`set_carrier_heard`); what the endpoint reports as that time (`pinc-connect`) is not modelled here.
  The end of a dialing side's session its peer never confirmed ([#390](https://github.com/sourcenetwork/pinc/pull/390))
  counts from the establishment in the models, which have no key answers; that a late key answer (a slow key host)
  does not shorten the wait is tested, not modelled (the first form of the change counted from the handshake's last
  datagram or timer and ended such a session early: found while modelling it, and corrected).
  The buffer of packets that arrive before their keys is modelled (see its row above); what it leaves open is what
  the frames of a drained packet do, beyond the drop of a 0-RTT packet with a frame only an established session
  sends, and a held packet that opens in the connection trace (the resumed servers' real 0-RTT packets arrive
  after their Hello).
- The congestion controller's cubic term (the origin `K` and the target) is checked at full width by the Lean replay
  only; TLC checks the bounded step of congestion avoidance (see the row above).
- The loss recovery TLC configs are small (a ring of 2 or 3 slots, three or four packet numbers, at most four to six
  calls, a clock of 8 to 90 units with the millisecond as 1 unit) and the trace check runs the real constants; the
  Lean theorems are unbounded in the ring, the times and the run. The order of the ring and the life of a slot are
  proved for every call and through every loop (`TransportRecoveryRing`: the packet numbers stay strictly increasing
  and at most the last one sent, `timeout_ok`, `flush_ok`, `ack_ok`, `send_ok`, `untracked_ok`; a slot found again by
  its number is the same packet, done if it was done and never back in flight, `*_doneStays`). Of `RingShape` the
  length is `push_len`, and its two other conjuncts are proved in `TransportRecoveryAck`: a slot's path is below the
  path count (`RingPath`, kept by `send_path`, `untracked_path`, `ack_path`, `timeout_path`, `flush_path`) and the
  largest acknowledged is not above the last sent (`LaLs`, kept by `send_laLs`, `untracked_laLs`, `ack_laLs`,
  `timeout_laLs`, `flush_laLs`), so all of `RingShape` is proved in Lean. The detection loop is proved to report only
  packets that were in flight (`detectLoop_lost_inflight`), and the acknowledgement loop to report an `acked` event
  only for a slot that was in flight in the ring the call found, with its number, size and frames, a `late` event
  only for a ghost of that ring, and no other event (`ackRing_events`, `ackRange1_events`, `ackRanges_events`).
- Of the stream table, the send half (send credit, the retransmission queue with its cut to the acknowledged
  prefix, the final size, source-backed streams) is modelled by `StreamSend.tla`: see its rows under
  [Properties](properties.md), transport. Urgency order is not modelled.
- The stream-table TLC configs are kept to about a minute each on the check host, which cut them to: `Streams`
  (offsets up to 3 of a 8-byte cap, was 6 of 12), `Streams_caps` (two slots, ids 0, 4 and 8, frames at offsets up to 2,
  was 3, a clock that does not advance), `Streams_ext` (offsets up to 2 of a 6-byte cap, was 4 of 12, other users of
  the pool up to 3 chunks), `Streams_ledger` (offsets up to 3, was 4) and `Streams_two` (two peer streams, offsets up
  to 1, a pool of 4 chunks). The longer runs of the cut configs are no longer checked by TLC. The cases they covered
  are carried unbounded in Lean: the ledger and the admission by `grantOne_ledger`, `frame_needs_no_more_than_ledger`
  and `admits_cap` (sums over all slots, any pool and window), delivery by `exactly_once_in_order` and
  `stored_immutable`, the final size by `onData_final_fixed`, the ring by `ring_never_overflows`. The two-stream
  interplay of the ledger is checked by `Streams_two` at small sizes and proved for any number of slots by
  `grantOne_ledger`, not end to end.
- The stream-table TLC configs are small (chunks of 1 or 2 bytes, 1 to 4 slots, windows of 2 to 6 bytes, a pool of 4
  to 6 chunks) and the trace check runs the real constants; the Lean theorems are unbounded in all of them. The Lean
  theorems of the table state facts about the grant, the admission and the receive half one step at a time and
  about the byte content in an abstract model; a Lean proof that the whole table keeps the slot invariant under
  every call (the inductive invariant TLC checks) is not done yet. The ledger conservation under a store (the
  demand falls by exactly the chunks the store takes) is checked by TLC (`LedgerAlways`) and the trace, and not yet
  proved in Lean.
  That a stream inside the credit is never held back is checked by TLC (`NoHeldWithinCredit`, configs with no other user
  of the pool) and not proved in Lean.
  The ledger holds across every way the table grants credit: a grant (`grantOne_ledger`), a peer admission
  (`admits_cap`'s companion test `windowsFit`) and a local stream (`openLocal_ledger`); that the free slot a stream
  takes is a new one (`FreeIsNew`) is checked by TLC and not yet proved in Lean.
- `pinc-membership`: the hub side of the 145 s awareness chain is proved over any sequence of the host's calls
  (`MembershipTimerRun.lean`, `MembershipTimerLease.lean`, `MembershipTimerDown.lean`): no input moves the tick
  deadline, the tick runs in every window of one tick period plus the host's slack, the lease of a crashed member is
  gone at that tick, and the tick hands its DOWN delta to every attached hub. Still open: the delivery of the DOWN to
  the member within 48 s as a theorem (delivery on a live session stays a
  hypothesis; the receiving hub's view step and its home deltas are proved per call by `applyDeltaCore_down_homes`, with
  the hub's own quiet window and the other hubs' copies as hypotheses, and the DOWN is sent once, with no retry); the
  awareness bound needs that the member's host is not later than `WAKE_GAP` at a tick between the DOWN and the removal:
  a late tick defers every waiting removal to the new window's end (`late_tick_reopens`, the reference model's rule), so
  a host slack above `WAKE_GAP` at every tick of a member keeps the member in the view. A heal does not: since #284 it
  leaves a waiting removal at its own instant and grace state (`heal_keeps_waiting`; TLC: `WaitKept`, with the rule
  before as the witness `MembershipSys_w_healwait.cfg`), and the removal is applied at that instant plus the one extra
  look whatever window is open (`recheckDue_removes`, `heal_then_removed`). That the removal's own instant is within
  `QUIET` of the DOWN (the window's length, `beginQuiet_window`) is a hypothesis of `awareness_budget`, not yet a
  theorem over runs, and so is that no late tick happens in between. Also open: the
  whole-run churn and heal theorems, the full-roster branch in the traces
  (a roster of `MAX_TABLE` entries needs about 8 million snapshot entries in the trace, and the model's ordered loops are
  quadratic in the table), that the trace of a view removal names a lease expiry only when a full lease of omission
  passed (the event raised, `left` or `down`, is proved), and the revocation invariant for the whole machine (proved per call for `recompute_one`,
  `apply_delta` and the helpers; the walk of the larger calls does not finish in the proof tactic yet).
- `pinc-values`: the five corrections found by the proofs are made and proven (HEAD_HOLD tail, one announcement per granule,
  stall timer started at the first verified granule (it was armed by the first request, then changed in 3ec9fb3), a wrong out-of-band proof frame evicts its provider, supersession after the
  install), and the gaps of the first round are closed in both languages (the flat `byteAt` equality, the run-wide exact
  partition and `take_chunk` exactness, split order and exactly once, completion at the queue level, the scheduling of
  the system model, the server slot table in the traces). Still open: the exact partition is proven for runs in which
  no list fills (the room guards of `ReachR`; a widened push is covered by `Cover`, not by `Exact`), and the sizes of a
  chunk and of a steal are the environment's in both models (their arithmetic is `ValuesSched`). Liveness theorems keep
  an explicit fairness hypothesis, as liveness requires.
- `pinc-connect`: the sleep and beacon signing jobs of the client, the local duty cycle and radio, the drive, the
  carriers and the candidates of a flight each have a model and a trace check since (`ConnectSleep`, `ConnectDuty`,
  `ConnectRadio`, `ConnectDrive`, `ConnectCarriers`, `ConnectFlight` under [Properties](properties.md)). The node's own record and address discovery is proved (candidate list, acceptance of a QADR answer, sequence number, when a record is signed, see "connectivity own record"; the timer path of a record job has no trace, as the trace has no open carrier), and so is the relay side (record store, lookup, expiry, the relay's own record and its republish, see "connectivity record store"). Not proven yet are the sleep tether beyond what those rows state, the scenario
  models (relay path, direct path after punching, fallback after a block, sleep and wake), and liveness under stated
  fairness (the link and client rules have bounded-response checks only). The pending, lookup and netcheck tables
  are model checked and traced, with Lean theorems for their sizes and single decisions only. Of the protected
  carrier (`session.rs`), the handshake machine is an input of the models (its outputs are
  taken from the run; it is proved by itself) and the any-split theorem covers hosts that only read and poll. Of the client rules,
  three statements are not proved in Lean yet: that a splice just seen has age 0, that a thin dial try sends on at most
  one candidate, and that taking a peer from the pending table clears its entry. The source address of a tunnel packet and the freshness of a found record are not
  modelled, and the thin kind of a running dial has no check ([#748](https://github.com/sourcenetwork/pinc/issues/748)).
- `pinc-connect`, the protected carrier: three places where the code does not do what `session.rs` documents, found
  while modelling it (the models follow the code; nothing is delivered, opened or sealed after the end in any of
  them). The module says that after the end every later call returns `Closed`, but `answer_soft` returns
  `Handshake(UnexpectedKeyResponse)`, `seal_bytes` checks the length first (`UnitSize`, `NoRoom`) and `seal` the encoder
  and the room (`Frame`, `NoRoom`); `transmit` still hands out handshake bytes queued before the end. `key_response`
  is documented to fail with `Handshake` when no request is outstanding, but on an open carrier it returns `Closed` and
  ends the carrier. `free()` is documented as how many bytes `receive` would take now, but after a poll that took a
  unit it is short by that unit until the next `receive` or `poll` releases it.
- The facade `pinc`: proven are the access gate, the access decisions per protocol and direction with revocation
  against the answer cache, discovery by signed records, and the standby slab with the drive's turn (rows above).
  Since the fix of
  [#311](https://github.com/sourcenetwork/pinc/issues/311) the queue holds tickets and the baton skips the entry of a
  released one, so it wakes the oldest waiting ticket as the module docs of `standby.rs` say; since the fix of
  [#419](https://github.com/sourcenetwork/pinc/issues/419) the release that brings a slot's generation round drops
  the queue's stale entries, so no stale entry names a live slot again and the order is proved of every run of the
  slab's calls (Lean with 2^32 generations, TLC with 2 and 3); the rule before each fix is kept as a witness. Since
  then the facade's buffers, machines, open gate, stream calls, waits, turn, records and saved state, and of the relay
  role its carriers and what it keeps, each have a model with a trace check or a model-based test (rows under
  [Properties](properties.md)). Not proven yet: the files that no row or trace names (matched by name, so one may be
  covered under another row): of the relay role `relay/hub.rs`, `relay/run.rs`, `relay/peers.rs`,
  `relay/carrier_fns.rs`, `relay/fx.rs`, `relay/limits.rs` and `relay/stats.rs`, the carrier and HTTP I/O
  (`drive/carrier_io.rs`, `drive/http_io.rs`), `mem.rs`, `host.rs`, `maps.rs`, `body.rs` and `endpoint_topics.rs`; and
  `notifyall` ([#748](https://github.com/sourcenetwork/pinc/issues/748)); its async plumbing is assumed of the host
  ([#246](https://github.com/sourcenetwork/pinc/issues/246) (c)).
