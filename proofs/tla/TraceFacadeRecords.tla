------------------------- MODULE TraceFacadeRecords -------------------------
(***************************************************************************)
(* Trace validation of the facade's record discovery against              *)
(* FacadeRecords.tla: crates/pinc/src/records.rs `PeerRecord::verified`,   *)
(* `newest`, `remember`, `Records::find` and crates/pinc/src/endpoint/     *)
(* records.rs `Endpoint::{signed_record, publish_record, lookup}`.         *)
(*                                                                         *)
(* The test `tests/trace_facade_records.rs` (file facade_records.ndjson)   *)
(* runs two publishing endpoints and one looking up, over an in-process    *)
(* store the test controls, with no relay (RELAYS FALSE: `lookup` returns  *)
(* what `find` gives). A record's sequence number is wall milliseconds,    *)
(* above TLC's integers, so the test writes its rank among the records its *)
(* node signed (1, 2, ...). Events:                                        *)
(*   publish {n, rank}         the node signed and published its record   *)
(*   tamper  {n, kind, rank, by} the test made the store hold, for n:      *)
(*            "replay": n's own record of that rank; "misfiled": node by's *)
(*            record of that rank; "forged": n's record of that rank with  *)
(*            one signature byte flipped                                   *)
(*   lookup  {n, rank}         `lookup(n)` answered the record of that rank *)
(*                             of n (0: None)                              *)
(* Each event is one action of the model with its parameters, and the     *)
(* answer must be the model's. The table bound (KNOWN_MAX 4096) is not     *)
(* reached by two nodes: eviction is checked by the model only.            *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable PINC_TRACE_DIR, the directory that holds facade_records.ndjson. *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLC, Json, IOUtils, TraceEnd

VARIABLES published, store, known, peak, answer, i
mvars == <<published, store, known, peak, answer>>

M == INSTANCE FacadeRecords WITH Nodes <- {"n1", "n2"}, MaxSeq <- 64, SeqCheck <- TRUE, KMAX <- 4096,
                                 RELAYS <- FALSE

Trace == ndJsonDeserialize(IOEnv.PINC_TRACE_DIR \o "/facade_records.ndjson")
Ev == Trace[i]

\* the record the store holds after a tamper event
Held(ev) == CASE ev.kind = "replay" -> [signer |-> ev.n, seq |-> ev.rank, sound |-> TRUE]
              [] ev.kind = "misfiled" -> [signer |-> ev.by, seq |-> ev.rank, sound |-> TRUE]
              [] ev.kind = "forged" -> [signer |-> ev.n, seq |-> ev.rank, sound |-> FALSE]

Step ==
    CASE Ev.op = "publish" -> M!Publish(Ev.n) /\ published'[Ev.n] = Ev.rank
      [] Ev.op = "tamper" -> M!Tamper(Ev.n) /\ store'[Ev.n] = Held(Ev)
      [] Ev.op = "lookup" -> M!Lookup(Ev.n) /\ answer'.rec.seq = Ev.rank
                              /\ (Ev.rank > 0 => answer'.rec.signer = Ev.n /\ answer'.rec.sound)
      [] OTHER -> FALSE

Init == M!Init /\ i = 1
Next == \/ i <= Len(Trace) /\ Step /\ i' = i + 1
        \* Finished: the trace was read to its end (a mismatch deadlocks before it)
        \/ i > Len(Trace) /\ UNCHANGED <<mvars, i>>
TraceSpec == Init /\ [][Next]_<<mvars, i>>

Inv == M!KnownGenuine /\ M!NoRollback /\ M!LookupNewest /\ M!AnswerGenuine
\* the end check (TraceEnd.tla): some behaviour consumed every line of a trace that has one
ReplayAtEnd == ReplaySeen(i > Len(Trace))
ReplayEnded == ReplayRead(Len(Trace))
=============================================================================
