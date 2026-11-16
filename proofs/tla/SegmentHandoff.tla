---------------------------- MODULE SegmentHandoff ----------------------------
(***************************************************************************)
(* Who gets a spare pool segment, and what they find in it (vinc#435).     *)
(*                                                                         *)
(* Who acts: the sessions of one endpoint, each in a slot. A session that  *)
(* needs more pool memory than its first chunk takes a segment: a spare    *)
(* one if the endpoint has one (the one freed last), else one it asks the  *)
(* system for, which the system may refuse. A session writes its bytes in  *)
(* its segment, goes quiet (its segment goes spare, with its bytes in it), *)
(* and ends (the next session of the slot is a new session). A session    *)
(* that only shakes hands holds one chunk at a time, its first, which is   *)
(* an allocation of its own.                                               *)
(*                                                                         *)
(* What must never happen: a session that can read bytes another session  *)
(* wrote (on a hub, one member's data reaching another member); a segment *)
(* cleared for the session that wrote it (a cost for nothing on the path   *)
(* where a session goes quiet after every request); a refused segment that *)
(* aborts the process; a session that only shakes hands taking a segment. *)
(*                                                                         *)
(* Code: Segments::take, put, session and Grown::make, take, release,      *)
(* reset, locate in crates/vinc-transport/src/stream/pool/grown.rs         *)
(* (OWN_CHUNKS); the session's reset in Endpoint::alloc_slot               *)
(* (crates/vinc-core/src/endpoint.rs). The timer that gives spares back    *)
(* is SegmentTimer.tla; this model has no expiry, which only ever removes  *)
(* the oldest spares.                                                      *)
(*                                                                         *)
(* Lean counterpart: PoolGrown.lean, `seen_clean`, `seen_own`,             *)
(* `no_clear_leaks` (what a take shows) and `own_segment`, `own_alone`,    *)
(* `no_own_shares` (the first chunk is a segment of its own).              *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

\* Slots: the slots of the endpoint; MaxOps: the inputs in a run; Refusals: whether the system may refuse a segment;
\* Bug: "none" for the code, or the bug a RED configuration plants.
CONSTANTS Slots, MaxOps, Refusals, Bug

VARIABLES
    sid,        \* sid[k]: the number of the session in slot k
    hold,       \* hold[k]: what session k keeps its later chunks in: "none", a "seg"ment, or chunks "apart"
    seen,       \* seen[k]: whose bytes session k can read in its segment, 0 for zeros (while hold[k] = "seg")
    refused,    \* refused[k]: the system refused session k a segment, so it keeps its chunks apart until it ends
    spares,     \* the spare segments, oldest first, each the number of the session whose bytes it holds (0: zeros)
    next,       \* the number the next new session gets
    ops,        \* inputs so far
    mapped,     \* segments the system mapped, in all
    helloSegs,  \* segments taken by sessions that only shook hands
    ownCleared, \* segments cleared for the session that wrote them
    aborted     \* the process aborted

vars == <<sid, hold, seen, refused, spares, next, ops, mapped, helloSegs, ownCleared, aborted>>

\* The sessions that hold a segment now.
Holders == {k \in Slots : hold[k] = "seg"}

\* What session k finds in a spare that session w's bytes fill: its own bytes as they were if w is k's session, else
\* nothing, the segment emptied. RED "noclear": another session's bytes are left in it. RED "clearown": it is cleared
\* even for the session that wrote it.
Found(k, w) ==
    IF w = sid[k]
    THEN IF Bug = "clearown" THEN 0 ELSE w      \* its own segment: kept as it was
    ELSE IF Bug = "noclear" THEN w ELSE 0       \* another's: emptied

\* Session k gets a segment the system maps now: it holds zeros.
Mapped(k) ==
    /\ mapped' = mapped + 1                     \* the system maps one more
    /\ hold' = [hold EXCEPT ![k] = "seg"]        \* the session keeps its chunks in it
    /\ seen' = [seen EXCEPT ![k] = 0]            \* new memory reads as zeros

\* An input in which session k needs a chunk past its first (Grown::take, Grown::make).
Take(k) ==
    /\ ops < MaxOps                             \* the run still has inputs
    /\ ~aborted                                 \* the process still runs
    /\ hold[k] = "none"                         \* the session has no segment yet
    /\ ops' = ops + 1                           \* one more input
    /\ IF refused[k]
       THEN /\ hold' = [hold EXCEPT ![k] = "apart"]   \* refused once: chunks apart, no new ask
            /\ UNCHANGED <<seen, refused, spares, mapped, ownCleared, aborted>>
       ELSE IF spares # <<>>
       THEN LET w == spares[Len(spares)]              \* whose bytes the spare freed last holds
            IN /\ spares' = SubSeq(spares, 1, Len(spares) - 1)   \* it leaves the spares
               /\ hold' = [hold EXCEPT ![k] = "seg"]  \* the session keeps its chunks in it
               /\ seen' = [seen EXCEPT ![k] = Found(k, w)]       \* and finds what the take leaves in it
               /\ ownCleared' = ownCleared + (IF w = sid[k] /\ Bug = "clearown" THEN 1 ELSE 0)   \* a needless clear
               /\ UNCHANGED <<refused, mapped, aborted>>
       ELSE \/ /\ Mapped(k)                           \* the system grants a segment
               /\ UNCHANGED <<refused, spares, ownCleared, aborted>>
            \/ /\ Refusals                            \* or refuses it
               /\ IF Bug = "abort"
                  THEN /\ aborted' = TRUE             \* RED: an allocation that cannot fail aborts
                       /\ UNCHANGED <<hold, seen, refused, spares, mapped, ownCleared>>
                  ELSE /\ refused' = [refused EXCEPT ![k] = TRUE]   \* counted, and kept for the session
                       /\ hold' = [hold EXCEPT ![k] = "apart"]      \* its chunks are allocations of their own
                       /\ UNCHANGED <<seen, spares, mapped, ownCleared, aborted>>
    /\ UNCHANGED <<sid, next, helloSegs>>

\* An input in which session k writes its bytes into its segment.
Write(k) ==
    /\ hold[k] = "seg" /\ seen[k] # sid[k]       \* it holds a segment it has not written yet
    /\ ~aborted                                 \* the process still runs
    /\ seen' = [seen EXCEPT ![k] = sid[k]]       \* from now on the segment holds its bytes
    /\ UNCHANGED <<sid, hold, refused, spares, next, ops, mapped, helloSegs, ownCleared, aborted>>

\* An input in which a session with no segment only shakes hands: it holds one chunk at a time, its first, an
\* allocation of its own, and takes no segment. RED "noown": its first chunk lies in a segment, which it takes new.
Hello(k) ==
    /\ ops < MaxOps                             \* the run still has inputs
    /\ ~aborted                                 \* the process still runs
    /\ hold[k] = "none"                         \* the session holds no segment
    /\ ops' = ops + 1                           \* one more input
    /\ IF Bug = "noown"
       THEN /\ Mapped(k)                          \* RED: the handshake maps a segment
            /\ helloSegs' = helloSegs + 1         \* counted against the rule
       ELSE UNCHANGED <<hold, seen, mapped, helloSegs>>   \* the code: nothing but its own chunk
    /\ UNCHANGED <<sid, refused, spares, next, ownCleared, aborted>>

\* What going quiet leaves of session k's memory: a segment goes spare with what it holds; chunks apart go to the
\* allocator.
Free(k) ==
    /\ spares' = IF hold[k] = "seg" THEN Append(spares, seen[k]) ELSE spares   \* a segment is kept spare
    /\ hold' = [hold EXCEPT ![k] = "none"]       \* the session holds nothing more

\* An input after which session k is quiet (Streams::settle trims: Grown::release puts its segment in Segments).
Quiet(k) ==
    /\ ops < MaxOps                             \* the run still has inputs
    /\ ~aborted                                 \* the process still runs
    /\ hold[k] # "none"                         \* it has something to free
    /\ ops' = ops + 1                           \* one more input
    /\ Free(k)
    /\ UNCHANGED <<sid, seen, refused, next, mapped, helloSegs, ownCleared, aborted>>

\* The session of slot k ends and a new session takes the slot (Endpoint::alloc_slot resets the pool: Grown::reset
\* frees what it held, numbers a new session, and forgets the refusal).
End(k) ==
    /\ ops < MaxOps                             \* the run still has inputs
    /\ ~aborted                                 \* the process still runs
    /\ ops' = ops + 1                           \* one more input
    /\ Free(k)
    /\ sid' = [sid EXCEPT ![k] = next]           \* the slot's next session is a new one
    /\ next' = next + 1                         \* with a number never given before
    /\ refused' = [refused EXCEPT ![k] = FALSE]  \* it asks the system again
    /\ UNCHANGED <<seen, mapped, helloSegs, ownCleared, aborted>>

Init ==
    /\ sid = [k \in Slots |-> k]                \* slot k starts with session k
    /\ hold = [k \in Slots |-> "none"]          \* no session holds anything
    /\ seen = [k \in Slots |-> 0]               \* and has read nothing
    /\ refused = [k \in Slots |-> FALSE]        \* the system has refused nothing
    /\ spares = <<>>                            \* nothing is spare
    /\ next = Cardinality(Slots) + 1            \* the next session number
    /\ ops = 0 /\ mapped = 0 /\ helloSegs = 0 /\ ownCleared = 0 /\ aborted = FALSE

Next == \E k \in Slots : Take(k) \/ Write(k) \/ Hello(k) \/ Quiet(k) \/ End(k)

Spec == Init /\ [][Next]_vars

\* A session can read in its segment only zeros and its own bytes, never another session's.
NoForeignBytes == \A k \in Slots : hold[k] = "seg" => seen[k] \in {0, sid[k]}

\* A session that takes back the segment it wrote finds it as it was: nothing is cleared on that path.
OwnKept == ownCleared = 0

\* A segment the system refuses aborts nothing.
NoAbort == ~aborted

\* A session that only shakes hands takes no segment.
HelloMapsNothing == helloSegs = 0

\* A session the system refused takes no segment until it ends: it does not ask again on every chunk.
RefusedApart == \A k \in Slots : refused[k] => hold[k] # "seg"

\* Every segment mapped is held by a session or spare: none is lost (this model has no expiry).
Conserved == mapped = Cardinality(Holders) + Len(spares)
=============================================================================
