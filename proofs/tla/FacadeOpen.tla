----------------------------- MODULE FacadeOpen -----------------------------
(***************************************************************************)
(* The facade's queue of stream opens that wait for a place.               *)
(*                                                                         *)
(* Who acts. Application futures ask to open a stream on one session. The  *)
(* peer gives the session a fixed number of places; an open that finds     *)
(* none waits. A stream that ends gives its place back, and the endpoint   *)
(* then wakes a waiting open. A woken open runs only when its executor     *)
(* polls it, so between the wake and the poll anything else may happen:   *)
(* a place frees, another open asks, a waiting open is dropped.            *)
(*                                                                         *)
(* What must never happen. An open takes a place while an open that asked *)
(* before it still waits (NoOvertake). A place is free, an open waits for  *)
(* it, and no waiting open is woken to take it (NoStall). More streams are *)
(* open than there are places (PlacesKept).                                *)
(*                                                                         *)
(* Rust: crates/pinc/src/engine.rs `Core::{wake_s, wake_open, forget,      *)
(* open_ahead}` (the wait list `Sess::waits`, `first_wait`);               *)
(* crates/pinc/src/engine/ops.rs `Core::open`; crates/pinc/src/drive.rs    *)
(* `Shared::run_as` (sets `Core::caller`, the ticket of the running open). *)
(* Lean counterpart: Pinc/FacadeOpen.lean.                                 *)
(*                                                                         *)
(* Witnesses (scripts/proofs.sh witness_tlc): Fifo = FALSE is the code     *)
(* before #162: a wake took every waiting open off the list and an open    *)
(* that had never waited took a free place at once, so NoOvertake fails.   *)
(* Handoff = FALSE keeps the queue but drops the wake of the next open     *)
(* when the oldest leaves: with two places freed at once the second stays  *)
(* free beside a sleeping waiter, so NoStall fails.                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Opens,    \* the futures that each ask for one stream
    Places,   \* how many streams the peer lets the session hold at once
    Fifo,     \* TRUE: the queue as built; FALSE: the old wake-everyone code (a witness config)
    Handoff   \* TRUE: the oldest open that leaves wakes the next; FALSE: it does not (a witness config)

VARIABLES
    st,         \* per open: "idle" (has not asked), "wait", "open" (holds a place) or "gone"
    waits,      \* the session's wait list for opens, oldest first (Sess::waits, the Open entries)
    woken,      \* the opens notified and not yet polled
    free,       \* the places not held
    clock,      \* counts the asks, to order them
    askedAt,    \* per open: the clock of its ask (0 before it asked)
    overtaken   \* history: some open took a place while an earlier one waited

vars == <<st, waits, woken, free, clock, askedAt, overtaken>>

\* Is `o` on the wait list?
Listed(o) == \E i \in 1..Len(waits) : waits[i] = o

\* The wait list without `o`, the others kept in their order (retain in `forget`).
Without(o) == SelectSeq(waits, LAMBDA x : x # o)

\* The opens on the wait list, as a set.
ListedSet == {waits[i] : i \in 1..Len(waits)}

\* The opens that wait, listed or not (the old code takes them off the list when it wakes them).
Waiting == {o \in Opens : st[o] = "wait"}

\* Some open other than `o` asked before time `t` and still waits.
Earlier(o, t) == \E w \in Waiting \ {o} : askedAt[w] < t

\* The open `o` that asked at time `t` takes a place; note an overtake if an earlier open still waits.
Take(o, t) ==
    /\ free' = free - 1
    /\ st' = [st EXCEPT ![o] = "open"]
    /\ overtaken' = (overtaken \/ Earlier(o, t))

\* The opens to wake when `o`, at the head of `w`, leaves it: the next one, with the hand-off.
Next2(w) == IF Handoff /\ Len(w) > 1 THEN {w[2]} ELSE {}

Init ==
    /\ st = [o \in Opens |-> "idle"]
    /\ waits = <<>>
    /\ woken = {}
    /\ free = Places
    /\ clock = 0
    /\ askedAt = [o \in Opens |-> 0]
    /\ overtaken = FALSE

\* An open asks for the first time. It has no ticket yet (caller = None), so with the queue it waits behind any
\* listed open (open_ahead); otherwise it takes a free place or joins the end of the list.
Ask(o) ==
    LET t == clock + 1 IN
    /\ st[o] = "idle"
    /\ clock' = t
    /\ askedAt' = [askedAt EXCEPT ![o] = t]
    /\ IF (Fifo /\ waits # <<>>) \/ free = 0
       THEN /\ st' = [st EXCEPT ![o] = "wait"]
            /\ waits' = Append(waits, o)
            /\ UNCHANGED <<woken, free, overtaken>>
       ELSE /\ Take(o, t)
            /\ UNCHANGED <<waits, woken>>

\* A woken open is polled and asks again, now with its ticket (caller = its own).
Poll(o) ==
    /\ o \in woken
    /\ st[o] = "wait"
    /\ IF Fifo
       THEN IF waits # <<>> /\ waits[1] = o /\ free > 0
            \* The oldest takes the place, leaves the list, and hands the turn on.
            THEN /\ Take(o, askedAt[o])
                 /\ waits' = Tail(waits)
                 /\ woken' = (woken \ {o}) \cup Next2(waits)
            \* Not the oldest, or no place: it stays where it is on the list.
            ELSE /\ woken' = woken \ {o}
                 /\ UNCHANGED <<st, waits, free, overtaken>>
       \* The old code: the wake took it off the list; it takes a place or joins the end again.
       ELSE IF free > 0
            THEN /\ Take(o, askedAt[o])
                 /\ woken' = woken \ {o}
                 /\ UNCHANGED waits
            ELSE /\ woken' = woken \ {o}
                 /\ waits' = IF Listed(o) THEN waits ELSE Append(waits, o)
                 /\ UNCHANGED <<st, free, overtaken>>
    /\ UNCHANGED <<clock, askedAt>>

\* A stream ends and gives its place back; the endpoint wakes waiting opens (wake_open): with the queue only the
\* oldest, which keeps its place on the list; in the old code every listed open, taken off the list.
Release(o) ==
    /\ st[o] = "open"
    /\ st' = [st EXCEPT ![o] = "gone"]
    /\ free' = free + 1
    /\ IF Fifo
       THEN /\ woken' = woken \cup (IF waits # <<>> THEN {waits[1]} ELSE {})
            /\ UNCHANGED waits
       ELSE /\ woken' = woken \cup ListedSet
            /\ waits' = <<>>
    /\ UNCHANGED <<clock, askedAt, overtaken>>

\* A waiting open is dropped (its future ends): `forget` takes it off the list, and the oldest that leaves hands
\* the turn on.
Cancel(o) ==
    /\ st[o] = "wait"
    /\ st' = [st EXCEPT ![o] = "gone"]
    /\ waits' = Without(o)
    /\ woken' = (woken \ {o}) \cup (IF Fifo /\ waits # <<>> /\ waits[1] = o THEN Next2(waits) ELSE {})
    /\ UNCHANGED <<free, clock, askedAt, overtaken>>

Next == \E o \in Opens : Ask(o) \/ Poll(o) \/ Release(o) \/ Cancel(o)

Spec == Init /\ [][Next]_vars

\* The values have their types.
TypeOK ==
    /\ st \in [Opens -> {"idle", "wait", "open", "gone"}]
    /\ woken \subseteq Opens
    /\ free \in 0..Places
\* Every held place is counted: the open streams and the free places add up to the places.
PlacesKept == Cardinality({o \in Opens : st[o] = "open"}) + free = Places
\* No open ever took a place while an open that asked before it still waited.
NoOvertake == ~overtaken
\* A free place with an open waiting for it always has a waiting open woken to take it.
NoStall == (free > 0 /\ Waiting # {}) => (woken \cap Waiting # {})
\* With the queue, the list holds exactly the waiting opens, each once, in the order they asked.
ListInOrder ==
    Fifo =>
        /\ ListedSet = Waiting
        /\ Len(waits) = Cardinality(Waiting)
        /\ \A i, j \in 1..Len(waits) : i < j => askedAt[waits[i]] < askedAt[waits[j]]
=============================================================================
