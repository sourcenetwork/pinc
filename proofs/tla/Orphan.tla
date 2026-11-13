------------------------------- MODULE Orphan -------------------------------
(***************************************************************************)
(* The endpoint's table of handshake fragments held until the start of     *)
(* their message arrives (vinc-core orphan.rs), over every interleaving of *)
(* hold, take and expire at any times (a clock that steps back included),  *)
(* at small sizes (OrphanOps.tla has the operators).                       *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the table never grows: N entries whatever arrives, each datagram at  *)
(*    most MAX bytes (Bounded);                                            *)
(*  - held = replayed + expired + evicted + waiting after every call       *)
(*    (Balance);                                                           *)
(*  - the held datagrams have distinct places in the order of arrival,     *)
(*    all below the next one (Orders);                                     *)
(*  - after every call that looks at the table no datagram in it is older  *)
(*    than LIFE at the time of that call (Fresh);                          *)
(*  - a datagram is given out only if it was held for the message asked    *)
(*    for, is not older than LIFE, and is the oldest arrival of that       *)
(*    message still fresh; when none is given, none such was held          *)
(*    (GivenRight);                                                        *)
(*  - a datagram given out is gone from the table and never given again    *)
(*    (GivenOnce, and the last two lines of GivenRight);                   *)
(*  - a datagram of at most MAX bytes is always held; it costs a fresh     *)
(*    datagram its entry only when every entry holds a fresh one, and then *)
(*    only the oldest arrival; a longer one changes nothing; expire lets   *)
(*    go of exactly the old ones (HoldRight).                              *)
(* TAKE_LIFE is the age the take lets go at: LIFE as the code has it. The  *)
(* witness Orphan_stale sets it past every time, a take that forgot to     *)
(* expire, and GivenRight fails. Orphan_evict is a reachability witness:   *)
(* an eviction happens.                                                    *)
(* Lean counterpart: proofs/lean/Vinc/CoreOrphan*.lean.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, MAX, LIFE, TAKE_LIFE, TMAX, KEYS, HMAX
VARIABLES o, last, given, right, kept
vars == <<o, last, given, right, kept>>

INSTANCE OrphanOps

Init == o = Orphan0(N) /\ last = 0 /\ given = {} /\ right = TRUE /\ kept = TRUE

Entries(x) == {x.slots[k] : k \in DOMAIN x.slots} \ {None}
FreshOf(x, t) == {e \in Entries(x) : t - e[1] <= LIFE}

ExpireStep == \E t \in 0..TMAX :
    /\ o' = Expire(o, LIFE, t) /\ last' = t
    /\ kept' = (kept /\ Entries(o') = FreshOf(o, t))
    /\ UNCHANGED <<given, right>>

HoldStep == \E t \in 0..TMAX, key \in KEYS, len \in {1, MAX, MAX + 1} :
    LET x == Hold(o, MAX, LIFE, t, key, 0, len, o.order)
        new == <<t, o.order, key, 0, len, o.order>>
        fresh == FreshOf(o, t)
        full == Cardinality(fresh) = N
        victim == CHOOSE e \in fresh : \A f \in fresh : e[2] <= f[2]
    IN /\ o' = x.o
       /\ last' = IF x.ok THEN t ELSE last
       /\ kept' = (kept /\ IF len > MAX THEN ~x.ok /\ o' = o
                           ELSE /\ x.ok
                                /\ Entries(o') = (IF full THEN fresh \ {victim} ELSE fresh) \cup {new}
                                /\ o'.evicted = o.evicted + (IF full THEN 1 ELSE 0))
       /\ UNCHANGED <<given, right>>

TakeStep == \E t \in 0..TMAX, key \in KEYS :
    LET x == Take(o, TAKE_LIFE, t, key)
        cand == {e \in FreshOf(o, t) : e[3] = key}
    IN /\ o' = x.o /\ last' = t
       /\ given' = IF x.out = None THEN given ELSE given \cup {x.out[2]}
       /\ right' = (right /\ IF x.out = None THEN cand = {}
                             ELSE /\ x.out \in cand
                                  /\ \A e \in cand : x.out[2] <= e[2]
                                  /\ x.out[2] \notin given
                                  /\ x.out \notin Entries(o'))
       /\ UNCHANGED kept

Next == ExpireStep \/ HoldStep \/ TakeStep
Spec == Init /\ [][Next]_vars
Bound == o.held <= HMAX

Bounded == /\ DOMAIN o.slots = 1..N
           /\ \A e \in Entries(o) : e[5] <= MAX
Balance == o.held = o.replayed + o.expired + o.evicted + Waiting(o)
Orders == /\ \A e \in Entries(o) : e[2] < o.order
          /\ \A j, k \in DOMAIN o.slots :
                (o.slots[j] # None /\ o.slots[k] # None /\ o.slots[j][2] = o.slots[k][2]) => j = k
Fresh == \A e \in Entries(o) : last - e[1] <= LIFE
GivenRight == right
GivenOnce == \A e \in Entries(o) : e[2] \notin given
HoldRight == kept
Inv == Bounded /\ Balance /\ Orders /\ Fresh /\ GivenOnce /\ HoldRight

\* a reachability witness: an eviction happens
NoEvict == o.evicted = 0
=============================================================================
