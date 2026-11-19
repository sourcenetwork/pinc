------------------------------- MODULE Reach --------------------------------
(***************************************************************************)
(* The ring of REACH_OUT bodies (pinc-core reach.rs): every sequence of    *)
(* puts at small sizes (ReachOps.tla has the operators; a get changes      *)
(* nothing).                                                               *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the ring never grows: N places; its counter is the number of puts    *)
(*    (Bounded);                                                           *)
(*  - a body longer than MX is never stored (Short);                       *)
(*  - at most one body per session (OnePerSession), and it is the latest   *)
(*    put for that session (Latest, a ghost `last` per session), so a get  *)
(*    returns the latest body of a held session, and nothing for one that  *)
(*    is not held (GetLatest);                                             *)
(*  - the stamp of a place is the number of the put that wrote it, the     *)
(*    last put of its session (StampIsLastPut, against the ghost seenT);   *)
(*  - the filled places come first: a place is empty only if every place   *)
(*    after it is (Room), so a session that is not held never overwrites   *)
(*    another while there is room and loses nothing (RoomRule);            *)
(*  - the rule of a put (PutRule): the counter moves on by one; a too-long *)
(*    body changes no place and put returns 1; a session that is held gets *)
(*    its own place, no other place changes and put returns 0; a session   *)
(*    that is not held takes the first empty place and put returns 0, or,  *)
(*    in a full ring, the place with the smallest stamp and put returns 1; *)
(*    no other place changes;                                              *)
(*  - which body goes (EvictsLeastRecent): a full ring gives up the body   *)
(*    of the session put longest ago, by the ghost seenT of every put that *)
(*    kept a body;                                                         *)
(*  - every body is counted (Counted): the puts are the bodies held, the   *)
(*    refreshes (a body replaced by a later one of its session) and the    *)
(*    bodies put returned as lost (`dropped`, what the endpoint adds to    *)
(*    its count).                                                          *)
(* Witnesses: Reach_dup (a held session also takes a new place:            *)
(* OnePerSession and Latest fail), Reach_newest (a full ring overwrites    *)
(* the body put last: PutRule fails), Reach_first (EvictsFirstIn: the code *)
(* does NOT give up the session that entered the ring first, because a     *)
(* refresh counts as a put: after puts for A, B, C and A again, D takes    *)
(* B's place). Reach_refresh, Reach_evict, Reach_refuse and Reach_renew    *)
(* are reachability witnesses: a refresh, an eviction, a refused body and  *)
(* a refresh of the body put longest ago in a full ring happen.            *)
(* Lean counterpart: proofs/lean/Pinc/CoreReach*.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets
CONSTANTS N, MX, S, LS, PMAX, DUP, NEWEST
VARIABLES r, last, born, seenT, nextId, act, arg, lost, dropped, refreshed
vars == <<r, last, born, seenT, nextId, act, arg, lost, dropped, refreshed>>

INSTANCE ReachOps

SS == 1..S

Init == /\ r = Reach0(N)
        /\ last = [s \in SS |-> None] /\ born = [s \in SS |-> 0] /\ seenT = [s \in SS |-> 0]
        /\ nextId = 1 /\ act = "init" /\ arg = None /\ lost = 0 /\ dropped = 0 /\ refreshed = 0

PutStep == \E l \in LS, s \in SS :
    LET b == <<nextId, l>>
    IN /\ r' = RPut(r, N, MX, s, b, DUP, NEWEST)
       /\ lost' = RLost(r, N, MX, s, b, DUP, NEWEST)
       /\ dropped' = dropped + lost'
       /\ refreshed' = IF l <= MX /\ Has(r.cells, N, s) THEN refreshed + 1 ELSE refreshed
       /\ nextId' = nextId + 1
       /\ last' = IF l > MX THEN last ELSE [last EXCEPT ![s] = b]
       /\ born' = IF l > MX \/ Has(r.cells, N, s) THEN born ELSE [born EXCEPT ![s] = nextId]
       /\ seenT' = IF l > MX THEN seenT ELSE [seenT EXCEPT ![s] = nextId]
       /\ act' = "put" /\ arg' = <<s, b>>

Next == PutStep
Spec == Init /\ [][Next]_vars
Bound == nextId <= PMAX

C == r.cells
Bounded == /\ DOMAIN C = 0..N - 1 /\ r.clock = nextId - 1
Short == \A i \in Occ(C, N) : C[i][2][2] <= MX
OnePerSession == \A i, j \in Occ(C, N) : C[i][1] = C[j][1] => i = j
Latest == \A i \in Occ(C, N) : last[C[i][1]] = C[i][2]
StampIsLastPut == \A i \in Occ(C, N) : C[i][3] = seenT[C[i][1]]
Room == \A i, j \in 0..N - 1 : (i < j /\ C[i] = None) => C[j] = None
Counted == nextId - 1 = refreshed + dropped + Cardinality(Occ(C, N))
Inv == Bounded /\ Short /\ OnePerSession /\ Latest /\ StampIsLastPut /\ Room /\ Counted

Same(c1, c2, except) == \A i \in 0..N - 1 : i # except => c1[i] = c2[i]

PutRuleA ==
    act' = "put" =>
        LET s == arg'[1] b == arg'[2] t == r.clock + 1
        IN /\ r'.clock = t
           /\ IF b[2] > MX
              THEN r'.cells = C /\ lost' = 1
              ELSE IF Has(C, N, s)
                   THEN LET p == Pos(C, N, s)
                        IN Same(r'.cells, C, p) /\ r'.cells[p] = <<s, b, t>> /\ lost' = 0
                   ELSE \E p \in 0..N - 1 :
                          /\ Same(r'.cells, C, p) /\ r'.cells[p] = <<s, b, t>>
                          /\ IF Full(C, N)
                             THEN lost' = 1 /\ \A i \in 0..N - 1 : C[p][3] <= C[i][3]
                             ELSE lost' = 0 /\ C[p] = None /\ \A j \in 0..p - 1 : C[j] # None
GetLatestA == act' = "put" =>
    LET s == arg'[1] b == arg'[2]
    IN IF b[2] > MX THEN RGet(r', N, s) = RGet(r, N, s) ELSE RGet(r', N, s) = b
\* a session that is not held never overwrites another while there is room, and loses nothing
RoomRuleA == (act' = "put" /\ arg'[2][2] <= MX /\ ~Has(C, N, arg'[1]) /\ ~Full(C, N)) =>
    /\ lost' = 0
    /\ \A i \in Occ(C, N) : r'.cells[i] = C[i]
PutRule == [][PutRuleA]_vars
GetLatest == [][GetLatestA]_vars
RoomRule == [][RoomRuleA]_vars

\* which body a full ring gives up, by the ghosts: the session put longest ago (it holds), or the one that entered
\* first (a witness: it does not)
NewHeld == act' = "put" /\ arg'[2][2] <= MX /\ ~Has(C, N, arg'[1]) /\ Full(C, N)
Victim == CHOOSE v \in 0..N - 1 : r'.cells[v] # C[v]
EvictsLeastRecentA == NewHeld => \A i \in 0..N - 1 : seenT[C[Victim][1]] <= seenT[C[i][1]]
EvictsFirstInA == NewHeld => \A i \in 0..N - 1 : born[C[Victim][1]] <= born[C[i][1]]
EvictsLeastRecent == [][EvictsLeastRecentA]_vars
EvictsFirstIn == [][EvictsFirstInA]_vars

\* reachability witnesses
NoRefresh == [][~(act' = "put" /\ arg'[2][2] <= MX /\ Has(C, N, arg'[1]))]_vars
NoEvict == [][~NewHeld]_vars
NoRefuse == [][~(act' = "put" /\ arg'[2][2] > MX)]_vars
\* a full ring refreshes the body put longest ago, which is then not the next one given up
NoRenewOldest == [][~(act' = "put" /\ arg'[2][2] <= MX /\ Full(C, N) /\ Has(C, N, arg'[1])
                      /\ \A i \in 0..N - 1 : C[Pos(C, N, arg'[1])][3] <= C[i][3])]_vars
=============================================================================
