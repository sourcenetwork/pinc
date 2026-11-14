------------------------------- MODULE Reach --------------------------------
(***************************************************************************)
(* The ring of REACH_OUT bodies (vinc-core reach.rs): every sequence of    *)
(* puts at small sizes (ReachOps.tla has the operators; a get changes      *)
(* nothing).                                                               *)
(*                                                                         *)
(* Checked:                                                                *)
(*  - the ring never grows: N places, `next` in 0..N-1 (Bounded);          *)
(*  - a body longer than MX is never stored (Short);                       *)
(*  - at most one body per session (OnePerSession), and it is the latest   *)
(*    put for that session (Latest, a ghost `last` per session), so a get  *)
(*    returns the latest body of a held session, and nothing for one that  *)
(*    is not held (GetLatest);                                             *)
(*  - while the ring has an empty place, `next` is the first empty place   *)
(*    and the places before it are filled; so a session that is not held   *)
(*    never overwrites another while there is room (Room, and RoomRule     *)
(*    on the step);                                                        *)
(*  - the rule of a put (PutRule): a too-long body changes nothing; a      *)
(*    session that is held gets its own place and no other place changes;  *)
(*    a session that is not held takes the place `next` and no other place *)
(*    changes, so a full ring loses exactly the body in the place `next`;  *)
(*    `next` moves on by one, modulo N, exactly when the place written was *)
(*    `next` (the pointer is a round robin over the places, held by what   *)
(*    the code does, and the body it overwrites is the one in that place). *)
(* Witnesses: Reach_dup (a held session also takes `next`: OnePerSession   *)
(* and Latest fail), Reach_newest (a full ring overwrites the place filled *)
(* last: PutRule fails); Reach_lru and Reach_first are what the module     *)
(* doc could be read to promise, "the oldest overwritten first": TLC       *)
(* finds that the code does NOT overwrite the body put longest ago         *)
(* (EvictsLeastRecent), nor the session that entered the ring first        *)
(* (EvictsFirstIn), because a put that refreshes a held session in the     *)
(* place `next` moves the pointer on while one that refreshes any other    *)
(* place does not. Reach_refresh, Reach_evict, Reach_refuse and            *)
(* Reach_atnext are reachability witnesses: a refresh, an eviction, a      *)
(* refused body and a refresh at the place `next` happen.                  *)
(* Lean counterpart: proofs/lean/Vinc/CoreReach*.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences
CONSTANTS N, MX, S, LS, PMAX, DUP, NEWEST
VARIABLES r, last, born, seenT, nextId, act, arg
vars == <<r, last, born, seenT, nextId, act, arg>>

INSTANCE ReachOps

SS == 1..S

Init == /\ r = Reach0(N)
        /\ last = [s \in SS |-> None] /\ born = [s \in SS |-> 0] /\ seenT = [s \in SS |-> 0]
        /\ nextId = 1 /\ act = "init" /\ arg = None

PutStep == \E l \in LS, s \in SS :
    LET b == <<nextId, l>>
    IN /\ r' = RPut(r, N, MX, s, b, DUP, NEWEST)
       /\ nextId' = nextId + 1
       /\ last' = IF l > MX THEN last ELSE [last EXCEPT ![s] = b]
       /\ born' = IF l > MX \/ Has(r.cells, N, s) THEN born ELSE [born EXCEPT ![s] = nextId]
       /\ seenT' = IF l > MX THEN seenT ELSE [seenT EXCEPT ![s] = nextId]
       /\ act' = "put" /\ arg' = <<s, b>>

Next == PutStep
Spec == Init /\ [][Next]_vars
Bound == nextId <= PMAX

C == r.cells
Bounded == /\ DOMAIN C = 0..N - 1 /\ r.next \in 0..N - 1
Short == \A i \in Occ(C, N) : C[i][2][2] <= MX
OnePerSession == \A i, j \in Occ(C, N) : C[i][1] = C[j][1] => i = j
Latest == \A i \in Occ(C, N) : last[C[i][1]] = C[i][2]
Room == \/ Full(C, N)
        \/ \A i \in 0..N - 1 : (C[i] = None) <=> (r.next <= i)
Inv == Bounded /\ Short /\ OnePerSession /\ Latest /\ Room

Same(c1, c2, except) == \A i \in 0..N - 1 : i # except => c1[i] = c2[i]

PutRuleA ==
    act' = "put" =>
        LET s == arg'[1] b == arg'[2]
        IN IF b[2] > MX
           THEN r' = r
           ELSE IF Has(C, N, s)
                THEN LET p == Pos(C, N, s)
                     IN /\ Same(r'.cells, C, p) /\ r'.cells[p] = <<s, b>>
                        /\ r'.next = IF p = r.next THEN (r.next + 1) % N ELSE r.next
                ELSE /\ Same(r'.cells, C, r.next) /\ r'.cells[r.next] = <<s, b>>
                     /\ r'.next = (r.next + 1) % N
GetLatestA == act' = "put" =>
    LET s == arg'[1] b == arg'[2]
    IN IF b[2] > MX THEN RGet(r', N, s) = RGet(r, N, s) ELSE RGet(r', N, s) = b
\* a session that is not held never overwrites another while there is room
RoomRuleA == (act' = "put" /\ arg'[2][2] <= MX /\ ~Has(C, N, arg'[1]) /\ ~Full(C, N)) => C[r.next] = None
PutRule == [][PutRuleA]_vars
GetLatest == [][GetLatestA]_vars
RoomRule == [][RoomRuleA]_vars

\* what "the oldest overwritten first" could mean: the session put longest ago, or the one that entered first
NewHeld == act' = "put" /\ arg'[2][2] <= MX /\ ~Has(C, N, arg'[1]) /\ Full(C, N)
EvictsLeastRecentA == NewHeld => \A i \in 0..N - 1 : seenT[C[r.next][1]] <= seenT[C[i][1]]
EvictsFirstInA == NewHeld => \A i \in 0..N - 1 : born[C[r.next][1]] <= born[C[i][1]]
EvictsLeastRecent == [][EvictsLeastRecentA]_vars
EvictsFirstIn == [][EvictsFirstInA]_vars

\* reachability witnesses
NoRefresh == [][~(act' = "put" /\ arg'[2][2] <= MX /\ Has(C, N, arg'[1]))]_vars
NoEvict == [][~NewHeld]_vars
NoRefuse == [][~(act' = "put" /\ arg'[2][2] > MX)]_vars
NoAtNext == [][~(act' = "put" /\ arg'[2][2] <= MX /\ Has(C, N, arg'[1]) /\ Pos(C, N, arg'[1]) = r.next)]_vars
=============================================================================
