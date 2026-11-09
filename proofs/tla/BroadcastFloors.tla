----------------------------- MODULE BroadcastFloors -----------------------------
(***************************************************************************)
(* The replay floors of vinc-broadcast floors.rs, step for step: the       *)
(* SentFloors a hub keeps (note, write) with its table caps and overflow   *)
(* flags, and what a restarted member does with the FLOOR bodies of every  *)
(* hub (on_floor, floor_settle, is_old).                                   *)
(*                                                                         *)
(* A hub takes messages (a session accepted the frame) and notes, per      *)
(* member it sent to, the timestamp and the origin. A member that restarts *)
(* gathers one FLOOR body from each hub and settles. The environment       *)
(* takes any message at any time for any subset of the members, restarts a *)
(* hub (it forgets what it sent; its floor is then its start time), and    *)
(* settles the member at any time.                                         *)
(*                                                                         *)
(* Timestamps are totally ordered numbers; a message is stamped no later   *)
(* than the clock of the hub that takes it, unless Future is set (an       *)
(* origin whose clock runs ahead; a hub does not follow a clock more than  *)
(* the drift ahead of its own).                                            *)
(*                                                                         *)
(* Checked: FloorsSound (after the settle, every message a hub took for    *)
(* the member is judged old, so nothing a session took is redelivered      *)
(* after a restart); FloorOnlyTaken (a floor advances only for a message a *)
(* session took, and is exactly the newest one); Caps (the tables stay     *)
(* within TableMax members and OriginMax origins per member); BareMarker   *)
(* (past the cap the body carries no list, and the member then judges by   *)
(* the overall floor, which covers every message taken); ListWithin;       *)
(* ConservativeOverflow (a full table reports a floor not below any        *)
(* timestamp it took: TopFix). Without TopFix the _top config finds the    *)
(* message a skewed origin stamped ahead of the hub clock, which the       *)
(* floor `present` of a full table does not cover. The _future config      *)
(* shows the residual that holds with TopFix: a restarted hub's floor is   *)
(* its start time, so a message stamped ahead of it is not covered.        *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Vinc/BroadcastFloors.lean.                *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Hubs, Members, Origins, Stamps, TableMax, OriginMax, MaxT, Future, TopFix, Drift, Restarts

NoT == -1
VARIABLES t, hs, taken, nrest
vars == <<t, hs, taken, nrest>>

Max2(a, b) == IF a >= b THEN a ELSE b
Min2(a, b) == IF a <= b THEN a ELSE b

HubInit(born) == [born |-> born, hlc |-> born, maxsent |-> [p \in Members |-> NoT], msOver |-> FALSE,
                  osent |-> [p \in Members |-> [o \in Origins |-> NoT]], opeers |-> {}, oOver |-> FALSE, top |-> NoT]

Init == t = 0 /\ hs = [h \in Hubs |-> HubInit(0)] /\ taken = [h \in Hubs |-> [p \in Members |-> [o \in Origins |-> NoT]]] /\ nrest = 0

\* floors.rs SentFloors::note
Note(S, p, ts, origin) ==
    LET d == S.osent[p]
        cnt == Cardinality({o \in Origins : d[o] # NoT})
        S1 == IF S.oOver THEN S
              ELSE IF p \notin S.opeers /\ Cardinality(S.opeers) >= TableMax THEN [S EXCEPT !.oOver = TRUE]
              ELSE IF d[origin] # NoT \/ cnt < OriginMax
                   THEN [S EXCEPT !.opeers = @ \union {p}, !.osent[p][origin] = IF d[origin] = NoT THEN ts ELSE Max2(d[origin], ts)]
                   ELSE [S EXCEPT !.opeers = @ \union {p}, !.oOver = TRUE]
        known == S.maxsent[p] # NoT
        mscount == Cardinality({q \in Members : S.maxsent[q] # NoT})
        S2 == IF known \/ mscount < TableMax
              THEN [S1 EXCEPT !.maxsent[p] = IF known THEN Max2(@, ts) ELSE ts]
              ELSE [S1 EXCEPT !.msOver = TRUE]
    IN [S2 EXCEPT !.top = Max2(@, ts)]

\* floors.rs SentFloors::write: the FLOOR body for peer p
Body(S, p, born) ==
    LET known == S.maxsent[p] # NoT
        present == IF TopFix THEN Max2(S.hlc, S.top) ELSE S.hlc
        floor == IF S.msOver THEN present ELSE Max2(IF known THEN S.maxsent[p] ELSE 0, born)
        lst == IF S.oOver \/ S.msOver THEN NoT ELSE S.osent[p]
    IN [floor |-> floor, hist |-> S.msOver \/ known, list |-> lst, haslist |-> ~(S.oOver \/ S.msOver)]

\* floors.rs on_floor and floor_settle over the bodies of every hub
Settle(bodies) ==
    LET f == CHOOSE x \in {bodies[h].floor : h \in Hubs} : \A y \in {bodies[h].floor : h \in Hubs} : x >= y
        fhist == \E h \in Hubs : bodies[h].hist
        allList == \A h \in Hubs : bodies[h].haslist
        merged == [o \in Origins |-> LET vs == {bodies[h].list[o] : h \in Hubs}
                                     IN CHOOSE x \in vs : \A y \in vs : x >= y]
    IN [rfloor |-> IF fhist THEN f ELSE NoT, ofloor |-> IF allList THEN merged ELSE NoT, hasOf |-> allList, nohist |-> ~fhist]

\* floors.rs is_old, once the floors are settled (the local clock rule applies only if neither floor nor nohist holds)
IsOld(F, origin, ts) ==
    IF F.hasOf THEN F.ofloor[origin] # NoT /\ ts <= F.ofloor[origin]
    ELSE IF F.rfloor # NoT /\ ts <= F.rfloor THEN TRUE
    ELSE FALSE

Floors(M) == Settle([h \in Hubs |-> Body(hs[h], M, hs[h].born)])

(* ---- environment ---- *)
\* a hub takes a message of `origin` stamped `ts` for member p: it follows the stamp unless it is too far ahead
\* (observe), then notes it
Take == \E h \in Hubs, p \in Members, o \in Origins, ts \in Stamps :
    /\ (Future \/ ts <= t)
    /\ LET obs == IF ts <= t + Drift THEN Max2(hs[h].hlc, ts) ELSE hs[h].hlc
           S0 == [hs[h] EXCEPT !.hlc = obs]
       IN /\ hs' = [hs EXCEPT ![h] = Note(S0, p, ts, o)]
          /\ taken' = [taken EXCEPT ![h][p][o] = Max2(@, ts)]
    /\ UNCHANGED <<t, nrest>>

\* a hub restarts: it forgets what it sent and its floor becomes its start time
HubRestart == /\ nrest < Restarts
              /\ \E h \in Hubs : hs' = [hs EXCEPT ![h] = HubInit(t)]
              /\ nrest' = nrest + 1 /\ UNCHANGED <<t, taken>>

Tick == t < MaxT /\ t' = t + 1 /\ UNCHANGED <<hs, taken, nrest>>

Next == Take \/ HubRestart \/ Tick
Spec == Init /\ [][Next]_vars

(* ---------------------------- the checked properties ---------------------------- *)
TypeOK == \A h \in Hubs : Cardinality(hs[h].opeers) <= TableMax

\* the newest message of an origin taken for a member (the oldest ones follow by the order of timestamps)
\* every message a hub took for the member is old for the member once it settles the floors of every hub
FloorsSound == \A h \in Hubs, p \in Members, o \in Origins : taken[h][p][o] # NoT => IsOld(Floors(p), o, taken[h][p][o])

TakenMax(h, p) == LET vs == {taken[h][p][o] : o \in Origins} IN CHOOSE x \in vs : \A y \in vs : x >= y

\* an exact floor: the newest message taken for the member by the hub, when the table did not overflow
FloorOnlyTaken == \A h \in Hubs, p \in Members :
    (~hs[h].msOver /\ hs[h].maxsent[p] # NoT /\ nrest = 0) => hs[h].maxsent[p] = TakenMax(h, p)
FloorExact == \A h \in Hubs, p \in Members :
    (nrest = 0 /\ TakenMax(h, p) # NoT) => hs[h].maxsent[p] # NoT \/ hs[h].msOver

Caps == \A h \in Hubs : /\ Cardinality({p \in Members : hs[h].maxsent[p] # NoT}) <= TableMax
                         /\ \A p \in Members : Cardinality({o \in Origins : hs[h].osent[p][o] # NoT}) <= OriginMax

BareMarker == \A h \in Hubs, p \in Members : (hs[h].oOver \/ hs[h].msOver) => ~Body(hs[h], p, hs[h].born).haslist
ListWithin == \A h \in Hubs, p \in Members : Body(hs[h], p, hs[h].born).haslist =>
                  Cardinality({o \in Origins : Body(hs[h], p, hs[h].born).list[o] # NoT}) <= OriginMax
ConservativeOverflow == \A h \in Hubs, p \in Members : (hs[h].msOver /\ nrest = 0 /\ TakenMax(h, p) # NoT) =>
    Body(hs[h], p, hs[h].born).floor >= TakenMax(h, p)
=============================================================================
