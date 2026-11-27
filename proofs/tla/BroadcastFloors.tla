----------------------------- MODULE BroadcastFloors -----------------------------
(***************************************************************************)
(* The replay floors of pinc-broadcast floors.rs, step for step: the       *)
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
(* The FLOOR frame on the wire (floors.rs write and parse_floor), at the   *)
(* token level: one token for the topic length, the timestamp, the        *)
(* history byte, the list marker, the count, an origin key and an entry's *)
(* timestamp. Checked: EncodeParses (the frame of every body a hub writes  *)
(* is taken and re-encodes to itself) and, over every frame of at most    *)
(* WireLen tokens drawn from WireTok, OnFloorStrict (on_floor records a   *)
(* floor only for a frame that re-encodes to the same tokens: a refused   *)
(* frame records nothing). The witness configs put the parsers back that  *)
(* let the bug through: _w_lenient the old one (topic skipped, a list read *)
(* only if it looks like one, trailing tokens ignored), _w_bare one that   *)
(* also takes a frame ending after the history byte, which the encoder    *)
(* never writes. Before the wire was modelled a hub's body reached the    *)
(* member as a value, so no malformed frame could exist in the model.     *)
(*                                                                         *)
(* Lean counterpart: proofs/lean/Pinc/BroadcastFloors.lean (parse_strict,  *)
(* parse_encode).                                                          *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Hubs, Members, Origins, Stamps, TableMax, OriginMax, MaxT, Future, TopFix, Drift, Restarts, Parser, WireTok, WireLen

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

(* ---- the FLOOR frame ---- *)
NO_LIST == 0
LIST == 1
\* the keys of a set in ascending order
RECURSIVE Asc(_)
Asc(S) == IF S = {} THEN <<>> ELSE LET m == CHOOSE x \in S : \A y \in S : x <= y IN <<m>> \o Asc(S \ {m})
\* the entries of a per-origin list, as written: key, timestamp, ascending by key
EntriesOf(l) == LET ks == Asc({o \in DOMAIN l : l[o] # NoT})
                IN [i \in 1..(2 * Len(ks)) |-> IF i % 2 = 1 THEN ks[(i + 1) \div 2] ELSE l[ks[i \div 2]]]
\* SentFloors::write behind an empty topic: topic length 0, the floor, the history byte, then the bare marker or the list
Encode(b) == <<0, b.floor, IF b.hist THEN 1 ELSE 0>>
             \o (IF b.haslist THEN <<LIST, Cardinality({o \in DOMAIN b.list : b.list[o] # NoT})>> \o EntriesOf(b.list)
                 ELSE <<NO_LIST>>)
Refused == [refused |-> TRUE]
Drop(f, n) == IF n >= Len(f) THEN <<>> ELSE SubSeq(f, n + 1, Len(f))
\* ok: es is exactly n entries with keys strictly ascending; l: the list they make
ListOf(n, es) == [ok |-> Len(es) = 2 * n /\ \A i \in 1..(n - 1) : es[2 * i - 1] < es[2 * i + 1],
                  l |-> [k \in {es[2 * i - 1] : i \in 1..Min2(n, Len(es) \div 2)} |->
                           es[2 * (CHOOSE i \in 1..n : es[2 * i - 1] = k)]]]
\* floors.rs parse_floor: a body only for exactly a frame the encoder writes (Parser "bare" also takes a frame that ends
\* after the history byte, the empty tail floors.rs still accepts)
ParseStrict(f) ==
    IF Len(f) < 3 \/ f[1] # 0 \/ f[3] > 1 THEN Refused
    ELSE LET tail == Drop(f, 3)
             b0 == [floor |-> f[2], hist |-> f[3] = 1, list |-> NoT, haslist |-> FALSE]
         IN IF tail = <<NO_LIST>> \/ (Parser = "bare" /\ tail = <<>>) THEN b0
            ELSE IF Len(tail) >= 2 /\ tail[1] = LIST /\ tail[2] <= OriginMax /\ ListOf(tail[2], Drop(tail, 2)).ok
            THEN [b0 EXCEPT !.list = ListOf(tail[2], Drop(tail, 2)).l, !.haslist = TRUE]
            ELSE Refused
\* the old on_floor: the topic skipped whatever it holds, the history byte taken as set only if 1, a list read only if
\* it has at least its count of entries (the first n taken), and every token after it ignored
ParseOld(f) ==
    IF Len(f) < 1 THEN Refused
    ELSE LET rest == Drop(f, 1 + f[1]) IN
         IF Len(f) < 1 + f[1] \/ Len(rest) < 2 THEN Refused
         ELSE LET tail == Drop(rest, 2)
                  b0 == [floor |-> rest[1], hist |-> rest[2] = 1, list |-> NoT, haslist |-> FALSE]
                  n == IF Len(tail) >= 2 THEN tail[2] ELSE 0
                  es == SubSeq(tail, 3, 2 + 2 * n)
              IN IF Len(tail) >= 2 /\ tail[1] = LIST /\ Len(tail) - 2 >= 2 * n
                 THEN [b0 EXCEPT !.list = [k \in {es[2 * i - 1] : i \in 1..n} |->
                                             es[2 * (CHOOSE i \in 1..n : es[2 * i - 1] = k)]], !.haslist = TRUE]
                 ELSE b0
Parse(f) == IF Parser = "old" THEN ParseOld(f) ELSE ParseStrict(f)
\* on_floor: the body recorded for a hub (Refused: nothing is recorded, the gathering still waits for the hub)
OnFloor(f) == Parse(f)
Frames == UNION {[1..n -> WireTok] : n \in 0..WireLen}

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
\* the frame of every body a hub writes is taken, and what is taken re-encodes to it
EncodeParses == \A h \in Hubs, p \in Members : LET f == Encode(Body(hs[h], p, hs[h].born)) IN
                    OnFloor(f) # Refused /\ Encode(OnFloor(f)) = f
\* on_floor records a floor only for a frame that re-encodes to the same tokens
\* (t >= 0: a state-level formula, so TLC reports a violation as one; a constant formula is reported otherwise)
OnFloorStrict == t >= 0 /\ \A f \in Frames : OnFloor(f) # Refused => Encode(OnFloor(f)) = f
ConservativeOverflow == \A h \in Hubs, p \in Members : (hs[h].msOver /\ nrest = 0 /\ TakenMax(h, p) # NoT) =>
    Body(hs[h], p, hs[h].born).floor >= TakenMax(h, p)
=============================================================================
