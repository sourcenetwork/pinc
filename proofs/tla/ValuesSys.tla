------------------------------ MODULE ValuesSys ------------------------------
(***************************************************************************)
(* System model of the multi-provider value fetch: vinc-values            *)
(* fetch/{mod,sched,recv,rx,wt,stall}.rs at the granularity of whole       *)
(* groups. Hashing is symbolic and collision free (as in                   *)
(* RangeVerifier.tla): a group hashes to the root exactly when its bytes    *)
(* are the true ones, so a frame carries a kind instead of bytes:          *)
(*   "g" genuine data and a genuine in-band proof and header,              *)
(*   "b" genuine data, but the in-band proof or the header is wrong        *)
(*       (in the order parse: Hash or Protocol eviction; ahead path: the   *)
(*       data still verifies against a good range proof),                  *)
(*   "j" junk data (fails its hash in every path).                         *)
(* The adversary is every provider in Liars (it may send any kind of       *)
(* BadKinds, truncate, send bytes after the last range, send wrong range   *)
(* proofs) and the network (any frame may be delivered in any order: the   *)
(* in-order frame is parsed, the others are held ahead, and with a         *)
(* covering range proof an ahead frame is verified and written at once:    *)
(* WRITE_THROUGH). Loss of an honest provider is delay (the transport      *)
(* repairs it), so loss is the same as reordering here; a provider that    *)
(* never answers is a provider that is not in Fair.                        *)
(*                                                                         *)
(* The scheduling decisions (top-up chunk, steal tail) are nondeterministic *)
(* in the size only, the size being the environment's (the target and the  *)
(* rates), and constrained to what sched.rs guarantees: whole groups, front *)
(* of the queue, never a verified group, a chunk of at least the minimum   *)
(* target (MinChunk), a victim chosen as the code chooses it, a rate victim *)
(* keeping at least one group;                                              *)
(* their arithmetic is ValuesSched, the head-hold and stall timing is      *)
(* ValuesTime. The clock is discrete: ticks since the last progress are     *)
(* saturating counters (IDLE for the steal idleness, SW for the stall      *)
(* wait), and the deadline is a tick count. Delays (redial, restream,      *)
(* steal re-check) are abstracted to "later" under weak fairness.          *)
(*                                                                         *)
(* A call into the machine is atomic: the work it leaves to do (top-ups,   *)
(* check_done, the restream retry) is the queue tasks, and the store write  *)
(* and the commit are two steps pd, so a restart can fall between them.    *)
(* Every external action waits for tasks = <<>> and pd = NONE.             *)
(*                                                                         *)
(* With Mid, the in-order frame of a stream is taken in two events: its   *)
(* header and proof are accepted while the group is not stored (status    *)
(* "mg"), and its bytes complete later ("kg"); another stream may store   *)
(* the group in between (the mid-group race). The completion then finds   *)
(* the group stored and, with DupFix, only accounts for it (no write, no  *)
(* Readable). Not in this model (stated where the report lists them): the  *)
(* range-list capacity widening, PROOF_REQ, and the doubling of the stall *)
(* wait (ValuesTime).                                                      *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, ValuesSysCore

CONSTANTS
    NP,        \* providers 1..NP (at most 4)
    G,         \* groups 0..G-1 of the value
    SPP,       \* streams per provider at once
    Want,      \* wanted groups
    Head0,     \* the group that holds the first requested byte (HEAD_HOLD), in Want if Want is not empty
    InitVer,   \* groups the store has verified at the start
    Listed,    \* the providers the fetch names
    Empty,     \* the value has length 0
    RootOk,    \* the root is the hash of the empty value (only used when Empty)
    Liars,     \* providers that may send bad frames
    Always,    \* providers (in Liars) whose every frame is bad
    BadKinds,  \* subset of {"b", "j"}
    Fair,      \* providers that answer (weak fairness of their steps)
    Faults,    \* budget of benign faults of fair providers: closes, resets, dial failures, refused opens
    CanBusy,   \* the session may refuse to open a stream (against Faults)
    Trunc,     \* a liar may end a stream early
    Extra,     \* a liar may send bytes after the last range
    Ahead,     \* the network may deliver a frame ahead of the in-order one
    Proofs,    \* range proofs exist (a provider may send them)
    StoreFail, \* the store may refuse a write or a commit
    Restarts,  \* restarts of the process allowed
    Mid,       \* a frame's bytes may arrive in two events, and the host may report a session up twice: two streams of a provider can carry one group
    DupFix,    \* TRUE: a group another stream stored while this one was inside it is neither written nor announced again (the code); FALSE: the code before the fix
    OldConn,   \* TRUE: a provider that connects is not topped up (the code before the fix)
    Churn,     \* providers outside Fair may close, vanish and reset streams as often as they like
    OldRetry,  \* TRUE: a retry is dropped while any stream is open (the code before the fix); FALSE: only the provider's own streams count
    HasDl, DeadlineT, \* a deadline exists, and its tick
    MinT,      \* groups of the minimum target (MIN_TARGET_GROUPS = 4 in the code): a top-up takes at least this many
               \* groups from a provider that holds none, half as many from one that holds some; 1 lets a value of a few
               \* groups be striped among the providers, which the real minimum would give to the first one whole
    IDLE, SW, SMIN \* idle ticks before a steal, stall ticks before a redial (0: none), groups a busy victim must hold


Grps == 0..G-1
Provs == 1..NP
Slots == 1..SPP
Kinds(p) == IF p \in Always THEN BadKinds ELSE IF p \in Liars THEN {"g"} \cup BadKinds ELSE {"g"}

ASSUME /\ NP \in 1..4 /\ G \in 0..6 /\ SPP \in 1..4
       /\ Want \subseteq Grps /\ InitVer \subseteq Grps /\ Listed \subseteq Provs
       /\ Liars \subseteq Provs /\ Always \subseteq Liars /\ (Always # {} => BadKinds # {}) /\ Fair \subseteq Provs /\ BadKinds \subseteq {"b", "j"}
       /\ (Want # {} => Head0 \in Want)
       /\ MinT \in 1..4 /\ OldConn \in BOOLEAN /\ OldRetry \in BOOLEAN /\ Churn \in BOOLEAN /\ Faults \in Nat /\ Restarts \in Nat /\ DeadlineT \in Nat /\ HasDl \in BOOLEAN

Min(X) == CHOOSE x \in X : \A y \in X : x <= y
Max(X) == CHOOSE x \in X : \A y \in X : y <= x
Ascending(X) == [i \in 1..Cardinality(X) |-> CHOOSE x \in X : Cardinality({y \in X : y < x}) = i - 1]
FirstK(X, k) == {x \in X : Cardinality({y \in X : y < x}) < k}

VARIABLES S
(* The state, a record:
   run     "idle" | "run" | "done"          fin     NONE or the final event
   nfin    final events emitted             late    events emitted after the final event
   ann     [g -> 0..2] Readable events of g (capped)
   wr      [g -> "none" | "true" | "junk"] the bytes the store holds
   ver     committed (verified) groups, ver0 the verified groups when the fetch started
   reqd    groups asked for since the start, lied the providers that sent bad frames, askedEv: an evicted provider was asked
   queue   the stripe queue                 hd, rel  the held first granule (-1 none) and whether it was released
   inP inA asg conn dial retry up           per provider: in_provs, in_assign, assigned groups, session up,
                                            dial pending, retry timer set, reachable
   lpa     [p -> 0..IDLE] ticks since the provider last made progress or got work
   rx      [p -> [slot -> stream]]          stream = [on, fr |-> [g -> status], pf |-> [g -> 0..2]]
           status: "x" not asked, "u" unsent, "t" never sent, "c" consumed, "n?" in the network, "h?" held (? the kind)
           pf: 0 no range proof, 1 good, 2 bad
   fb      faults left                      rs      restarts left
   now     ticks (only counted with a deadline)    ss  ticks since the last bytes or granule
   lastp   a request was sent (the stall timer is armed)      tw  the steal re-check timer is armed
   tasks   work left in the current call      pd  a verified group between its write and its commit (on, p, s, g, c, step)
   dr      the stream being drained (0 none, 8p+s)      striped  more than one provider
   aheadN  1 once a group was committed from the write-through path; stolen, redialed: a steal / a stall redial happened *)

NoStream == [on |-> FALSE, fr |-> [g \in Grps |-> "x"], pf |-> [g \in Grps |-> 0]]
NoStreams == [s \in Slots |-> NoStream]
NoPd == [on |-> FALSE, p |-> 1, s |-> 1, g |-> 0, ahead |-> FALSE, c |-> "true", step |-> "w"]
Streams(T, p) == {s \in Slots : T.rx[p][s].on}
AllRxNone(T) == \A p \in Provs : \A s \in Slots : ~T.rx[p][s].on
NoOwnStream(T, p) == IF OldRetry THEN AllRxNone(T) ELSE \A s \in Slots : ~T.rx[p][s].on
Pend(st) == {g \in Grps : st.fr[g] \notin {"x", "c"}}
NewStream(need) == [on |-> TRUE, fr |-> [g \in Grps |-> IF g \in need THEN "u" ELSE "x"], pf |-> [g \in Grps |-> 0]]
SlotFree(T, p) == Min(Slots \ Streams(T, p))
IsNet(x) == x \in {"ng", "nb", "nj"}
IsHeld(x) == x \in {"hg", "hb", "hj", "kg"}
KindOf(x) == IF x \in {"ng", "hg", "kg", "mg"} THEN "g" ELSE IF x \in {"nb", "hb"} THEN "b" ELSE "j"
HeldOf(k) == IF k = "g" THEN "hg" ELSE IF k = "b" THEN "hb" ELSE "hj"
NetOf(k) == IF k = "g" THEN "ng" ELSE IF k = "b" THEN "nb" ELSE "nj"

Fresh ==
    [run |-> "idle", fin |-> NONE, nfin |-> 0, late |-> 0, ann |-> [g \in Grps |-> 0],
     wr |-> [g \in Grps |-> IF g \in InitVer THEN "true" ELSE "none"], ver |-> InitVer, ver0 |-> InitVer,
     reqd |-> {}, lied |-> {}, askedEv |-> FALSE, aheadN |-> 0, dupN |-> 0, stolen |-> FALSE, redialed |-> FALSE, queue |-> {}, hd |-> -1, rel |-> FALSE,
     inP |-> [p \in Provs |-> FALSE], inA |-> [p \in Provs |-> FALSE], asg |-> [p \in Provs |-> {}],
     conn |-> [p \in Provs |-> FALSE], dial |-> [p \in Provs |-> FALSE], retry |-> [p \in Provs |-> FALSE],
     up |-> [p \in Provs |-> TRUE], lpa |-> [p \in Provs |-> 0], rx |-> [p \in Provs |-> NoStreams],
     fb |-> Faults, rs |-> Restarts, now |-> 0, ss |-> 0, lastp |-> FALSE, tw |-> FALSE,
     tasks |-> <<>>, pd |-> NoPd, dr |-> 0, striped |-> FALSE]

Init == S = Fresh

(* ---- events and the end ---- *)
Finish(T, f) ==
    [Final(T, f) EXCEPT !.tasks = <<>>, !.pd = NoPd, !.dr = 0, !.rx = [p \in Provs |-> NoStreams]]

(* ---- request (sched.rs request / open_request) ---- *)
ReqOut(T, p, useAsg, only) ==
    IF ~T.conn[p]
    THEN {IF T.dial[p] THEN T ELSE [T EXCEPT !.dial[p] = TRUE, !.askedEv = T.askedEv \/ ~T.inP[p]]}
    ELSE LET need == (IF useAsg THEN T.asg[p] ELSE only) \ T.ver
         IN IF need = {} THEN {T}
            ELSE LET failT == [T EXCEPT !.retry[p] = TRUE]
                 IN IF Cardinality(Streams(T, p)) >= SPP THEN {failT}
                    ELSE {[T EXCEPT !.rx[p][SlotFree(T, p)] = NewStream(need), !.reqd = T.reqd \cup need,
                                    !.askedEv = T.askedEv \/ ~T.inP[p],
                                    !.ss = IF T.lastp THEN T.ss ELSE 0, !.lastp = TRUE]}
                         \cup (IF CanBusy /\ T.fb > 0 THEN {[failT EXCEPT !.fb = T.fb - 1]} ELSE {})

(* the thief takes the stolen tail: assigned, its idle clock restarts, requested *)
ReqOutFor(T, p, tail) ==
    ReqOut([T EXCEPT !.asg[p] = T.asg[p] \cup tail, !.lpa[p] = 0], p, FALSE, tail)

(* ---- steal (sched.rs steal) ---- *)
Miss(T, u) == T.asg[u] \ T.ver
HeadOf(T, v, keep) == FirstK(Miss(T, v), keep)
Rest(T, v, keep) == Miss(T, v) \ FirstK(Miss(T, v), keep)

StealFrom(Tr, p, v, keep) ==
    UNION {(IF Rest(Tr, v, keep) = {} THEN {Tw} ELSE ReqOutFor([Tw EXCEPT !.stolen = TRUE], p, Rest(Tr, v, keep)))
           : Tw \in ReqOut([Tr EXCEPT !.asg[v] = HeadOf(Tr, v, keep), !.rx[v] = NoStreams], v, TRUE, {})}

StealOut(Tr, p) ==
    LET vs == {u \in Provs \ {p} : Tr.inA[u] /\ Miss(Tr, u) # {}}
        idle == {u \in vs : Tr.lpa[u] >= IDLE}
        rate == {u \in vs \ idle : Cardinality(Miss(Tr, u)) >= SMIN}
        from == IF idle # {} THEN {Min(idle)} ELSE rate
        none == IF idle = {} THEN {[Tr EXCEPT !.tw = TRUE]} ELSE {}
        \* an idle victim is robbed of everything (its rate is taken as 0); a slow one keeps any head
        \* a rate victim has a positive rate and at least SMIN groups, so the group-rounded cut keeps one group or more
        keeps(v) == IF v \in idle THEN {0} ELSE 1..Cardinality(Miss(Tr, v))
    IN none \cup UNION {UNION {StealFrom(Tr, p, v, k) : k \in keeps(v)} : v \in from}

(* ---- top-up (sched.rs top_up) ---- *)
TakeChunk(T0, p, out, chunk) ==
    ReqOut([T0 EXCEPT !.queue = {x \in T0.queue : x > Max(chunk)}, !.asg[p] = T0.asg[p] \cup chunk,
                      !.lpa[p] = IF out = 0 THEN 0 ELSE T0.lpa[p]], p, FALSE, chunk)

\* take_chunk gathers want bytes of unverified groups: want is at least two groups when the provider holds work (a
\* top-up returns early from half the target) and at least the four-group minimum target when it holds none, and the
\* loop ends only at want or on an empty queue
MinChunk(out, nq) ==
    LET m == IF out = 0 THEN MinT ELSE (IF MinT \div 2 < 1 THEN 1 ELSE MinT \div 2)
    IN IF nq < m THEN nq ELSE m

TopUpOut(T, p) ==
    IF ~T.striped \/ T.run # "run" \/ ~T.inA[p] THEN {T}
    ELSE LET T0 == [T EXCEPT !.asg[p] = T.asg[p] \ T.ver]
             out == Cardinality(T0.asg[p])
             qv == T0.queue \ T0.ver
         IN IF Cardinality(Streams(T0, p)) >= SPP THEN {T0}
            ELSE (IF out > 0 THEN {T0} ELSE {})
                 \cup (IF qv # {}
                       THEN UNION {TakeChunk(T0, p, out, FirstK(qv, k)) : k \in MinChunk(out, Cardinality(qv))..Cardinality(qv)}
                       ELSE IF out = 0 /\ T0.conn[p] THEN StealOut([T0 EXCEPT !.queue = {}], p)
                            ELSE {[T0 EXCEPT !.queue = {}]})

(* ---- check_done ---- *)
ChkOut(T) ==
    IF T.run # "run" THEN {T}
    ELSE UNION {IF Want \ U.ver = {} THEN {Finish(ReleaseHd(U), "Complete")} ELSE {U}
                : U \in (IF T.hd >= 0 THEN {ReleaseHd(T), T} ELSE {T})}

(* ---- eviction (sched.rs evict) ---- *)
EvictOut(T, p) ==
    LET share == T.asg[p] \ T.ver
        T1 == [T EXCEPT !.rx[p] = NoStreams, !.inP[p] = FALSE, !.inA[p] = FALSE, !.retry[p] = FALSE,
                        !.asg[p] = {}, !.lpa[p] = 0, !.lied = T.lied \cup {p}, !.dr = 0]
        T2 == IF \A q \in Provs : ~T1.inA[q] THEN [T1 EXCEPT !.inA = T1.inP] ELSE T1
        rest == {q \in Provs : T2.inA[q]}
    IN IF rest = {} THEN Finish(T2, "EveryProviderLied")
       ELSE [T2 EXCEPT !.queue = T2.queue \cup share,
                       !.tasks = [i \in 1..Cardinality(rest) |-> <<"top", Ascending(rest)[i]>>]]

(* ---- the call tasks ---- *)
Task ==
    /\ S.tasks # <<>> /\ S.pd.on = FALSE
    /\ LET t == Head(S.tasks)
           T0 == [S EXCEPT !.tasks = Tail(S.tasks)]
       IN \/ /\ t[1] = "top" /\ S' \in TopUpOut(T0, t[2])
          \/ /\ t[1] = "chk" /\ S' \in ChkOut(T0)
          \/ /\ t[1] = "rs"
             /\ S' = IF T0.run = "run" /\ NoOwnStream(T0, t[2]) THEN [T0 EXCEPT !.retry[t[2]] = TRUE] ELSE T0

External == S.run = "run" /\ S.tasks = <<>> /\ ~S.pd.on /\ S.dr = 0

(* ---- start ---- *)
StartBegin(T) ==
    LET need == Want \ T.ver
        n == Cardinality(Listed)
        T1 == [T EXCEPT !.run = "run", !.ver0 = T.ver, !.reqd = {}, !.inP = [p \in Provs |-> p \in Listed],
                        !.striped = n > 1]
    IN IF Empty /\ ~RootOk THEN {Finish(T1, "BadRoot")}
       ELSE IF need = {} THEN {Finish(T1, "Complete")}
       ELSE IF Listed = {} THEN {Finish(T1, "NoProvider")}
       ELSE IF n > 1
            THEN {[T1 EXCEPT !.queue = need, !.inA = [p \in Provs |-> p \in Listed],
                             !.tasks = [i \in 1..n |-> <<"top", Ascending(Listed)[i]>>]]}
            ELSE ReqOut([T1 EXCEPT !.inA[Min(Listed)] = TRUE, !.asg[Min(Listed)] = need], Min(Listed), TRUE, {})

Start == S.run = "idle" /\ S' \in StartBegin(S)

(* ---- the environment: sessions ---- *)
OnDown(T, p, closed) ==
    [T EXCEPT !.dial[p] = FALSE, !.conn[p] = FALSE, !.retry[p] = IF T.inA[p] THEN TRUE ELSE T.retry[p],
              !.rx[p] = IF closed THEN NoStreams ELSE T.rx[p]]

Cost(p) == IF p \in Fair THEN 1 ELSE 0
MayChurn(p) == p \in Fair \/ Churn

DialOkG(p) == External /\ S.inP[p] /\ S.dial[p] /\ S.up[p]

DialOk(p) ==
    /\ DialOkG(p)
    /\ LET T == [S EXCEPT !.dial[p] = FALSE, !.conn[p] = TRUE]
           Up(U) == IF U.inA[p] /\ U.striped /\ ~OldConn THEN [U EXCEPT !.tasks = <<<<"top", p>>>>] ELSE U
       IN S' \in IF T.inA[p] THEN {Up(U) : U \in ReqOut(T, p, TRUE, {})} ELSE {T}

DialFail(p) ==
    /\ External /\ S.inP[p] /\ S.dial[p]
    /\ \/ ~S.up[p] /\ S' = OnDown(S, p, FALSE)
       \/ S.up[p] /\ S.fb >= Cost(p) /\ S' = [OnDown(S, p, FALSE) EXCEPT !.fb = S.fb - Cost(p)]

Close(p) == \* the session of p closes
    /\ External /\ S.inP[p] /\ S.conn[p] /\ S.fb >= Cost(p) /\ MayChurn(p)
    /\ S' = [OnDown(S, p, TRUE) EXCEPT !.fb = S.fb - Cost(p)]

Down(p) == \* p becomes unreachable: its session closes and dials fail until it is back
    /\ External /\ S.up[p] /\ S.fb >= Cost(p) /\ MayChurn(p)
    /\ S' = IF S.inP[p] /\ S.conn[p] THEN [OnDown(S, p, TRUE) EXCEPT !.up[p] = FALSE, !.fb = S.fb - Cost(p)]
            ELSE [S EXCEPT !.up[p] = FALSE, !.fb = S.fb - Cost(p)]

Back(p) == External /\ ~S.up[p] /\ S' = [S EXCEPT !.up[p] = TRUE]

(* ---- try_ahead: the group g of the stream is held, a covering proof is cached, the group is not stored ---- *)
TryAhead(T, p, s, g) ==
    LET st == T.rx[p][s]
    IN IF Proofs /\ st.on /\ IsHeld(st.fr[g]) /\ st.pf[g] # 0 /\ g \notin T.ver
       THEN IF st.pf[g] = 1 /\ KindOf(st.fr[g]) # "j"
            THEN {[T EXCEPT !.pd = [on |-> TRUE, p |-> p, s |-> s, g |-> g, ahead |-> TRUE, c |-> "true", step |-> "w"]]}
            ELSE {EvictOut(T, p)}   \* the proof and the bytes, both from p, do not hash to the root
       ELSE {T}

(* ---- the server side of a stream (the adversary, or an honest provider) ---- *)
SendG(p, s, g) ==
    /\ External /\ S.inP[p] /\ S.conn[p] /\ S.rx[p][s].on
    /\ S.rx[p][s].fr[g] = "u" /\ \A h \in Grps : (h < g /\ S.rx[p][s].fr[h] # "x") => S.rx[p][s].fr[h] # "u"

Send(p, s, g, k) ==
    /\ SendG(p, s, g) /\ k \in Kinds(p)
    /\ S' = [S EXCEPT !.rx[p][s].fr[g] = NetOf(k)]

Truncate(p, s) ==
    /\ External /\ Trunc /\ p \in Liars /\ S.inP[p] /\ S.rx[p][s].on
    /\ \E g \in Grps : S.rx[p][s].fr[g] = "u"
    /\ S' = [S EXCEPT !.rx[p][s].fr = [g \in Grps |-> IF S.rx[p][s].fr[g] = "u" THEN "t" ELSE S.rx[p][s].fr[g]]]

ExtraBytes(p, s) == \* bytes after the last range: a protocol fault
    /\ External /\ Extra /\ p \in Liars /\ S.inP[p] /\ S.rx[p][s].on
    /\ Pend(S.rx[p][s]) = {}
    /\ S' = EvictOut(S, p)

ProofSend(p, s, g, j) == \* a range proof for g (good or wrong), from the provider of the stream
    /\ External /\ Proofs /\ S.inP[p] /\ S.rx[p][s].on /\ S.rx[p][s].fr[g] # "x"
    /\ (j = 1 \/ (p \in Liars /\ j = 2))
    /\ \/ S' \in TryAhead([S EXCEPT !.rx[p][s].pf[g] = j], p, s, g)
       \/ j = 2 /\ S' = EvictOut(S, p)   \* a frame that does not fit the value evicts its provider

EndStream(p, s, cost) ==
    [S EXCEPT !.rx[p][s] = NoStream, !.fb = S.fb - cost,
              !.tasks = <<<<"chk">>>> \o (IF S.striped THEN <<<<"top", p>>>> ELSE <<>>) \o <<<<"rs", p>>>>]

FinishedG(p, s) ==
    /\ External /\ S.inP[p] /\ S.rx[p][s].on
    /\ \A g \in Grps : S.rx[p][s].fr[g] \in {"x", "c", "t"}

Finished(p, s) == \* the peer ended the stream after every byte was consumed
    /\ FinishedG(p, s)
    /\ S' = EndStream(p, s, 0)

ResetBy(p, s) == \* the peer reset the stream
    /\ External /\ S.inP[p] /\ S.conn[p] /\ S.rx[p][s].on /\ S.fb >= Cost(p) /\ MayChurn(p)
    /\ S' = EndStream(p, s, Cost(p))

(* ---- the client side: delivery, parse ---- *)
DeliverG(p, s, g) ==
    /\ External /\ S.inP[p] /\ S.conn[p] /\ S.rx[p][s].on /\ IsNet(S.rx[p][s].fr[g])
    /\ (g = Min(Pend(S.rx[p][s])) \/ Ahead)

Deliver(p, s, g) ==
    /\ DeliverG(p, s, g)
    /\ LET st == S.rx[p][s] IN
       \/ /\ g = Min(Pend(st))
          /\ S' = [S EXCEPT !.rx[p][s].fr[g] = HeldOf(KindOf(st.fr[g])), !.dr = 8 * p + s, !.ss = 0]
       \/ /\ Mid /\ g = Min(Pend(st)) /\ st.fr[g] = "ng" /\ g \notin S.ver
          /\ S' = [S EXCEPT !.rx[p][s].fr[g] = "mg"]
       \/ /\ g # Min(Pend(st))
          /\ S' \in TryAhead([S EXCEPT !.rx[p][s].fr[g] = HeldOf(KindOf(st.fr[g]))], p, s, g)

FinishMid(p, s, g) == \* the rest of the bytes of a frame accepted for verification arrive
    /\ External /\ S.inP[p] /\ S.conn[p] /\ S.rx[p][s].on /\ S.rx[p][s].fr[g] = "mg"
    /\ S' = [S EXCEPT !.rx[p][s].fr[g] = "kg", !.dr = 8 * p + s, !.ss = 0]

Reconnect(p) == \* the host reports a session up that is already up: the missing work is asked for again
    /\ Mid /\ External /\ S.inP[p] /\ S.conn[p] /\ S.inA[p]
    /\ S' \in ReqOut(S, p, TRUE, {})

Drain(p, s) ==
    /\ S.run = "run" /\ S.tasks = <<>> /\ ~S.pd.on /\ S.dr = 8 * p + s
    /\ LET st == S.rx[p][s] IN
       IF st.on /\ Pend(st) # {} /\ IsHeld(st.fr[Min(Pend(st))])
       THEN LET g == Min(Pend(st))
                k == KindOf(st.fr[g])
                T0 == [S EXCEPT !.lastp = TRUE, !.ss = 0]
            IN IF k = "b" THEN S' = EvictOut(T0, p)
               ELSE IF g \in S.ver /\ st.fr[g] # "kg" THEN S' = [T0 EXCEPT !.rx[p][s].fr[g] = "c"]
               ELSE IF g \in S.ver /\ DupFix THEN \* stored by another stream while this one was inside the group: accounted, not announced again
                    S' = [T0 EXCEPT !.rx[p][s].fr[g] = "c", !.dupN = 1, !.lpa[p] = 0,
                                    !.tasks = IF T0.striped THEN <<<<"top", p>>, <<"chk">>>> ELSE <<<<"chk">>>>]
               ELSE IF k = "j" THEN S' = EvictOut(T0, p)
               ELSE S' = [T0 EXCEPT !.rx[p][s].fr[g] = "c",
                                    !.pd = [on |-> TRUE, p |-> p, s |-> s, g |-> g, ahead |-> FALSE, c |-> "true", step |-> "w"]]
       ELSE S' = [S EXCEPT !.dr = 0]

(* write_at then commit: a refusal ends the fetch with Store *)
Write ==
    /\ S.run = "run" /\ S.pd.on /\ S.pd.step = "w" /\ S.tasks = <<>>
    /\ \/ S' = [S EXCEPT !.wr[S.pd.g] = S.pd.c, !.pd.step = "c"]
       \/ StoreFail /\ S' = Finish(S, "Store")

Commit ==
    /\ S.run = "run" /\ S.pd.on /\ S.pd.step = "c" /\ S.tasks = <<>>
    /\ LET d == S.pd
           g == d.g
           T0 == [S EXCEPT !.ver = S.ver \cup {g}, !.pd = NoPd, !.aheadN = IF d.ahead THEN 1 ELSE S.aheadN]
           T1 == IF ~T0.rel /\ g = Head0 THEN [T0 EXCEPT !.hd = g] ELSE Readable(T0, g)
           T2 == [T1 EXCEPT !.lpa[d.p] = 0,
                            !.tasks = IF T1.striped THEN <<<<"top", d.p>>, <<"chk">>>> ELSE <<<<"chk">>>>]
       IN \/ S' = T2
          \/ StoreFail /\ S' = Finish([S EXCEPT !.pd = NoPd], "Store")

(* ---- the timers of the machine ---- *)
Fire(p) == \* a retry is due
    /\ External /\ S.retry[p] /\ S.inP[p]
    /\ LET T == [S EXCEPT !.retry[p] = FALSE]
       IN S' \in IF NoOwnStream(T, p) \/ ~T.conn[p] THEN ReqOut(T, p, TRUE, {}) ELSE {T}

TwFire ==
    /\ External /\ S.striped /\ S.tw
    /\ S' = [S EXCEPT !.tw = FALSE,
                      !.tasks = [i \in 1..Cardinality({q \in Provs : S.inA[q]}) |->
                                    <<"top", Ascending({q \in Provs : S.inA[q]})[i]>>]]

StallRedial == \* nothing for the stall wait since the first request: hang up every session, dial afresh (SW = 0: no stall redial)
    /\ External /\ SW > 0 /\ S.lastp /\ S.ss >= SW
    /\ S' = [S EXCEPT !.ss = 0, !.redialed = TRUE,
                      !.rx = [p \in Provs |-> IF S.inA[p] /\ S.conn[p] THEN NoStreams ELSE S.rx[p]],
                      !.conn = [p \in Provs |-> IF S.inA[p] THEN FALSE ELSE S.conn[p]],
                      !.dial = [p \in Provs |-> IF S.inA[p] THEN TRUE ELSE S.dial[p]]]

Release == \* HEAD_HOLD: the first granule is announced (buffer, granules or timeout: the time is ValuesTime)
    /\ External /\ S.hd >= 0
    /\ S' = ReleaseHd(S)

DeadlineFire ==
    /\ External /\ HasDl /\ S.now > DeadlineT
    /\ S' = Finish(S, "Deadline")

(* An answering provider answers within the stall wait and the idle wait: while one of its steps is possible,
   time does not pass (the assumption that the stall wait outlasts the response time of a provider in Fair). *)
Urgent ==
    \E p \in Fair : \/ DialOkG(p)
                    \/ \E s \in Slots : \/ FinishedG(p, s)
                                        \/ \E g \in Grps : SendG(p, s, g) \/ DeliverG(p, s, g)

Tick ==
    /\ External /\ ~Urgent
    /\ S' = [S EXCEPT !.now = IF HasDl /\ S.now <= DeadlineT THEN S.now + 1 ELSE S.now,
                      !.ss = IF S.ss >= SW THEN SW ELSE S.ss + 1,
                      !.lpa = [p \in Provs |-> IF S.lpa[p] >= IDLE THEN IDLE ELSE S.lpa[p] + 1]]

Restart ==
    /\ S.run # "idle" /\ S.rs > 0
    /\ S' = [Fresh EXCEPT !.wr = S.wr, !.ver = S.ver, !.ver0 = S.ver, !.fb = S.fb, !.rs = S.rs - 1, !.up = S.up]

Next ==
    \/ Start \/ Task \/ Write \/ Commit \/ TwFire \/ StallRedial \/ Release \/ DeadlineFire \/ Tick \/ Restart
    \/ \E p \in Provs :
          \/ Reconnect(p)
          \/ \E s \in Slots, g \in Grps : FinishMid(p, s, g)
          \/ DialOk(p) \/ DialFail(p) \/ Close(p) \/ Down(p) \/ Back(p) \/ Fire(p)
          \/ \E s \in Slots : Drain(p, s) \/ Truncate(p, s) \/ ExtraBytes(p, s) \/ Finished(p, s) \/ ResetBy(p, s)
          \/ \E s \in Slots : \E g \in Grps :
                \/ \E k \in {"g", "b", "j"} : Send(p, s, g, k)
                \/ Deliver(p, s, g)
                \/ \E j \in 1..2 : ProofSend(p, s, g, j)

HonestSteps(p) ==
    DialOk(p) \/ (\E s \in Slots : \E g \in Grps : FinishMid(p, s, g)) \/ (\E s \in Slots : \E g \in Grps : (\E k \in Kinds(p) : Send(p, s, g, k)) \/ Deliver(p, s, g)) \/ (\E s \in Slots : Finished(p, s))

(* Micro-steps of a call (Task, Write, Commit, Drain) are enabled until taken, so weak fairness. The external
   events of the host (a timer that is due, a frame of an answering provider, a provider that comes back) are
   enabled only between calls; they are strongly fair: an event that is possible again and again is processed. *)
Fairness ==
    /\ WF_S(Task) /\ WF_S(Write) /\ WF_S(Commit) /\ WF_S(Start)
    /\ WF_S(\E p \in Provs, s \in Slots : Drain(p, s))
    /\ SF_S(Tick) /\ SF_S(TwFire) /\ SF_S(StallRedial) /\ SF_S(Release) /\ SF_S(DeadlineFire)
    /\ \A p \in Provs : SF_S(Fire(p))
    /\ \A p \in Fair : SF_S(HonestSteps(p)) /\ SF_S(Back(p))

Spec == Init /\ [][Next]_S /\ Fairness
SafeSpec == Init /\ [][Next]_S

(* ---- safety ---- *)
TypeOK ==
    /\ S.run \in {"idle", "run", "done"} /\ S.nfin \in 0..1 /\ S.late \in Nat
    /\ S.ver \subseteq Grps /\ S.queue \subseteq Grps /\ S.fb \in Nat /\ S.rs \in Nat
    /\ \A g \in Grps : S.wr[g] \in {"none", "true", "junk"}

(* 1: every byte in the store and every Readable event is a byte of the true value *)
OnlyVerified == SoundStore(S, Grps) /\ SoundEvents(S, Grps)

(* exactly one final event, none after it *)
OneFinal == OneFinalP(S)

(* a wrong range proof never stays next to a held out-of-order group of its stream: the provider is evicted *)
BadProofEvicts ==
    \A p \in Provs : \A s \in Slots : \A g \in Grps :
        ~(S.rx[p][s].on /\ S.rx[p][s].pf[g] = 2 /\ IsHeld(S.rx[p][s].fr[g]) /\ g # Min(Pend(S.rx[p][s])) /\ g \notin S.ver)

(* a granule is announced once, however the streams race on it *)
AnnOnce == \A g \in Grps : S.ann[g] <= 1

NoEventAfterDone == [][S.run = "done" => (S' = S \/ S'.run = "idle")]_S

VerifiedOnlyGrows == [][S.ver \subseteq S'.ver]_S

(* the reason of a failure is the right one *)
FailReasons == ReasonOk(S, Want, Listed, Empty, RootOk, StoreFail, HasDl, DeadlineT)

(* 3: a liar is evicted and gone; only a provider that sent a bad frame is evicted *)
LiarEvicted ==
    /\ S.lied \subseteq Liars
    /\ \A p \in Listed : (S.run # "idle" /\ ~S.inP[p]) => p \in S.lied
    /\ \A p \in Provs : (S.run = "run" /\ ~S.inP[p]) =>
          (S.asg[p] = {} /\ ~S.inA[p] /\ ~S.retry[p] /\ \A s \in Slots : ~S.rx[p][s].on)
    /\ ~S.askedEv

(* resume: nothing verified at the start is asked for *)
Resume == S.reqd \cap S.ver0 = {}

(* work is conserved: every missing wanted group is queued or assigned to a provider that holds a share, and no
   group has two owners *)
WorkConserved ==
    S.run = "run" =>
        /\ (Want \ S.ver) \subseteq (S.queue \cup UNION {S.asg[p] : p \in {q \in Provs : S.inA[q]}})
        /\ \A p, q \in Provs : p # q => (S.asg[p] \cap S.asg[q]) \subseteq S.ver
        /\ \A p \in Provs : (S.asg[p] \cap S.queue) \subseteq S.ver

(* ---- liveness ---- *)
(* witnesses: each of these is violated by some behaviour, so the outcome is reachable *)
NeverLiedFail == S.fin # "EveryProviderLied"
NeverDeadlineFail == S.fin # "Deadline"
NeverStoreFail == S.fin # "Store"
NeverAheadCommit == S.aheadN = 0
NeverComplete == S.fin # "Complete"
NeverLiarThenComplete == ~(S.fin = "Complete" /\ S.lied # {})
NeverStolen == ~S.stolen
NeverRedialed == ~S.redialed
NeverDup == S.dupN = 0

Terminates == <>(S.run = "done")
Completes == <>(S.fin = "Complete")
CompletesOrDeadline == <>(S.fin \in {"Complete", "Deadline"})

=============================================================================
