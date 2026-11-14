------------------------------ MODULE ConnectOwn ------------------------------
(***************************************************************************)
(* Model check of the node's own record and address discovery, over the    *)
(* operators of ConnectOwnOps.tla. The steps are set_local, a round of     *)
(* probes, an answer (from any address, with any nonce), a restart of the  *)
(* probe state, a tick with a wall clock, and the signing of the record    *)
(* (record_job). The wall clock is the host's: with Strict it rises by at  *)
(* least a millisecond between ticks, without it it may repeat or step     *)
(* back (a clock that was set back).                                       *)
(*                                                                         *)
(* Properties (Lean: Vinc/ConnectOwnThm.lean):                             *)
(*  CandCap      the record lists at most cap addresses (MAX_ADDRS)        *)
(*  CandPrefix   the distinct reflexive addresses come first, in relay     *)
(*               order                                                     *)
(*  CandLocal    after them come the node's own addresses, in order, each  *)
(*               once and none that is already listed; all of them when    *)
(*               there is room                                             *)
(*  CandOnly     nothing else is listed                                    *)
(*  CandDistinct every address is listed once, one that several relays     *)
(*               report included                                           *)
(*  Observed     a reflexive address enters only from the configured       *)
(*               address of a relay, for the nonce of that relay's         *)
(*               outstanding probe, and only once per probe; an answer     *)
(*               that is not taken changes nothing                         *)
(*  Seq          the record's sequence number is the wall clock of the     *)
(*               last tick; it is strictly above the previous record's     *)
(*               exactly when the clock rose (SeqAbove holds with Strict   *)
(*               and fails without it: the code keeps nothing across a     *)
(*               restart, so a restart is the same as a tick)              *)
(* Witnesses (BUG, a rule that is not the code's; TLC must violate the     *)
(* property): "dup" lists the node's own addresses without leaving out     *)
(* those already listed (CandLocal); "refldup" is the rule the code had    *)
(* before an address several relays report was listed once: one entry per *)
(* relay that reported it (CandDistinct); "nocap" ignores the cap          *)
(* (CandCap); "anyfrom" and "anynonce" take an answer from any address or  *)
(* for any nonce (Observed).                                               *)
(***************************************************************************)
EXTENDS ConnectOwnOps, TLC

CONSTANTS Addrs, Relays, U1, U2, Nonces, Walls, Cap, MaxCalls, Strict, Spaced, BUG

Udps == <<U1, U2>>
cf == [cap |-> Cap, udp |-> Udps]

VARIABLES S, job, obs, calls
vars == <<S, job, obs, calls>>

NoJob == [seq |-> 0, home |-> 0, reach |-> 0, addrs |-> <<>>, hints |-> 0, rl |-> <<>>, loc |-> <<>>, prev |-> 0, made |-> FALSE]
NoObs == [from |-> 0, nonce |-> 0, took |-> FALSE, k |-> 0, probe |-> 0, at |-> 0]
Ob(f, n, t, k, p) == [from |-> f, nonce |-> n, took |-> t, k |-> k, probe |-> p, at |-> calls + 1]

Init == S = NewNode(cf) /\ job = NoJob /\ obs = NoObs /\ calls = 0

RECURSIVE SeqsUpTo(_)
SeqsUpTo(n) == IF n = 0 THEN {<<>>} ELSE SeqsUpTo(n - 1) \cup {Append(s, a) : s \in SeqsUpTo(n - 1), a \in Addrs}

(* the wrong rules of the witnesses *)
CandsB ==
    IF BUG = "dup" THEN
        LET r0 == ReflList(cf, S)
            F[i \in 0..Len(S.local)] == IF i = 0 THEN r0 ELSE IF Len(F[i - 1]) < Cap THEN Append(F[i - 1], S.local[i]) ELSE F[i - 1]
        IN F[Len(S.local)]
    ELSE IF BUG = "nocap" THEN
        LET r0 == ReflList(cf, S)
            F[i \in 0..Len(S.local)] == IF i = 0 THEN r0 ELSE IF ~InSeq(F[i - 1], S.local[i]) THEN Append(F[i - 1], S.local[i]) ELSE F[i - 1]
        IN F[Len(S.local)]
    ELSE IF BUG = "refldup" THEN
        LET R[k \in 0..Len(S.refl)] == IF k = 0 THEN <<>> ELSE IF S.refl[k] # 0 THEN Append(R[k - 1], S.refl[k]) ELSE R[k - 1]
            r0 == SubSeq(R[Len(S.refl)], 1, Min(Len(R[Len(S.refl)]), Cap))
            F[i \in 0..Len(S.local)] == IF i = 0 THEN r0
                ELSE IF Len(F[i - 1]) < Cap /\ ~InSeq(F[i - 1], S.local[i]) THEN Append(F[i - 1], S.local[i]) ELSE F[i - 1]
        IN F[Len(S.local)]
    ELSE Cands(cf, S)

DoLocal == \E a \in SeqsUpTo(Cap + 1) : /\ S' = SetLocal(cf, S, a) /\ UNCHANGED <<job, obs>>
DoProbe == \E n1 \in Nonces, n2 \in Nonces : LET ns == <<n1, n2>> IN /\ S' = ProbeAll(cf, S, ns) /\ UNCHANGED <<job, obs>>
DoRestart == /\ S' = Restart(S) /\ UNCHANGED <<job, obs>>

DoAnswer == \E from \in {U1, U2, 99}, n \in Nonces, a \in Addrs :
    LET o == Observe(cf, S, from, n, a)
        k == RelayAt(cf, from)
        anyfrom == BUG = "anyfrom" /\ k = 0
        anyn == BUG = "anynonce" /\ k # 0 /\ S.probe[k] # 0 /\ S.probe[k] # n
    IN /\ \/ anyfrom /\ S' = [S EXCEPT !.refl[1] = a] /\ obs' = Ob(from, n, TRUE, 1, 0)
          \/ anyn /\ S' = [S EXCEPT !.refl[k] = a, !.probe[k] = 0] /\ obs' = Ob(from, n, TRUE, k, S.probe[k])
          \/ ~anyfrom /\ ~anyn /\ S' = o.S
             /\ obs' = Ob(from, n, o.took, k, IF k = 0 THEN 0 ELSE S.probe[k])
       /\ UNCHANGED job

DoTick == \E w \in Walls : /\ (Strict => w > S.wall) /\ S' = Tick(S, w) /\ UNCHANGED <<job, obs>>

DoJob == \E home \in Relays, class \in 1..2, h \in 0..1 :
    /\ S.wall # 0
    /\ (Spaced => S.wall > job.seq)
    /\ LET j == RecordJob(cf, S, home, class, h) IN
       job' = [seq |-> j.seq, home |-> j.home, reach |-> j.reach, addrs |-> CandsB, hints |-> j.hints,
               rl |-> ReflList(cf, S), loc |-> S.local, prev |-> job.seq, made |-> TRUE]
    /\ UNCHANGED <<S, obs>>

Next == /\ calls < MaxCalls /\ calls' = calls + 1
        /\ (DoLocal \/ DoProbe \/ DoRestart \/ DoAnswer \/ DoTick \/ DoJob)

Spec == Init /\ [][Next]_vars

Dist(s) == \A i, j \in 1..Len(s) : i # j => s[i] # s[j]
Rest(s, n) == SubSeq(s, n + 1, Len(s))
SetOf(s) == {s[i] : i \in 1..Len(s)}

CandCap == job.made => Len(job.addrs) <= Cap
CandPrefix == job.made => SubSeq(job.addrs, 1, Len(job.rl)) = job.rl
CandLocal == job.made =>
    LET t == Rest(job.addrs, Len(job.rl)) IN
    /\ Dist(t)
    /\ \A i \in 1..Len(t) : ~InSeq(job.rl, t[i]) /\ InSeq(job.loc, t[i])
    /\ (Len(job.addrs) < Cap => \A i \in 1..Len(job.loc) : InSeq(job.addrs, job.loc[i]))
CandOnly == job.made => SetOf(job.addrs) \subseteq SetOf(job.rl) \cup SetOf(job.loc)
CandDistinct == job.made => Dist(job.addrs)
SeqIsWall == job.made => job.seq # 0
SeqAbove == job.made => job.seq > job.prev

Observed == [][obs'.at = calls' =>
                 /\ (obs'.took => /\ obs'.k # 0 /\ Udps[obs'.k] = obs'.from /\ obs'.probe # 0 /\ obs'.probe = obs'.nonce
                                  /\ S'.probe[obs'.k] = 0 /\ S'.refl[obs'.k] # 0)
                 /\ (~obs'.took => S' = S)]_vars
\* what is taken changes only that relay's entries
OnlyThatRelay == [][(obs'.at = calls' /\ obs'.took) =>
                      \A k \in 1..Len(S.refl) : k # obs'.k => S'.refl[k] = S.refl[k] /\ S'.probe[k] = S.probe[k]]_vars

\* reachability
NotTook == ~obs.took
NotRefused == ~(obs.k # 0 /\ ~obs.took)
NotFull == ~(job.made /\ Len(job.addrs) = Cap)
NotDedup == ~(job.made /\ \E i \in 1..Len(job.loc) : InSeq(job.rl, job.loc[i]))
=============================================================================
