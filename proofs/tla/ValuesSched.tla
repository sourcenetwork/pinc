------------------------------ MODULE ValuesSched ------------------------------
(***************************************************************************)
(* Model of the work scheduler of pinc-values (fetch/sched.rs, the start    *)
(* of fetch/mod.rs and the finish of fetch/recv.rs) on the span lists of    *)
(* span.rs: the stripe queue, every provider's assigned list, the store's   *)
(* verified set, with the code's own steps: start (align of the wanted      *)
(* ranges, push_new, `missing`, the first providers, NoProvider/Complete,   *)
(* the one-share split of a single provider, resume), top_up (retain,       *)
(* target, TAIL_SHRINK, take_chunk, the steal when idle), steal (victim by  *)
(* eta with the two idle corrections, keep rounded to a group, head/tail    *)
(* cut), evict (LIAR_EVICT: the share goes back to the queue front, the     *)
(* provider leaves, all providers evicted => Failed(EveryProviderLied)),    *)
(* verification of a group and the pass of time.                            *)
(*                                                                         *)
(* The environment is nondeterministic where the code reads the clock or    *)
(* the network: the outstanding target of a top-up is any of TGTS, the rate *)
(* of a provider that has verified a group is RATES[p], time is the age of  *)
(* a provider's last verified group or hand-over in steps of STEAL_IDLE/1   *)
(* (0, 1, 2 = idle). Providers in SILENT never verify, in LIARS are         *)
(* evicted.                                                                 *)
(*                                                                         *)
(* Checked (TLC, all behaviours of the bounded model):                      *)
(*  Cover     every wanted group the store has not verified is in the queue *)
(*            or in the list of a provider that holds a share, whatever     *)
(*            widened (property 2, "never skips");                          *)
(*  Exact     with room for every list (no push is ever on a full list; a   *)
(*            configuration where it is proved by Room) every wanted group  *)
(*            is held exactly once, and none outside the wanted set: the    *)
(*            bytes are partitioned among queue, lists and the verified set *)
(*            (conservation across top_up, TAIL_SHRINK, steal, evict, and  *)
(*            resume: no verified byte is ever queued);                     *)
(*  Sized     lists within capacity, spans aligned to groups;               *)
(*  Evicted   an evicted provider holds nothing, is no candidate, and is    *)
(*            never given work again;                                       *)
(*  StealOk   no steal from itself; the thief held nothing; the bytes moved *)
(*            equal the tail's total and the head and tail partition the   *)
(*            victim's list; the victim was idle or its eta reached 800 ms; *)
(*  Termination  the measure (unverified wanted groups, active providers,   *)
(*            queue size) never rises: PhiLe;                               *)
(*  Done      Complete only with every wanted group verified; the liar end  *)
(*            only with no holder left.                                     *)
(* Lean counterpart: Pinc/ValuesSchedCover.lean (reach_cover), Evict.lean,  *)
(* Term.lean, Steal.lean; the exact accounting of the primitives is         *)
(* ValuesSchedList.lean / ValuesSchedHoles.lean.                            *)
(***************************************************************************)
EXTENDS ValuesSchedSpans, TLC

CONSTANTS NP, NG, SHORT, QN, AN, WN, WANTS, INITV, TGTS, RATES, LIARS, SILENT, NPROVS, CORRECTION, TRACK

L == NG * G - SHORT

(* the concrete parameter sets of the configurations *)
WantsA == {<<>>, <<[off |-> G + 5, len |-> 1]>>,
           <<[off |-> 3 * G, len |-> G], [off |-> 0, len |-> G + 1], [off |-> G, len |-> 0]>>,
           <<[off |-> 2 * G, len |-> G], [off |-> 2 * G + 7, len |-> G]>>}
WantsWhole == {<<>>}
InitvA == {{}, {0}, {1, 2}, {0, 3}}
InitvNone == {{}}
RatesA == [p \in 1 .. 3 |-> CASE p = 1 -> 2000 [] p = 2 -> 100 [] p = 3 -> 500]
TgtsA == {MINT, 6 * G}
TgtsMin == {MINT}
WantsMix == {<<[off |-> G + 5, len |-> 1], [off |-> 2 * G, len |-> 2 * G]>>}
WantsOver == {<<[off |-> 2 * G, len |-> G], [off |-> 2 * G + 7, len |-> G]>>}
InitvOne == {{}, {1}}
InitvTwo == {{0}, {1, 2}}
Provs == 1 .. NP
Groups == 0 .. (NG - 1)

(* ---- the store: the verified set is a set of groups; verified_from is the first run ending after c ---- *)
RunEnd(V, a) == CHOOSE b \in (a + 1) .. NG : b \notin V /\ (\A x \in a .. (b - 1) : x \in V)
GroupRuns(V) == {<<a, RunEnd(V, a)>> : a \in {x \in V : (x - 1) \notin V}}
VFg(V, c) ==
    LET cand == {r \in GroupRuns(V) : Min(r[2] * G, L) > c}
    IN IF cand = {} THEN NONE
       ELSE LET r == CHOOSE r \in cand : \A q \in cand : r[2] <= q[2]
            IN [start |-> r[1] * G, end |-> Min(r[2] * G, L)]
HolesV(V, s) == HolesOf(LAMBDA c : VFg(V, c), s)
RetainV(c, V, l) == Retain(c, LAMBDA x : VFg(V, x), l)

(* ---- the groups a list covers (its spans are aligned: Aligned) ---- *)
InSpan(s, g) == s.off <= g * G /\ g * G < End(s)
GCov(l) == {g \in Groups : \E k \in 1 .. Len(l) : InSpan(l[k], g)}
GMult(l, g) == Cardinality({k \in 1 .. Len(l) : InSpan(l[k], g)})

(* ---- take_chunk ---- *)
GFloor(n) == LET g == (n \div G) * G IN IF g = 0 THEN G ELSE g

RECURSIVE TC(_, _, _, _, _)
TC(V, size, got, qq, out) ==
    IF got >= size \/ qq = <<>> THEN [q |-> qq, out |-> out]
    ELSE LET s == Head(qq)
             rest == Tail(qq)
             room == size - got
             take == IF s.len <= room THEN s.len ELSE Min(GFloor(room), s.len)
             q1 == IF take < s.len THEN PushFrontC(QN, rest, [off |-> s.off + take, len |-> s.len - take]) ELSE rest
             hs == HolesV(V, [off |-> s.off, len |-> take])
         IN TC(V, size, got + TotalL(hs), q1, ExtendC(AN, out, hs))

(* ---- the cut of a steal: bytes passed, head and tail built so far ---- *)
RECURSIVE SS(_, _, _, _, _)
SS(keep, acc, l, head, tail) ==
    IF l = <<>> THEN [head |-> head, tail |-> tail]
    ELSE LET s == Head(l)
         IN IF acc >= keep THEN SS(keep, acc + s.len, Tail(l), head, PushC(AN, tail, s))
            ELSE IF acc + s.len <= keep THEN SS(keep, acc + s.len, Tail(l), PushC(AN, head, s), tail)
            ELSE SS(keep, acc + s.len, Tail(l), PushC(AN, head, [off |-> s.off, len |-> keep - acc]),
                    PushC(AN, tail, [off |-> s.off + keep - acc, len |-> s.len - (keep - acc)]))

(* ---- the share of an evicted provider returns to the queue front, in order ---- *)
RECURSIVE RetQ(_, _)
RetQ(qq, m) == IF m = <<>> THEN qq ELSE RetQ(PushFrontC(QN, qq, m[Len(m)]), SubSeq(m, 1, Len(m) - 1))

VARIABLES q, a, V, act, known, age, since, st, fail, W, striped, last
vars == <<q, a, V, act, known, age, since, st, fail, W, striped, last>>

NoLast == [kind |-> "none"]

Init ==
    /\ q = <<>> /\ a = [p \in Provs |-> <<>>] /\ V = {} /\ act = {} /\ known = [p \in Provs |-> FALSE]
    /\ age = [p \in Provs |-> 0] /\ since = [p \in Provs |-> 2] /\ st = "idle" /\ fail = "none" /\ W = {}
    /\ striped = FALSE /\ last = NoLast

(* ---- start: align, push_new, missing, providers, begin ---- *)
RECURSIVE WantLoop(_, _)
WantLoop(w, asked) ==
    IF asked = <<>> THEN w
    ELSE LET al == AlignG(G, Head(asked), L)
         IN WantLoop(IF al = NONE THEN w ELSE PushNewC(WN, w, al), Tail(asked))

Start(want, v0, np) ==
    LET asked == IF want = <<>> THEN <<[off |-> 0, len |-> L]>> ELSE want
        wl == WantLoop(<<>>, asked)
        wset == {g \in Groups : \E k \in 1 .. Len(wl) : InSpan(wl[k], g)}
        need == Retain(WN, LAMBDA x : VFg(v0, x), wl)
        strp == np > 1
    IN /\ st = "idle"
       /\ W' = wset /\ V' = v0
       /\ IF need = <<>>
          THEN /\ st' = "done" /\ fail' = "none" /\ act' = {} /\ q' = <<>> /\ a' = a /\ striped' = FALSE
          ELSE IF np = 0
               THEN /\ st' = "done" /\ fail' = "noprov" /\ act' = {} /\ q' = <<>> /\ a' = a /\ striped' = FALSE
               ELSE /\ st' = "running" /\ fail' = "none" /\ act' = 1 .. np /\ striped' = strp
                    /\ q' = IF strp THEN ExtendC(QN, <<>>, need) ELSE <<>>
                    /\ a' = [p \in Provs |-> IF ~strp /\ p = 1
                                              THEN ExtendC(AN, <<>>, SplitG(G, AN, need, 4, 1)[0]) ELSE <<>>]
       /\ UNCHANGED <<known, age, since>>
       /\ last' = [kind |-> "start", need |-> need, v0 |-> v0]

(* ---- the choice of a victim (Ops.EtaOf with the idle clock, then the greatest eta, lowest slot) ---- *)
Rate(p) == IF known[p] THEN RATES[p] ELSE 0
EtaP(a1, j) == EtaOf(age[j] >= 2, TotalL(a1[j]), Rate(j))
CandP(a1, p, j) == j \in act /\ j # p /\ EtaP(a1, j) >= ETAMS
BestP(a1, p, j) == CandP(a1, p, j) /\ \A c \in Provs : CandP(a1, p, c) =>
                      (EtaP(a1, c) < EtaP(a1, j) \/ (EtaP(a1, c) = EtaP(a1, j) /\ c >= j))

(* ---- top_up(p) with target tgt ---- *)
TopUp(p, tgt) ==
    LET ap == RetainV(AN, V, a[p])
        out == TotalL(ap)
        k == Cardinality(act)
        want == TailWant(tgt - out, k, TotalL(q))
        tcr == IF q = <<>> THEN [q |-> q, out |-> <<>>] ELSE TC(V, want, 0, q, <<>>)
        doSteal == tcr.out = <<>> /\ out = 0
        a1 == [j \in Provs |-> IF j = p THEN ap ELSE IF j \in act THEN RetainV(AN, V, a[j]) ELSE a[j]]
        hasV == \E j \in Provs : BestP(a1, p, j)
        v == IF hasV THEN CHOOSE j \in Provs : BestP(a1, p, j) ELSE 0
        m == IF hasV THEN TotalL(a1[v]) ELSE 0
        rqv == IF hasV /\ EtaP(a1, v) < STALLED THEN Rate(v) ELSE 0
        keep == KeepOf(m, rqv, Rate(p))
        sp == IF hasV THEN SS(keep, 0, a1[v], <<>>, <<>>) ELSE [head |-> <<>>, tail |-> <<>>]
    IN /\ st = "running" /\ striped /\ p \in act
       /\ IF out >= tgt \div 2
          THEN \* the early return still prunes the provider's list
               /\ a' = [a EXCEPT ![p] = ap] /\ UNCHANGED <<q, age, since>> /\ last' = [kind |-> "prune"]
          ELSE IF doSteal
               THEN IF hasV
                    THEN LET a2 == [a1 EXCEPT ![v] = ExtendC(AN, <<>>, sp.head)]
                         IN /\ a' = IF sp.tail = <<>> THEN a2 ELSE [a2 EXCEPT ![p] = ExtendC(AN, a2[p], sp.tail)]
                            /\ q' = tcr.q
                            /\ age' = IF sp.tail = <<>> THEN age ELSE [age EXCEPT ![p] = IF CORRECTION THEN 0 ELSE age[p]]
                            /\ since' = IF TRACK /\ sp.tail # <<>> THEN [since EXCEPT ![p] = 0] ELSE since
                            /\ last' = [kind |-> "steal", from |-> v, to |-> p, moved |-> TotalL(sp.tail), before |-> a1[v],
                                        head |-> sp.head, tail |-> sp.tail, m |-> m, keep |-> keep, thief |-> a1[p],
                                        victimIdle |-> age[v] >= 2, victimSince |-> since[v], eta |-> EtaP(a1, v), qq |-> q]
                    ELSE /\ a' = a1 /\ q' = tcr.q /\ UNCHANGED <<age, since>> /\ last' = [kind |-> "nosteal"]
               ELSE /\ q' = tcr.q
                    /\ a' = IF tcr.out = <<>> THEN [a EXCEPT ![p] = ap] ELSE [a EXCEPT ![p] = ExtendC(AN, ap, tcr.out)]
                    /\ age' = IF tcr.out # <<>> /\ out = 0 /\ CORRECTION THEN [age EXCEPT ![p] = 0] ELSE age
                    /\ since' = IF TRACK /\ tcr.out # <<>> /\ out = 0 THEN [since EXCEPT ![p] = 0] ELSE since
                    /\ last' = [kind |-> "topup", p |-> p, took |-> tcr.out, qbefore |-> q]
       /\ UNCHANGED <<V, act, known, st, fail, W, striped>>

(* ---- a provider verifies a group of its list ---- *)
Verify(p, g) ==
    /\ st = "running" /\ p \in act /\ p \notin SILENT /\ p \notin LIARS
    /\ g \in GCov(a[p]) /\ g \notin V /\ g \in W
    /\ V' = V \cup {g}
    /\ known' = [known EXCEPT ![p] = TRUE]
    /\ age' = [age EXCEPT ![p] = 0]
    /\ IF W \subseteq V \cup {g} THEN st' = "done" ELSE st' = st
    /\ last' = [kind |-> "verify", p |-> p, g |-> g]
    /\ UNCHANGED <<q, a, act, since, fail, W, striped>>

(* ---- time passes for a provider that holds a share ---- *)
Tick(p) ==
    /\ st = "running" /\ p \in act /\ age[p] < 2
    /\ age' = [age EXCEPT ![p] = age[p] + 1]
    /\ since' = IF TRACK /\ since[p] < 2 THEN [since EXCEPT ![p] = since[p] + 1] ELSE since
    /\ last' = [kind |-> "tick"]
    /\ UNCHANGED <<q, a, V, act, known, st, fail, W, striped>>

(* ---- LIAR_EVICT ---- *)
Evict(p) ==
    LET miss == RetainV(AN, V, a[p])
        rest == act \ {p}
    IN /\ st = "running" /\ p \in act /\ p \in LIARS
       /\ act' = rest
       /\ a' = [a EXCEPT ![p] = <<>>]
       /\ known' = [known EXCEPT ![p] = FALSE]
       /\ age' = [age EXCEPT ![p] = 0]
       /\ since' = IF TRACK THEN [since EXCEPT ![p] = 2] ELSE since
       /\ IF rest = {}
          THEN st' = "done" /\ fail' = "liar" /\ q' = q
          ELSE st' = "running" /\ fail' = "none" /\ q' = RetQ(q, miss)
       /\ last' = [kind |-> "evict", p |-> p, share |-> a[p], miss |-> miss]
       /\ UNCHANGED <<V, W, striped>>

DoneStutter == st = "done" /\ UNCHANGED vars

Next ==
    \/ \E w \in WANTS, v0 \in INITV, np \in NPROVS : Start(w, v0, np)
    \/ \E p \in Provs, t \in TGTS : TopUp(p, t)
    \/ \E p \in Provs, g \in Groups : Verify(p, g)
    \/ \E p \in Provs : Tick(p) \/ Evict(p)
    \/ DoneStutter

Spec == Init /\ [][Next]_vars

(* ---- invariants ---- *)
Held == GCov(q) \cup (UNION {GCov(a[p]) : p \in Provs})
RECURSIVE SumH(_, _)
SumH(S, g) == IF S = {} THEN 0 ELSE LET p == CHOOSE p \in S : TRUE IN GMult(a[p], g) + SumH(S \ {p}, g)
Holders(g) == GMult(q, g) + SumH(Provs, g)

TypeOK ==
    /\ st \in {"idle", "running", "done"} /\ fail \in {"none", "liar", "noprov"}
    /\ act \subseteq Provs /\ V \subseteq Groups /\ W \subseteq Groups

(* lists within capacity; spans aligned to groups (an end is a group boundary or the end of the value) and non-empty *)
Sized ==
    /\ Len(q) <= QN /\ \A p \in Provs : Len(a[p]) <= AN
    /\ \A k \in 1 .. Len(q) : q[k].len > 0 /\ q[k].off % G = 0 /\ (End(q[k]) % G = 0 \/ End(q[k]) = L)
    /\ \A p \in Provs : \A k \in 1 .. Len(a[p]) :
         a[p][k].len > 0 /\ a[p][k].off % G = 0 /\ (End(a[p][k]) % G = 0 \/ End(a[p][k]) = L)

(* property 2: every wanted group the store has not verified is queued or held by a provider that holds a share *)
Cover ==
    st = "running" =>
        \A g \in W \ V : g \in GCov(q) \/ \E p \in act : g \in GCov(a[p])

(* conservation: the bytes of the wanted groups are partitioned among queue, lists and the verified set *)
Exact ==
    (st = "running" /\ striped) =>
        \A g \in Groups : /\ (g \notin W => Holders(g) = 0)
                          /\ (g \in W => Holders(g) <= 1 /\ (g \notin V => Holders(g) = 1))

(* non-striped (one provider): its list is the whole missing set and nobody else holds work *)
SingleExact ==
    (st = "running" /\ ~striped) =>
        /\ q = <<>> /\ \A p \in Provs \ {1} : a[p] = <<>>
        /\ \A g \in W \ V : g \in GCov(a[1])

(* resume: the queue after the start asks for no verified byte *)
ResumeFresh == (last.kind = "start" /\ st = "running" /\ striped) => GCov(q) \cap V = {}

(* an evicted provider holds nothing and never again; the others' state is untouched *)
Evicted == \A p \in Provs : p \notin act => (a[p] = <<>> /\ ~known[p])

(* no group is held twice: false in the tight configuration, where a full list widens a span over a gap (asks twice,
   never skips: Cover still holds there) *)
NoDup == \A g \in Groups : Holders(g) <= 1

(* no list is ever full when a push can come: the bound under which Exact needs no widening *)
Room == Len(q) < QN /\ \A p \in Provs : Len(a[p]) < AN

StealOk ==
    last.kind = "steal" =>
        /\ last.from # last.to
        /\ last.thief = <<>>
        /\ last.qq = <<>>
        /\ last.moved = last.m - Min(last.keep, last.m)
        /\ GCov(last.head) \cup GCov(last.tail) = GCov(last.before)
        /\ (last.victimIdle \/ last.eta >= ETAMS)

(* the first idle correction: a provider just handed work is not robbed as idle (violated when the clock is stale) *)
NoStealOfJustGiven == last.kind = "steal" => (last.eta >= STALLED => last.victimSince >= 2)

(* the second idle correction at work: a stalled provider holding less than STEAL_MIN is a candidate *)
NoSmallIdleSteal == ~(last.kind = "steal" /\ last.eta >= STALLED /\ last.m < STEALMIN)

DoneOk ==
    st = "done" =>
        /\ (fail = "none" => (W \subseteq V \/ W = {}))
        /\ (fail = "liar" => act = {})

(* the measure of Term.lean: unverified wanted groups, active providers, queue size; lexicographic, never rising *)
Phi == <<Cardinality(W \ V), Cardinality(act), TotalL(q) + Len(q)>>
LexLe(x, y) == \/ x[1] < y[1]
               \/ (x[1] = y[1] /\ x[2] < y[2])
               \/ (x[1] = y[1] /\ x[2] = y[2] /\ x[3] <= y[3])
PhiLe == [][st = "running" => LexLe(Phi', Phi)]_vars

(* the work is conserved by the step: the groups held before are held after, unless verified or evicted-and-returned *)
Monotone == [][st = "running" /\ st' = "running" =>
                  \A g \in W \ V' : (g \in Held) => g \in (GCov(q') \cup UNION {GCov(a'[p]) : p \in Provs})]_vars

Inv == TypeOK /\ Sized /\ Cover /\ SingleExact /\ Evicted /\ StealOk /\ DoneOk

(* ---- liveness: with time passing and every enabled honest step taken, the fetch ends; it completes if at least one
   honest provider holds a share (a silent one is robbed once idle, a liar is evicted) ---- *)
Fair ==
    /\ WF_vars(\E p \in Provs, t \in TGTS : TopUp(p, t))
    /\ WF_vars(\E p \in Provs, g \in Groups : Verify(p, g))
    /\ WF_vars(\E p \in Provs : Tick(p))
    /\ WF_vars(\E p \in Provs : Evict(p))
    /\ WF_vars(\E w \in WANTS, v0 \in INITV, np \in NPROVS : Start(w, v0, np))
FairSpec == Spec /\ Fair

Ends == <>(st = "done")
Completes == <>(st = "done" /\ fail = "none")
=================================================================================
