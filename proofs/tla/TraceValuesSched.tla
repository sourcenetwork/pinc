---------------------------- MODULE TraceValuesSched ----------------------------
(***************************************************************************)
(* Trace validation of the work scheduler of the value fetch: vinc-values   *)
(* fetch/sched.rs (begin, top_up with TAIL_SHRINK and take_chunk, steal     *)
(* with the two idle corrections, evict) and the start/finish paths of      *)
(* fetch/mod.rs and fetch/recv.rs.                                          *)
(*                                                                         *)
(* The Rust test tests/trace_values_sched.rs runs the real Fetch over the   *)
(* in-memory multi-provider harness (several providers of different        *)
(* speeds, ranges and resume, liars, a silent provider, a dropped one, more *)
(* providers than the fetch uses, no provider, a wrong root, nothing        *)
(* missing) and records the transitions of the fetch's Trace log. Every     *)
(* recorded event must be a step of the model below:                        *)
(*  - run: the wanted groups are the ranges asked rounded out to whole      *)
(*    groups (align), the verified groups are those of the store;           *)
(*  - start: the bytes wanted are exactly the missing ones, once;           *)
(*  - topup: the target is Target(), the provider holds less than half of   *)
(*    it, the bytes taken are what TAIL_SHRINK and the group cut of         *)
(*    take_chunk allow (or the tail of the steal just before);              *)
(*  - steal: the victim is the candidate with the greatest eta (the idle    *)
(*    corrections included), the thief held nothing and the queue is       *)
(*    empty, the bytes moved are the list beyond `keep`;                    *)
(*  - ver: a group of the wanted set verifies once, out of the assigned     *)
(*    bytes of its provider; its clocks and counters move;                  *)
(*  - liar: the share goes back to the queue, the provider is cleared and   *)
(*    never assigned again;                                                 *)
(*  - end: complete only when every wanted group is verified, failed only   *)
(*    with no holder left (EveryProviderLied), NoProvider and BadRoot at   *)
(*    the start.                                                            *)
(* The state invariant is the conservation of the bytes: queue, assigned    *)
(* lists and verified wanted bytes add up to the wanted bytes at every      *)
(* step (the models ValuesSched / ValuesSchedList prove it on the span      *)
(* lists, the Lean file ValuesSchedCover proves no wanted byte is dropped). *)
(*                                                                         *)
(* What is not recorded: the spans of the lists (byte counts only), so the  *)
(* take_chunk check is the bound its loop guarantees (at least min(want, q) *)
(* bytes, less than a group beyond want) and not the exact spans.           *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment      *)
(* variable VINC_TRACE_DIR, the directory that holds values_sched.ndjson.   *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils, ValuesSchedOps

VARIABLES i, rs
vars == <<i, rs>>

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/values_sched.ndjson")
Ev == Trace[i]

Slots == 0..3
NONE == [none |-> TRUE]
T0 == [ms |-> 0, ns |-> 0]
TOf(e) == [ms |-> e.ms, ns |-> e.ns]

NGroups(L) == (L + G - 1) \div G
GSize(g, L) == Min((g + 1) * G, L) - g * G
(* the bytes of a set of groups of a value of length L: whole groups, the last one short *)
BytesOf(S, L) ==
    IF L = 0 THEN 0
    ELSE Cardinality(S) * G - (IF (NGroups(L) - 1) \in S THEN NGroups(L) * G - L ELSE 0)

(* the groups a request covers once rounded out (span.rs align, whole value if no ranges) *)
RangeGroups(r, L) ==
    LET a == (r[1] \div G) * G
        b == Min(CeilG(r[1] + r[2]), L)
    IN IF r[2] > 0 /\ b > a THEN a \div G .. (b - 1) \div G ELSE {}

WantedGroups(ranges, L) ==
    IF ranges = <<>> THEN (IF L = 0 THEN {} ELSE 0 .. (NGroups(L) - 1))
    ELSE UNION {RangeGroups(ranges[k], L) : k \in 1 .. Len(ranges)}

(* the groups lying wholly inside a verified interval [s, e) *)
VerifiedGroups(ivs, L) ==
    {g \in (IF L = 0 THEN {} ELSE 0 .. (NGroups(L) - 1)) :
        \E k \in 1 .. Len(ivs) : ivs[k][1] <= g * G /\ Min((g + 1) * G, L) <= ivs[k][2]}

EmptyProv == [inA |-> FALSE, a |-> 0, pb |-> 0, hasPt |-> FALSE, pt |-> T0, hasLp |-> FALSE, lp |-> T0]

Init ==
    /\ i = 1
    /\ rs = [ph |-> "new", run |-> 0, L |-> 0, W |-> {}, V |-> {}, vb |-> 0, striped |-> FALSE, q |-> 0,
             pv |-> [s \in Slots |-> EmptyProv], t0 |-> T0, pend |-> NONE, ev |-> {}, np |-> 0, ngp |-> 0,
             badroot |-> FALSE]

Quiet == rs.pend = NONE

(* ---- run: a new run starts from a fresh machine ---- *)
RunEv ==
    LET L == Ev.len
        W == WantedGroups(Ev.want, L)
        V == VerifiedGroups(Ev.ver, L)
    IN /\ Ev.op = "run" /\ rs.ph \in {"new", "ended"}
       /\ rs' = [rs EXCEPT !.ph = "init", !.run = Ev.run, !.L = L, !.W = W, !.V = V, !.vb = BytesOf(W \cap V, L),
                           !.striped = FALSE, !.q = 0, !.pv = [s \in Slots |-> EmptyProv], !.t0 = T0, !.pend = NONE,
                           !.ev = {}, !.np = Len(Ev.provs), !.ngp = 0, !.badroot = (Ev.badroot = 1)]

(* ---- start: the missing bytes are wanted once; the first four providers hold shares ---- *)
StartEv ==
    LET missing == rs.W \ rs.V
        w == BytesOf(missing, rs.L)
        n == Ev.prov
    IN /\ Ev.op = "start" /\ rs.ph = "init" /\ Ev.run = rs.run
       /\ Ev.wanted = w /\ w > 0
       /\ n = Min(rs.np, 4) /\ n >= 1
       /\ (Ev.striped = 1) <=> (n > 1)
       /\ rs' = [rs EXCEPT !.ph = "running", !.striped = (Ev.striped = 1), !.t0 = TOf(Ev), !.ngp = n,
                           !.q = IF Ev.striped = 1 THEN w ELSE 0,
                           !.pv = [s \in Slots |->
                                 [EmptyProv EXCEPT !.inA = s < n, !.a = IF Ev.striped = 0 /\ s = 0 THEN w ELSE 0]]]

(* ---- the choice of a victim and the cut of a steal ---- *)
EtaAt(r, s, now) ==
    LET p == r.pv[s]
    IN EtaOf(Idle(p.hasLp, p.lp, r.t0, now), p.a, Prate(p.hasPt, p.pt, p.pb, now))

CandAt(r, s, to, now) == s # to /\ r.pv[s].inA /\ EtaAt(r, s, now) >= ETAMS

IsBest(r, b, to, now) ==
    /\ CandAt(r, b, to, now)
    /\ \A c \in Slots : CandAt(r, c, to, now) =>
          (EtaAt(r, c, now) < EtaAt(r, b, now) \/ (EtaAt(r, c, now) = EtaAt(r, b, now) /\ c >= b))

StealEv ==
    LET from == Ev.from
        to == Ev.to
        now == TOf(Ev)
        m == rs.pv[from].a
        stalled == EtaAt(rs, from, now) >= STALLED
        rq == IF stalled THEN 0 ELSE Prate(rs.pv[from].hasPt, rs.pv[from].pt, rs.pv[from].pb, now)
        rp == Prate(rs.pv[to].hasPt, rs.pv[to].pt, rs.pv[to].pb, now)
        keep == KeepOf(m, rq, rp)
        moved == m - Min(keep, m)
    IN /\ Ev.op = "steal" /\ rs.ph = "running" /\ rs.striped /\ Ev.run = rs.run /\ Quiet
       /\ from \in Slots /\ to \in Slots /\ from # to
       /\ rs.q = 0 /\ rs.pv[to].inA /\ rs.pv[to].a = 0
       /\ IsBest(rs, from, to, now)
       /\ RateOk(rq) /\ RateOk(rp)
       /\ Ev.bytes = moved
       /\ rs' = [rs EXCEPT !.pv[from].a = m - moved, !.pend = IF moved > 0 THEN [to |-> to, bytes |-> moved] ELSE NONE]

(* ---- top_up: from the queue (TAIL_SHRINK, take_chunk) or the tail of the steal just before ---- *)
TopUpEv ==
    LET p == Ev.p
        pv == rs.pv[p]
        now == TOf(Ev)
        tgt == Target(pv.hasPt, pv.pt, pv.pb, now)
        k == Cardinality({s \in Slots : rs.pv[s].inA})
        want == TailWant(tgt - pv.a, k, rs.q)
        fromQueue == rs.pend = NONE
    IN /\ Ev.op = "topup" /\ rs.ph = "running" /\ rs.striped /\ Ev.run = rs.run
       /\ p \in Slots /\ pv.inA
       /\ Ev.tgt = tgt /\ pv.a < tgt \div 2
       /\ IF fromQueue
          THEN /\ rs.q > 0
               /\ Min(want, rs.q) <= Ev.bytes /\ Ev.bytes <= rs.q /\ Ev.bytes < want + G
               /\ rs' = [rs EXCEPT !.q = rs.q - Ev.bytes, !.pv[p].a = pv.a + Ev.bytes,
                                   !.pv[p].hasLp = TRUE, !.pv[p].lp = IF pv.a = 0 THEN now ELSE pv.lp]
                    /\ UNCHANGED rs.pend
          ELSE /\ rs.pend.to = p /\ Ev.bytes = rs.pend.bytes
               /\ rs.q = 0 /\ pv.a = 0
               /\ rs' = [rs EXCEPT !.pv[p].a = pv.a + Ev.bytes, !.pv[p].hasLp = TRUE, !.pv[p].lp = now, !.pend = NONE]

(* ---- a group verifies ---- *)
VerEv ==
    LET p == Ev.p
        g == Ev.off \div G
        now == TOf(Ev)
        pv == rs.pv[p]
    IN /\ Ev.op = "ver" /\ rs.ph = "running" /\ Ev.run = rs.run /\ Quiet
       /\ p \in Slots /\ Ev.off % G = 0 /\ g \in rs.W /\ g \notin rs.V /\ Ev.len = GSize(g, rs.L)
       /\ IF rs.striped
          THEN /\ pv.a >= Ev.len
               /\ rs' = [rs EXCEPT !.V = rs.V \cup {g}, !.vb = rs.vb + Ev.len, !.pv[p].a = pv.a - Ev.len,
                                   !.pv[p].pb = pv.pb + Ev.len, !.pv[p].hasLp = TRUE, !.pv[p].lp = now,
                                   !.pv[p].hasPt = TRUE, !.pv[p].pt = IF pv.hasPt THEN pv.pt ELSE now]
          ELSE rs' = [rs EXCEPT !.V = rs.V \cup {g}, !.vb = rs.vb + Ev.len]

(* ---- eviction: the share goes back to the queue; the provider is cleared and never assigned again ---- *)
LiarEv ==
    LET p == Ev.p
        pv == rs.pv[p]
    IN /\ Ev.op = "liar" /\ rs.ph = "running" /\ Ev.run = rs.run /\ Quiet
       /\ p \in Slots /\ pv.inA /\ p \notin rs.ev
       /\ rs' = [rs EXCEPT !.q = rs.q + pv.a, !.pv[p] = EmptyProv, !.ev = rs.ev \cup {p}]

(* ---- the end ---- *)
AllVerified == rs.W \subseteq rs.V
NoHolder == \A s \in Slots : ~rs.pv[s].inA

EndEv ==
    /\ Ev.op = "end" /\ Ev.run = rs.run /\ Quiet
    /\ \/ \* nothing was missing at the start
          /\ Ev.res = "complete" /\ rs.ph = "init" /\ AllVerified
       \/ \* no provider named, with bytes missing
          /\ Ev.res = "noprov" /\ rs.ph = "init" /\ ~AllVerified /\ rs.np = 0 /\ ~(rs.L = 0 /\ rs.badroot)
       \/ \* an empty value under a root that is not the hash of the empty value
          /\ Ev.res = "badroot" /\ rs.ph = "init" /\ rs.L = 0 /\ rs.badroot
       \/ \* every wanted group verified; nothing queued or assigned is left
          /\ Ev.res = "complete" /\ rs.ph = "running" /\ AllVerified
          /\ (rs.striped => rs.q = 0 /\ \A s \in Slots : rs.pv[s].a = 0)
       \/ \* every provider lied
          /\ Ev.res = "liar" /\ rs.ph = "running" /\ NoHolder /\ ~AllVerified
    /\ rs' = [rs EXCEPT !.ph = "ended"]

Step ==
    /\ i <= Len(Trace)
    /\ \/ RunEv \/ StartEv \/ StealEv \/ TopUpEv \/ VerEv \/ LiarEv \/ EndEv
    /\ i' = i + 1

Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars /\ WF_vars(TNext)

(* every recorded event was a step of the model, and the trace was read to its end *)
TraceAccepted == <>(i = Len(Trace) + 1)

(* the conservation of the bytes at every step of a striped run (the tail of a steal is in flight until the top-up that
   receives it), and an evicted provider holds nothing for good *)
Inv ==
    rs.ph = "running" /\ rs.striped =>
        /\ rs.q + rs.pv[0].a + rs.pv[1].a + rs.pv[2].a + rs.pv[3].a + rs.vb + (IF rs.pend = NONE THEN 0 ELSE rs.pend.bytes)
               = BytesOf(rs.W, rs.L)
        /\ \A s \in rs.ev : ~rs.pv[s].inA /\ rs.pv[s].a = 0
=================================================================================
