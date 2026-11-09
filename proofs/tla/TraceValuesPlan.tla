--------------------------- MODULE TraceValuesPlan ---------------------------
(***************************************************************************)
(* Trace validation of the response geometry, ValueSource::read_at and the *)
(* server's range-proof frames of vinc-values (plan.rs, source.rs,         *)
(* server.rs).                                                             *)
(*                                                                         *)
(* The Rust test tests/trace_values_plan.rs runs the real Plan,            *)
(* ValueSource::read_at (over a store that logs its reads), proof_k and    *)
(* Server on seeded random values, spans, offsets and events, and records  *)
(* one line per call (values_plan_small.ndjson: the runs whose numbers fit *)
(* TLC's 32-bit integers; Lean replays all of values_plan.ndjson,          *)
(* proofs/lean/Vinc/TraceValuesPlan.lean). Every line must be what the     *)
(* operators of ValuesPlanOps.tla and ValuesPlanProofs.tla compute, at the *)
(* constants of the code (G = 16384, 16-byte headers, 64-byte pairs, the   *)
(* 2^62 - 1 response limit scaled to the integers TLC has, which the small *)
(* runs never reach):                                                      *)
(*                                                                         *)
(*  - vplan: the refusal or the total, the ranges, and the recorded frames,*)
(*    locates, frame_of_group and proof_pair answers;                       *)
(*  - vread: the store reads read_at made (outboard or value, offset,      *)
(*    length asked, length returned) and the length it returned, replayed  *)
(*    chunk by chunk from the plan;                                         *)
(*  - vk: proof_k;                                                         *)
(*  - vsrvnew / vsrv: the server's state machine on the events fed to it,  *)
(*    and the proof frames it sent (start, length, proof bytes, body);     *)
(*  - vslotnew / vslot: the request slots of the server (ValuesPlanServer): *)
(*    a stream opened (the first free slot, or a BUSY reset), a request    *)
(*    answered (UNAVAILABLE and only its slot freed when the value or the  *)
(*    plan is refused or the install fails; otherwise it serves the rounded *)
(*    ranges of its plan, and exactly the other streams of the peer        *)
(*    serving the root over an overlapping range are freed and reset       *)
(*    SUPERSEDED, in slot order), a stream finished or reset, a closed     *)
(*    session; the table before is the table after the last event.         *)
(*                                                                         *)
(* Needs the TLA+ CommunityModules (Json, IOUtils) and the environment     *)
(* variable VINC_TRACE_DIR, the directory that holds                       *)
(* values_plan_small.ndjson.                                               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC, Json, IOUtils

VARIABLES i, srv, tab
vars == <<i, srv, tab>>

MaxU == 1073741824
Ops == INSTANCE ValuesPlanOps WITH G <- 16384, HDR <- 16, PAR <- 64, MaxU <- MaxU, MaxS <- 268435455, MaxR <- 32
PR == INSTANCE ValuesPlanProofs WITH G <- 16384, PMax <- 1100, MaxK <- 16, MinK <- 4, MaxF <- 48, Lead <- 524288,
                                     MaxU <- MaxU, BodyHead <- 22,
                                     ln <- 0, st <- 0, vfront <- 0, window <- 0, armed <- 0, ok <- 0, fired <- 0

Trace == ndJsonDeserialize(IOEnv.VINC_TRACE_DIR \o "/values_plan_small.ndjson")
Ev == Trace[i]

IsNone(f) == "none" \in DOMAIN f
ErrOf(code) == IF code = 1 THEN "oob" ELSE IF code = 2 THEN "many" ELSE "long"

EmptySrv == [ln |-> 0, rs |-> <<>>, total |-> 0, st |-> [deep |-> FALSE, pfTo |-> 0],
             vfront |-> 0, window |-> 0, armed |-> FALSE]
Init == i = 1 /\ srv = EmptySrv /\ tab = <<>>

(* ---- vplan ---- *)
FrameRowOK(len, rs, r) ==
    LET f == Ops!Frame(len, rs, r[1] + 1, r[2])
    IN /\ ~IsNone(f)
       /\ f.start = r[3] /\ f.off = r[4] /\ f.dlen = r[5] /\ f.plen = r[6] /\ (f.follows <=> r[7] = 1)

PlanEv ==
    LET pn == Ops!PlanNew(Ev.len, Ev.spans)
    IN IF "err" \in DOMAIN Ev
       THEN "err" \in DOMAIN pn /\ pn.err = ErrOf(Ev.err)
       ELSE /\ ~("err" \in DOMAIN pn)
            /\ pn.total = Ev.total
            /\ [j \in 1 .. Len(pn.rs) |-> <<pn.rs[j].first, pn.rs[j].last, pn.rs[j].start>>] = Ev.ranges
            /\ \A j \in 1 .. Len(Ev.frames) : FrameRowOK(Ev.len, pn.rs, Ev.frames[j])
            /\ \A j \in 1 .. Len(Ev.loc) :
                 LET f == Ops!Locate(Ev.len, pn.rs, pn.total, Ev.loc[j][1])
                 IN ~IsNone(f) /\ f.range = Ev.loc[j][2] + 1 /\ f.k = Ev.loc[j][3]
            /\ \A j \in 1 .. Len(Ev.nloc) : IsNone(Ops!Locate(Ev.len, pn.rs, pn.total, Ev.nloc[j]))
            /\ \A j \in 1 .. Len(Ev.fog) :
                 LET f == Ops!FrameOfGroup(Ev.len, pn.rs, Ev.fog[j][1])
                 IN ~IsNone(f) /\ f.range = Ev.fog[j][2] + 1 /\ f.k = Ev.fog[j][3]
            /\ \A j \in 1 .. Len(Ev.nfog) : IsNone(Ops!FrameOfGroup(Ev.len, pn.rs, Ev.nfog[j]))
            /\ \A j \in 1 .. Len(Ev.pp) :
                 LET r == Ev.pp[j]
                     f == Ops!Frame(Ev.len, pn.rs, r[1] + 1, r[2])
                 IN ~IsNone(f) /\ Ops!ProofPair(Ev.len, pn.rs, f, r[3]) = [off |-> r[4]]
            /\ \A j \in 1 .. Len(Ev.npp) :
                 LET r == Ev.npp[j]
                     f == Ops!Frame(Ev.len, pn.rs, r[1] + 1, r[2])
                 IN ~IsNone(f) /\ IsNone(Ops!ProofPair(Ev.len, pn.rs, f, r[3]))

(* ---- vread: the chunks read_at takes ---- *)
RECURSIVE Chunks(_, _, _, _, _, _, _)
Chunks(len, rs, total, at, rem, acc, done) ==
    IF rem = 0 THEN [done |-> done, rest |-> acc, ok |-> TRUE]
    ELSE LET f == Ops!Locate(len, rs, total, at)
         IN IF IsNone(f) THEN [done |-> done, rest |-> acc, ok |-> TRUE]
            ELSE IF at < f.start + 16
            THEN LET chunk == Ops!Min(16 - (at - f.start), rem)
                 IN Chunks(len, rs, total, at + chunk, rem - chunk, acc, done + chunk)
            ELSE IF at < f.start + 16 + f.plen
            THEN LET into == at - (f.start + 16)
                     room == Ops!Min(64 - (into % 64), rem)
                     pp == Ops!ProofPair(len, rs, f, into \div 64)
                 IN IF IsNone(pp) \/ acc = <<>> THEN [done |-> done, rest |-> acc, ok |-> FALSE]
                    ELSE LET a == Head(acc)
                         IN IF ~(a[1] = 0 /\ a[2] = pp.off + (into % 64) /\ a[3] = room /\ a[4] <= room)
                            THEN [done |-> done, rest |-> acc, ok |-> FALSE]
                            ELSE IF a[4] < room THEN [done |-> done + a[4], rest |-> Tail(acc), ok |-> TRUE]
                            ELSE Chunks(len, rs, total, at + a[4], rem - a[4], Tail(acc), done + a[4])
            ELSE LET into == at - (f.start + 16 + f.plen)
                     room == Ops!Min(f.dlen - into, rem)
                 IN IF acc = <<>> THEN [done |-> done, rest |-> acc, ok |-> FALSE]
                    ELSE LET a == Head(acc)
                         IN IF ~(a[1] = 1 /\ a[2] = f.off + into /\ a[3] = room /\ a[4] <= room)
                            THEN [done |-> done, rest |-> acc, ok |-> FALSE]
                            ELSE IF a[4] < room THEN [done |-> done + a[4], rest |-> Tail(acc), ok |-> TRUE]
                            ELSE Chunks(len, rs, total, at + a[4], rem - a[4], Tail(acc), done + a[4])

ReadEv ==
    LET pn == Ops!PlanNew(Ev.len, Ev.spans)
        r == Chunks(Ev.len, pn.rs, pn.total, Ev.off, Ev.n, Ev.acc, 0)
    IN /\ ~("err" \in DOMAIN pn)
       /\ r.ok /\ r.rest = <<>> /\ r.done = Ev.ret

(* ---- vk ---- *)
KEv == PR!ProofK(Ev.ln) = Ev.k

(* ---- the server ---- *)
FrontOf(s, sent) ==
    LET f == Ops!Locate(s.ln, s.rs, s.total, Ops!Max(sent - 1, 0))
    IN IF IsNone(f) THEN 0 ELSE f.off + Ops!Min(Ops!Max(sent - (f.start + 16 + f.plen), 0), f.dlen)

FramesRow(ln, fr) ==
    [j \in 1 .. Len(fr) |->
        LET pairs == Ops!RangePairs(Ops!Groups(ln), fr[j].at \div 16384, (fr[j].at + fr[j].wn + 16383) \div 16384)
        IN <<fr[j].at, fr[j].wn, pairs * 64, 22 + pairs * 64>>]

SrvNewEv ==
    LET pn == Ops!PlanNew(Ev.ln, Ev.spans)
    IN /\ ~("err" \in DOMAIN pn)
       /\ srv' = [EmptySrv EXCEPT !.ln = Ev.ln, !.rs = pn.rs, !.total = pn.total]

SrvEv ==
    LET s == srv
    IN \/ /\ Ev.ev = "loss"
          /\ LET vf == Ops!Max(s.vfront, FrontOf(s, Ev.b))
                 lf == Ops!Locate(s.ln, s.rs, s.total, Ev.a)
                 from == IF IsNone(lf) THEN 0 ELSE lf.off
                 res == PR!ProofsCall(s.ln, s.st, vf, Ev.w, from, 0, 99)
             IN /\ FramesRow(s.ln, res.fr) = Ev.fr
                /\ srv' = [s EXCEPT !.st = res.st, !.vfront = vf, !.window = Ev.w, !.armed = TRUE]
       \/ /\ Ev.ev = "sent"
          /\ LET vf == Ops!Max(s.vfront, FrontOf(s, Ev.a))
                 go == s.armed /\ ~s.st.deep /\ Ops!Min(vf + (Ev.w \div 2), MaxU) > s.st.pfTo
                 upto == Ops!Min(vf + Ops!Min(Ev.w, 524288), MaxU)
                 res == PR!ProofsCall(s.ln, s.st, vf, Ev.w, IF vf = 0 THEN 0 ELSE vf - 1, upto, 99)
             IN IF go
                THEN /\ FramesRow(s.ln, res.fr) = Ev.fr
                     /\ srv' = [s EXCEPT !.st = res.st, !.vfront = vf, !.window = Ev.w]
                ELSE /\ Ev.fr = <<>>
                     /\ srv' = [s EXCEPT !.vfront = vf, !.window = Ev.w]
       \/ /\ Ev.ev = "ext"
          /\ LET res == PR!ProofsCall(s.ln, s.st, s.vfront, s.window, Ev.a, Ev.b, 99)
             IN /\ FramesRow(s.ln, res.fr) = Ev.fr
                /\ srv' = [s EXCEPT !.st = res.st, !.armed = TRUE]


(* ---- the request slots of the server ---- *)
\* a slot is <<>> (free), <<stream, peer>> (collecting) or <<stream, peer, root, ranges>> (serving)
BUSY == 6
UNAVAIL == 2
SUPERSEDED == 4
GB == 16384

Used(t) == {j \in 1 .. Len(t) : t[j] # <<>>}
StreamAt(t, st) == {j \in Used(t) : t[j][1] = st}

OverlapsB(rg, spans) ==
    \E r \in {rg[a] : a \in 1 .. Len(rg)}, sp \in {spans[b] : b \in 1 .. Len(spans)} :
        sp[2] > 0 /\ sp[1] < r[1] + r[2] /\ r[1] < sp[1] + sp[2]

\* the rounded ranges of a plan, clamped to the value (Plan::range_span)
MineOf(len, rs) == [j \in 1 .. Len(rs) |-> <<rs[j].first * GB, Ops!Min(rs[j].last * GB, len) - rs[j].first * GB>>]

RECURSIVE Supers(_, _, _)
Supers(t, sup, j) == IF j > Len(t) THEN <<>>
                     ELSE IF j \in sup THEN <<<<t[j][1], SUPERSEDED>>>> \o Supers(t, sup, j + 1)
                     ELSE Supers(t, sup, j + 1)

OpenEv ==
    /\ Ev.ev = "open" /\ Ev.before = tab /\ StreamAt(tab, Ev.stream) = {}
    /\ LET free == {j \in 1 .. Len(tab) : tab[j] = <<>>}
       IN IF free = {}
          THEN Ev.after = tab /\ Ev.rc = <<<<Ev.stream, BUSY>>>>
          ELSE LET j == CHOOSE j \in free : \A k \in free : j <= k
               IN Ev.after = [tab EXCEPT ![j] = <<Ev.stream, Ev.peer>>] /\ Ev.rc = <<>>

ReqEv ==
    /\ Ev.ev = "req" /\ Ev.before = tab
    /\ \E si \in StreamAt(tab, Ev.stream) :
         /\ Len(tab[si]) = 2
         /\ LET me == tab[si]
                pn == IF Ev.len = 0 THEN [err |-> "unknown"] ELSE Ops!PlanNew(Ev.len, Ev.spans)
            IN IF "err" \in DOMAIN pn \/ Ev.inst = 0
               THEN Ev.after = [tab EXCEPT ![si] = <<>>] /\ Ev.rc = <<<<Ev.stream, UNAVAIL>>>>
               ELSE LET sup == {j \in Used(tab) : j # si /\ tab[j][1] # Ev.stream /\ tab[j][2] = me[2]
                                 /\ Len(tab[j]) = 4 /\ tab[j][3] = Ev.root /\ OverlapsB(tab[j][4], Ev.spans)}
                    IN /\ Ev.after = [j \in 1 .. Len(tab) |->
                                         IF j = si THEN <<me[1], me[2], Ev.root, MineOf(Ev.len, pn.rs)>>
                                         ELSE IF j \in sup THEN <<>> ELSE tab[j]]
                       /\ Ev.rc = Supers(tab, sup, 1)

DoneEv ==
    /\ Ev.ev \in {"done", "reset"} /\ Ev.before = tab /\ Ev.rc = <<>>
    /\ LET at == StreamAt(tab, Ev.stream)
       IN IF at = {} THEN Ev.after = tab
          ELSE LET j == CHOOSE j \in at : \A k \in at : j <= k
               IN Ev.after = [tab EXCEPT ![j] = <<>>]

ClosedEv ==
    /\ Ev.ev = "closed" /\ Ev.before = tab /\ Ev.rc = <<>>
    /\ Ev.after = [j \in 1 .. Len(tab) |-> IF tab[j] # <<>> /\ tab[j][2] = Ev.peer THEN <<>> ELSE tab[j]]

SlotEv == OpenEv \/ ReqEv \/ DoneEv \/ ClosedEv

Step ==
    /\ i <= Len(Trace)
    /\ \/ Ev.t = "vplan" /\ PlanEv /\ UNCHANGED <<srv, tab>>
       \/ Ev.t = "vread" /\ ReadEv /\ UNCHANGED <<srv, tab>>
       \/ Ev.t = "vk" /\ KEv /\ UNCHANGED <<srv, tab>>
       \/ Ev.t = "vsrvnew" /\ SrvNewEv /\ UNCHANGED tab
       \/ Ev.t = "vsrv" /\ SrvEv /\ UNCHANGED tab
       \/ Ev.t = "vslotnew" /\ tab' = [j \in 1 .. Ev.s |-> <<>>] /\ UNCHANGED srv
       \/ Ev.t = "vslot" /\ SlotEv /\ tab' = Ev.after /\ UNCHANGED srv
    /\ i' = i + 1

\* the trace has ended: every event was a step of the model
Finished == i > Len(Trace) /\ UNCHANGED vars

TNext == Step \/ Finished

TraceSpec == Init /\ [][TNext]_vars
=============================================================================
