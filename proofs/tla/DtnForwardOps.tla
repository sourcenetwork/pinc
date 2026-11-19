---------------------------- MODULE DtnForwardOps ----------------------------
(***************************************************************************)
(* The operations of pinc-dtn forward.rs (Forwarder::step and poll), one   *)
(* node, step for step.                                                    *)
(*                                                                         *)
(* The four tables are fixed arrays of slots, as in the code: a slot is a *)
(* record with a full flag (None is full = FALSE), searches run in slot     *)
(* order, and a new entry goes to the first free slot. Node ids, bundle    *)
(* ids and times are integers (equal integer, equal bytes). Machine        *)
(* integers are exact: time and timers are u64 with saturating subtraction *)
(* (naturals with monus; the model bound on time is MaxTime of the         *)
(* checking spec, far below 2^64, and Lean proves the u64 statements),     *)
(* the send counter is a u8 with a saturating add (SatU8), copies are a    *)
(* u16 halved by integer division.                                         *)
(*                                                                         *)
(* A state is f = [now, bs, ls, ts, ds]: the physical time, the bundle     *)
(* slots (id, dest, exp, copies, delivered), the link slots (peer, up),   *)
(* the transfer slots (bundle, peer, given, deliver, ph, rem, sends) with  *)
(* ph in {"sent", "acked", "gaveup"} and the D slots of the memory table   *)
(* (id, exp) of the accepted bundles. An accepted bundle is remembered     *)
(* until its own expiry, whether still held or released (delivered,        *)
(* expired or forgotten): a hold of a remembered, unexpired bundle that is *)
(* not held is refused with err "Finished", so a late duplicate of a hold  *)
(* never re-creates copies the budget already counted. A new hold takes   *)
(* the first memory slot that is free or whose entry has expired (exp <=  *)
(* now), and is refused with "Full" when there is none. Release and Forget *)
(* do not touch the memory. The code also counts the ignored holds in a   *)
(* metric that nothing reads; it is not modelled.                         *)
(*                                                                         *)
(* Step(f, now, inp) is Forwarder::step: it first charges the elapsed time *)
(* to the timers whose link is up (Advance) and then applies the input;    *)
(* an error leaves the advanced state. Poll(f) is Forwarder::poll: one     *)
(* action or none, and it may change the state without an action (a       *)
(* transfer giving up). The caller polls until none.                       *)
(*                                                                         *)
(* The checking specs are DtnForward.tla (one node, with ghost counters), *)
(* DtnForwardNet.tla (several nodes and a lossy network) and the scenario  *)
(* models, which instantiate this module. The trace check              *)
(* (TraceDtnForward.tla) compares the real code with the same operators.   *)
(* Lean counterpart: proofs/lean/Pinc/DtnForward.lean.                     *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS B, L, T, D, Retry, MaxSends

Mon(a, b) == IF a > b THEN a - b ELSE 0               \* u64 saturating_sub
Max2(a, b) == IF a > b THEN a ELSE b
SatU8(x) == IF x > 255 THEN 255 ELSE x                 \* u8 saturating_add
MinOf(S) == CHOOSE i \in S : \A j \in S : i <= j

EmptyB == [full |-> FALSE, id |-> 0, dest |-> 0, exp |-> 0, copies |-> 0, delivered |-> FALSE]
EmptyL == [full |-> FALSE, peer |-> 0, up |-> FALSE]
EmptyD == [full |-> FALSE, id |-> 0, exp |-> 0]
EmptyT == [full |-> FALSE, bundle |-> 0, peer |-> 0, given |-> 0, deliver |-> FALSE, ph |-> "sent", rem |-> 0, sends |-> 0]

New(now) == [now |-> now, bs |-> [i \in 1..B |-> EmptyB], ls |-> [i \in 1..L |-> EmptyL], ts |-> [i \in 1..T |-> EmptyT], ds |-> [i \in 1..D |-> EmptyD]]

Up(f, p) == \E i \in 1..L : f.ls[i].full /\ f.ls[i].up /\ f.ls[i].peer = p
BIdx(f, id) == {i \in 1..B : f.bs[i].full /\ f.bs[i].id = id}
HasB(f, id) == BIdx(f, id) # {}
FreeB(f) == {i \in 1..B : ~f.bs[i].full}
FreeL(f) == {i \in 1..L : ~f.ls[i].full}
FreeT(f) == {i \in 1..T : ~f.ts[i].full}
\* the memory slots that can take a new entry: free, or expired (exp <= now)
FreeD(f) == {i \in 1..D : ~f.ds[i].full \/ f.ds[i].exp <= f.now}
\* a remembered bundle whose memory has not ended
SeenLive(f, id) == \E i \in 1..D : f.ds[i].full /\ f.ds[i].id = id /\ f.ds[i].exp > f.now
TIdx(f, id, p) == {i \in 1..T : f.ts[i].full /\ f.ts[i].bundle = id /\ f.ts[i].peer = p}

(* Forwarder::advance *)
Advance(f, now) ==
    LET dt == Mon(now, f.now) IN
    [f EXCEPT !.now = Max2(f.now, now),
              !.ts = [i \in 1..T |->
                  IF f.ts[i].full /\ f.ts[i].ph = "sent" /\ Up(f, f.ts[i].peer)
                  THEN [f.ts[i] EXCEPT !.rem = Mon(f.ts[i].rem, dt)] ELSE f.ts[i]]]

(* Forwarder::drop_bundle: the bundle slot and every transfer of the bundle *)
DropB(f, id) ==
    [f EXCEPT !.bs = [i \in 1..B |-> IF f.bs[i].full /\ f.bs[i].id = id THEN EmptyB ELSE f.bs[i]],
              !.ts = [i \in 1..T |-> IF f.ts[i].full /\ f.ts[i].bundle = id THEN EmptyT ELSE f.ts[i]]]

(* Inputs: [k |-> "tick"] [k |-> "hold", id, dest, exp, copies] [k |-> "up", peer] [k |-> "down", peer] *)
(*         [k |-> "ack", peer, id] [k |-> "forget", id]                                                  *)
(* The result is [f |-> the new state, err |-> "ok" or the ForwardError variant].                        *)
Step(f0, now, inp) ==
    LET f == Advance(f0, now)
        hold == IF inp.copies = 0 THEN [f |-> f, err |-> "NoCopies"]
                ELSE IF HasB(f, inp.id) THEN [f |-> f, err |-> "Duplicate"]
                ELSE IF SeenLive(f, inp.id) THEN [f |-> f, err |-> "Finished"]
                ELSE IF FreeD(f) = {} THEN [f |-> f, err |-> "Full"]
                ELSE IF FreeB(f) = {} THEN [f |-> f, err |-> "Full"]
                ELSE [f |-> [f EXCEPT !.bs[MinOf(FreeB(f))] =
                        [full |-> TRUE, id |-> inp.id, dest |-> inp.dest, exp |-> inp.exp, copies |-> inp.copies,
                         delivered |-> FALSE],
                        !.ds[MinOf(FreeD(f))] = [full |-> TRUE, id |-> inp.id, exp |-> inp.exp]], err |-> "ok"]
        li == {i \in 1..L : f.ls[i].full /\ f.ls[i].peer = inp.peer}
        link == IF li # {}
                THEN [f |-> [f EXCEPT !.ls[MinOf(li)].up = (inp.k = "up")], err |-> "ok"]
                ELSE IF FreeL(f) = {} THEN [f |-> f, err |-> "Full"]
                ELSE [f |-> [f EXCEPT !.ls[MinOf(FreeL(f))] =
                        [full |-> TRUE, peer |-> inp.peer, up |-> (inp.k = "up")]], err |-> "ok"]
        ti == TIdx(f, inp.id, inp.peer)
        t == f.ts[MinOf(ti)]
        f2 == [f EXCEPT !.ts[MinOf(ti)].ph = "acked"]
        ack == IF ti = {} THEN [f |-> f, err |-> "Unknown"]
               ELSE IF t.deliver /\ HasB(f, inp.id)
                    THEN [f |-> [f2 EXCEPT !.bs[MinOf(BIdx(f, inp.id))].delivered = TRUE], err |-> "ok"]
                    ELSE [f |-> f2, err |-> "ok"]
    IN CASE inp.k = "tick" -> [f |-> f, err |-> "ok"]
         [] inp.k = "hold" -> hold
         [] inp.k \in {"up", "down"} -> link
         [] inp.k = "ack" -> ack
         [] inp.k = "forget" -> IF HasB(f, inp.id) THEN [f |-> DropB(f, inp.id), err |-> "ok"]
                                ELSE [f |-> f, err |-> "Unknown"]

NoAct == [k |-> "none", peer |-> 0, bundle |-> 0, copies |-> 0, retr |-> FALSE, slot |-> 0]

(* poll step 1: a delivered or expired bundle is released first *)
DoneSet(f) == {i \in 1..B : f.bs[i].full /\ (f.bs[i].delivered \/ f.bs[i].exp <= f.now)}

(* poll_retransmit: the transfers whose timer ran out on a link that is up *)
Elig(f) == {i \in 1..T : f.ts[i].full /\ f.ts[i].ph = "sent" /\ f.ts[i].rem = 0 /\ Up(f, f.ts[i].peer)}
RetrSet(f) == {i \in Elig(f) : f.ts[i].sends < MaxSends}
\* the transfers that give up during the scan: those met before the one that sends, or all if none sends
GaveSet(f) == IF RetrSet(f) = {} THEN Elig(f) ELSE {i \in Elig(f) : i < MinOf(RetrSet(f))}
GiveUp(f) == [f EXCEPT !.ts = [i \in 1..T |->
                 IF i \in GaveSet(f) THEN [f.ts[i] EXCEPT !.ph = "gaveup"] ELSE f.ts[i]]]

(* poll_spray: the candidate pairs (link slot, bundle slot) as the key (li - 1) * B + bi, the order of the loops *)
LiOf(k) == ((k - 1) \div B) + 1
BiOf(k) == ((k - 1) % B) + 1
Cand(f) == {k \in 1..(L * B) :
    /\ f.ls[LiOf(k)].full /\ f.ls[LiOf(k)].up /\ f.bs[BiOf(k)].full
    /\ TIdx(f, f.bs[BiOf(k)].id, f.ls[LiOf(k)].peer) = {}
    /\ (f.ls[LiOf(k)].peer = f.bs[BiOf(k)].dest \/ f.bs[BiOf(k)].copies \div 2 > 0)}

Poll(f) ==
    IF DoneSet(f) # {} THEN
        LET i == MinOf(DoneSet(f)) IN
        [f |-> DropB(f, f.bs[i].id), act |-> [NoAct EXCEPT !.k = "release", !.bundle = f.bs[i].id]]
    ELSE IF RetrSet(f) # {} THEN
        LET i == MinOf(RetrSet(f))
            g == GiveUp(f)
            t == f.ts[i] IN
        [f |-> [g EXCEPT !.ts[i].rem = Retry, !.ts[i].sends = SatU8(t.sends + 1)],
         act |-> [k |-> "send", peer |-> t.peer, bundle |-> t.bundle, copies |-> t.given, retr |-> TRUE, slot |-> i]]
    ELSE
        LET g == GiveUp(f) IN
        IF Cand(g) = {} \/ FreeT(g) = {} THEN [f |-> g, act |-> NoAct]
        ELSE
            LET k == MinOf(Cand(g))
                li == LiOf(k)
                bi == BiOf(k)
                bu == g.bs[bi]
                peer == g.ls[li].peer
                deliver == (peer = bu.dest)
                given == IF deliver THEN 0 ELSE bu.copies \div 2
                s == MinOf(FreeT(g)) IN
            [f |-> [g EXCEPT !.ts[s] = [full |-> TRUE, bundle |-> bu.id, peer |-> peer, given |-> given,
                                        deliver |-> deliver, ph |-> "sent", rem |-> Retry, sends |-> 1],
                             !.bs[bi].copies = bu.copies - given],
             act |-> [k |-> "send", peer |-> peer, bundle |-> bu.id, copies |-> given, retr |-> FALSE, slot |-> s]]

CopiesHeld(f, id) == IF HasB(f, id) THEN f.bs[MinOf(BIdx(f, id))].copies ELSE 0

RECURSIVE SumGiven(_, _)
SumGiven(f, X) == IF X = {} THEN 0 ELSE LET i == MinOf(X) IN f.ts[i].given + SumGiven(f, X \ {i})
\* copies_handed: the copies handed to peers for the bundle, acknowledged or not
Handed(f, id) == SumGiven(f, {i \in 1..T : f.ts[i].full /\ f.ts[i].bundle = id})
=============================================================================
